from __future__ import print_function
from __future__ import division
import torch
import torch.nn as nn
import torchvision
import time
import copy
# from evaluate import fx_calc_map_label
import torch.nn.functional as F
import numpy as np
import math

print("PyTorch Version: ", torch.__version__)
print("Torchvision Version: ", torchvision.__version__)

def isequal(a, b, difference):
    if round(abs(a-b), 2) <= difference:
        return True
    else:
        return False

def cat(pos_dist, neg_dist):
    cat_list = []
    for i in range(pos_dist.size(0)):
        if pos_dist[i] < neg_dist[i]:
            cat_list.append(True)
        else:
            cat_list.append(False)
    return cat_list

def train_model(model, data_loaders, optimizer, calc_loss, num_epochs):
    since = time.time()

    best_model_wts = copy.deepcopy(model.state_dict())  # 模型最好权重
    best_acc = 0.0  # 最佳准确率

    train_loss = []
    train_acc = []
    valid_loss = []
    valid_acc = []
    for epoch in range(num_epochs):
        print('Epoch {}/{}'.format(epoch+1, num_epochs))  # 输出当前训练的epoch
        print('-' * 20)

        # 每个epoch都有一个训练和验证阶段
        for phase in ['train', 'valid']:
            if phase == 'train':
                model.train()  # 如果取的是训练数据  那么开始训练
            else:
                model.eval()  # 如果取的是验证数据  那么开始验证

            running_loss = 0.0
            running_corrects = 0
            running_val_loss = 0.0
            running_val_corrects = 0

            for sources, p_sms, n_sms in data_loaders[phase]:
                # print("训练{}||sources.size:{}||sms.size:{}||scores.size:{}".format(phase,sources.size(),sms.size(),scores.size()))
                if torch.sum(sources != sources)>1 or torch.sum(p_sms != p_sms)>1 or torch.sum(n_sms != n_sms)>1:
                    print("Data contains Nan.")
                # 零参数梯度
                optimizer.zero_grad()

                # 向前传播
                # track history if only in train
                with torch.set_grad_enabled(phase == 'train'):
                    # Get model outputs and calculate loss  获取模型输出 计算损失
                    if torch.cuda.is_available():
                        sources = sources.cuda()
                        p_sms = p_sms.cuda()
                        n_sms = n_sms.cuda()

                    # 零参数梯度
                    # optimizer.zero_grad()

                    # 前向传播
                    anchor, positive, negative = model(sources, p_sms, n_sms)  # 获得模型输出 即source和sm之间的相似度
                    # outputs = F.relu(model(sources, sms))
                    # outputs = nn.Sigmoid()(outputs)
                    loss = calc_loss(anchor, positive, negative)  # 计算模型输出与真实值的损失

                    # backward + optimize only if in training phase  后向传播 只再训练集阶段优化
                    if phase == 'train':
                        loss.backward()
                        optimizer.step()

                    with torch.no_grad():
                        # 计算每个batch_size下的accuracy
                        # 计算pos_dist和negative_dist
                        pos_dist = torch.sqrt((anchor - positive).pow(2).sum(1))
                        neg_dist = torch.sqrt((anchor - negative).pow(2).sum(1))
                        acc_list = cat(pos_dist, neg_dist)
                        # print(acc_list)
                        acc_list_tensor = torch.tensor(acc_list, dtype=torch.float32)
                        # print(acc_list_tensor)
                        accuracy = torch.sum(acc_list_tensor.float())

                # statistics
                running_loss += loss.item()  # 计算所有batch_size下的loss
                running_corrects += accuracy.item()  # 计算所有batch_size下的accuracy

            epoch_loss = running_loss / len(data_loaders[phase].dataset)
            epoch_acc = running_corrects / len(data_loaders[phase].dataset)
            # print("train中的dataset.size:{}".format(len(data_loaders['train'].dataset)))
            print('{}||  Loss: {:.4f}  Acc: {:.4f}'.format(phase, epoch_loss, epoch_acc))

            # 保存每个epoch的train_loss,train_acc和valid_loss,valid_acc
            if epoch % 1 == 0:
                if phase == 'train':
                    train_loss.append(epoch_loss)
                    train_acc.append(epoch_acc)
                if phase == 'valid':
                    valid_loss.append(epoch_loss)
                    valid_acc.append(epoch_acc)
                
            # deep copy the model  深度拷贝
            if phase == 'valid' and epoch_acc > best_acc:
                best_acc = epoch_acc
                best_model_wts = copy.deepcopy(model.state_dict())
        
        # if phase == 'train':
        #     scheduler.step()

        print()

    time_elapsed = time.time() - since
    print('Training complete in {:.0f}m {:.0f}s'.format(time_elapsed // 60, time_elapsed % 60))
    print('Best average ACC: {:4f}'.format(best_acc))

    # load best model weights
    model.load_state_dict(best_model_wts)
    return model, train_loss, train_acc, valid_loss, valid_acc