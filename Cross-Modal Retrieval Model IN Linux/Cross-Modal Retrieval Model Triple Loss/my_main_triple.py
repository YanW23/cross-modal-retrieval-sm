#coding=UTF-8 
import torch

from datetime import datetime
import torch.optim as optim
import torch.nn as nn
from torch.optim import lr_scheduler
import torch.nn.functional as F
import matplotlib.pyplot as plt
from my_model_triple import IDCM_NN
from my_train_model_triple import train_model, cat
from my_load_data_triple import get_loader
import math

if __name__ == '__main__':
    # print("主函数")
    # environmental setting: setting the following parameters based on your experimental environment.
    #环境设置：基于自身的实验环境设置以下参数
    # dataset = 'pascal'
    device = torch.device("cuda:0" if torch.cuda.is_available() else "cpu")
    # data parameters
    DATA_DIR = "TriplesForCross-Modal-Retrieval-Model/All_p_n_2_Triples_7_9.txt"
    PREDICT_DATA_DIR = "TriplesForCross-Modal-Retrieval-Model/s01/all_p_n_triples_for_predict.txt"
    # alpha = 1e-3
    # beta = 1e-1
    num_epochs = 100  # 训练轮数
    batch_size = 128  # 每批数据量
    lr = 2e-3  # 学习率
    betas = (0.5, 0.999)
    weight_decay = 0

    print('...Data loading is beginning...')

    #加载数据
    data_loader, input_data_par = get_loader(DATA_DIR, PREDICT_DATA_DIR, batch_size)

    # 7.6 查看数据
    # print(len(data_loader['train'].dataset))
    # for i in input_data_par.keys():
    #     print("{}:{}".format(i, input_data_par[i]))
    # print("score_test.type:{}".format(type(input_data_par['score_test'])))

    # print("输出data_loader:{}".format(data_loader['train'].batch_size))
    # # for epoch in range(2):
    # for i,data in enumerate(data_loader['train']):
    #     source,p_sm,n_sm = data
    #     print("i:{}||source.size:{}||p_sm.size:{}||n_sm.size:{}".format(i, source.size(), p_sm.size(), n_sm.size()))
    # 7.6 查看数据

    print('...Data loading is completed...')

    # model_ft = IDCM_NN(source_input_dim=input_data_par['source_dim'], sm_input_dim=input_data_par['sm_dim']).to(device)
    # params_to_update = list(model_ft.parameters())
    # print("params_to_update:{}".format(params_to_update))

    # # Observe that all parameters are being optimized 观察所有参数都在优化
    # optimizer = optim.Adam(params_to_update, lr=lr, betas=betas)
    # # 每150个epochs衰减LR通过设置gamma=0.1
    # # exp_lr_scheduler = lr_scheduler.StepLR(optimizer, step_size=150, gamma=0.1)

    # print('...Training is beginning...')
    # # Train and evaluate  训练阶段
    # calc_loss = torch.nn.TripletMarginLoss(margin=0.3, p=2, reduction='sum')
    # # calc_loss = torch.nn.MSELoss(reduction='sum')
    # model_ft, train_loss, train_acc, valid_loss, valid_acc = train_model(model_ft, data_loader, optimizer, calc_loss, num_epochs)
    # torch.save(model_ft, 'models/model1')
    # print('...Training is completed...')

    # print("------绘图------")
    # x = range(0, 100)
    # y1 = train_loss
    # y2 = train_acc
    # y3 = valid_loss
    # y4 = valid_acc
    # plt.subplot(2, 1, 1)
    # plt.plot(x, y1, color='red', label='train_loss', marker=".", linestyle="-")
    # plt.plot(x, y3, color='blue', label='valid_loss', marker=".", linestyle="-")
    # # plt.xticks(x, [i for i in x])
    # plt.title('loss vs. epoches')
    # plt.ylabel('loss')
    # plt.subplot(2, 1, 2)
    # plt.plot(x, y2, color='red', label='train_acc', marker=".", linestyle="-")
    # plt.plot(x, y4, color='blue', label='valid_acc', marker=".", linestyle="-")
    # # plt.xticks(x, [i for i in x])
    # plt.title('acc vs. epoches')
    # plt.ylabel('acc')
    # plt.show()
    # plt.savefig("images/triple_loss_acc1.jpg")

    # #测试阶段
    print('...Evaluation on testing data...')
    model_ft = torch.load('models/model1')
    model_ft.eval()
    source_embedding, p_sm_embedding, n_sm_embedding = model_ft(torch.tensor(input_data_par['source_test']).to(device), torch.tensor(input_data_par['p_sm_test']).to(device), torch.tensor(input_data_par['n_sm_test']).to(device))
    score = torch.tensor(input_data_par['score_test'])
    
    pos_dist = torch.sqrt((source_embedding - p_sm_embedding).pow(2).sum(1))
    neg_dist = torch.sqrt((source_embedding - n_sm_embedding).pow(2).sum(1))
    acc_list = cat(pos_dist, neg_dist)
    # print(acc_list)
    acc_list_tensor = torch.tensor(acc_list, dtype=torch.float32)
                        # print(acc_list_tensor)
    # outputs = nn.Sigmoid()((view_feature).detach().cpu())
    # print(acc_list_tensor)
    accuracy = torch.sum(acc_list_tensor.float()) / (pos_dist.size(0))
    print("accuracy:{}".format(accuracy))
    print("result:{}".format(acc_list))
    