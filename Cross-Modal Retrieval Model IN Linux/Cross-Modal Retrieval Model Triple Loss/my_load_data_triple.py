from torch.utils.data.dataset import Dataset
from scipy.io import loadmat, savemat
from torch.utils.data import DataLoader
import numpy as np
import random
import math

#自定义数据集
class CustomDataSet(Dataset):
    def __init__(
            self,
            sources,
            p_sms,
            n_sms):
        self.sources = sources
        self.p_sms = p_sms
        self.n_sms = n_sms

    def __getitem__(self, index):  # 根据索引获取某一实例
        source = self.sources[index]
        p_sm = self.p_sms[index]
        n_sm = self.n_sms[index]
        return source, p_sm, n_sm

    def __len__(self):  # 获取sources数量
        count = len(self.sources)
        assert len(self.sources) == len(self.p_sms), 'sources != p_sms'
        assert len(self.sources) == len(self.p_sms), 'sources != n_sms'
        return count

def score_processing(array):
    new_array_list = []
    for i in array:
        if i >= 0.8 and i < 1.0:
            i = 0.8
        elif i >= 0.7 and i < 0.8:
            i = 0.7
        elif i >= 0.6 and i < 0.7:
            i = 0.6
        else:
            i = i
        new_array_list.append(i)
    new_array = np.asarray(new_array_list, dtype=np.float32)
    return new_array

def get_loader(path, predict_path, batch_size):

    ratio = 0.75

    # 加载train和valid数据集
    all_triples_file = open(path, 'r', encoding='utf-8')
    all_triples_list = all_triples_file.readlines()  
    random.shuffle(all_triples_list)  # 随机打乱all_triples_list
    # 现all_triples_list中包含1,5637行数据  其中每一行的格式为[[source_embedding],[sm_embedding],score]
    # 每一行数据都是str 要把str->tup->list  此时每一行数据都是一个list list.size=3  除score之外其余两个元素都是list
    triples = []
    for line in all_triples_list:
        line_tup = eval(line)
        line_tup2list = list(line_tup)
        triples.append(line_tup2list)
    
    # 截取部分数据作为train 剩余数据作为valid
    triples_train = triples[0: math.ceil((len(triples)) * ratio)]
    triples_valid = triples[math.ceil((len(triples)) * ratio):]
    # # 对[[[source],[sm],sc],[[source],[sm],sc],[[source],[sm],sc]]转置
    # # 转换成[[[source],[source],[source]],[[sm],[sm],[sm]],[sc,sc,sc]]
    triples_train_reverse = list(map(list, zip(*triples_train)))  
    triples_valid_reverse = list(map(list, zip(*triples_valid)))
    # # 现在triples列表中保存了所有的triples 并且triples中前两个元素source_embedding和sm_embedding是list score是float
    # return triples
    # 加载train和valid数据集

    # 加载test数据集
    all_predict_triples_file = open(predict_path, 'r', encoding='utf-8')
    all_predict_triples_list = all_predict_triples_file.readlines()
    predict_triples = []
    for line in all_predict_triples_list:
        line_predict_tup = eval(line)
        line_predict_tup2list = list(line_predict_tup)
        predict_triples.append(line_predict_tup2list)
    triples_test_reverse = list(map(list, zip(*predict_triples)))
    # 加载test数据集

    source_train = np.asarray(triples_train_reverse[0], dtype=np.float32)  # 加载source训练集
    p_sm_train = np.asarray(triples_train_reverse[1], dtype=np.float32)  # 加载positive sm训练集
    n_sm_train = np.asarray(triples_train_reverse[2], dtype=np.float32)  # 加载negative sm训练集
    score_train = np.asarray(triples_train_reverse[3], dtype = np.float32)  # 加载score训练集
    score_train = np.asarray([int(i*10)/10 for i in score_train], dtype = np.float32)
    # score_train = score_processing(score_train)  # 加载score训练集 

    source_valid = np.asarray(triples_valid_reverse[0], dtype = np.float32)  # 加载source验证集
    p_sm_valid = np.asarray(triples_valid_reverse[1], dtype = np.float32)  # 加载positive sm验证集
    n_sm_valid = np.asarray(triples_valid_reverse[2], dtype = np.float32)  # 加载negative sm验证集
    score_valid = np.asarray(triples_valid_reverse[3], dtype = np.float32)  # 加载score验证集
    score_valid = np.asarray([int(i*10)/10 for i in score_valid], dtype = np.float32)
    # score_valid = score_processing(score_valid)  # 加载score验证集

    source_test = np.asarray(triples_test_reverse[0], dtype=np.float32)  # 加载source测试集
    p_sm_test = np.asarray(triples_test_reverse[1], dtype=np.float32)  # 加载positive sm测试集
    n_sm_test = np.asarray(triples_test_reverse[2], dtype=np.float32)  # 加载negative sm测试集
    score_test = np.asarray(triples_test_reverse[3], dtype = np.float32)  # 加载score测试集
    score_test = np.asarray([int(i*10)/10 for i in score_test], dtype = np.float32)
    # score_test = score_processing(score_valid)  # 加载score测试集
    
    sources = {'train': source_train, 'valid': source_valid}
    p_sms = {'train': p_sm_train, 'valid': p_sm_valid}
    n_sms = {'train': n_sm_train, 'valid': n_sm_valid}
    # scores = {'train': score_train, 'valid': score_valid}
    dataset = {x: CustomDataSet(sources=sources[x], p_sms=p_sms[x], n_sms=n_sms[x])
               for x in ['train', 'valid']}

    shuffle = {'train': True, 'valid': True}

    dataloader = {x: DataLoader(dataset[x], batch_size=batch_size,
                                shuffle=shuffle[x], num_workers=0) for x in ['train', 'valid']}


    source_dim = source_train.shape[1]
    sm_dim = p_sm_train.shape[1]
    # num_class = label_train.shape[1]

    input_data_par = {}
    input_data_par['source_valid'] = source_valid
    input_data_par['p_sm_valid'] = p_sm_valid
    input_data_par['n_sm_valid'] = n_sm_valid
    input_data_par['score_valid'] = score_valid
    input_data_par['source_train'] = source_train
    input_data_par['p_sm_train'] = p_sm_train
    input_data_par['n_sm_train'] = n_sm_train
    input_data_par['score_train'] = score_train
    input_data_par['source_dim'] = source_dim
    input_data_par['sm_dim'] = sm_dim
    input_data_par['source_test'] = source_test
    input_data_par['p_sm_test'] = p_sm_test
    input_data_par['n_sm_test'] = n_sm_test
    input_data_par['score_test'] = score_test
    return dataloader, input_data_par