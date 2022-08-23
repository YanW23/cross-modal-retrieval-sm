# from matplotlib.pyplot import axis
import torch
import numpy as np
# from my_model import IDCM_NN
import torch.nn as nn
# import torch.nn.functional as F
import sys


def get_predict_data(predict_path):
    # 加载predict数据集
    all_predict_triples_file = open(predict_path, 'r', encoding='utf-8')
    all_predict_triples_list = all_predict_triples_file.readlines()
    predict_triples = []
    for line in all_predict_triples_list:
        line_predict_tup = eval(line)
        line_predict_tup2list = list(line_predict_tup)
        predict_triples.append(line_predict_tup2list)
    triples_predict_reverse = list(map(list, zip(*predict_triples)))
    # 加载test数据集

    source_predict = np.asarray(triples_predict_reverse[0], dtype=np.float32)  # 加载source测试集
    sm_predict = np.asarray(triples_predict_reverse[1], dtype=np.float32)  # 加载sm测试集
    score_predict = np.asarray(triples_predict_reverse[2], dtype=np.float32)  # 加载score测试集
    score_predict = np.asarray([int(i*10)/10 for i in score_predict], dtype=np.float32)

    input_data_par = {}
    input_data_par['source_predict'] = source_predict
    input_data_par['sm_predict'] = sm_predict
    input_data_par['score_predict'] = score_predict
    return input_data_par


def embedding_string2array(source_embedding):
    source_embeeding_tup = eval(source_embedding)
    source_embedding_tup2list = list(source_embeeding_tup)
    source_embedding_array = np.asarray(source_embedding_tup2list, dtype=np.float32)
    return source_embedding_array

    
if __name__ == "__main__":
    # 给定source_embedding和sm_embedding 计算两者匹配度
    # print("...Load source_embedding_array...")
    args_input = []
    for i in range(1, len(sys.argv)):
        args_input.append(sys.argv[i])
    
    source_embedding = embedding_string2array(args_input[0])
    p_sm_embedding_joint_file = open(args_input[1], "r", encoding='utf-8')
    # p_sm_embedding_joint_file = open("F:\\Cross-Modal Retrieval Model IN Linux\\Cross-Modal Retrieval Model Triple Loss\\sm_embedding_joint.txt", "r", encoding='utf-8')
    p_sm_embedding_joint_list = p_sm_embedding_joint_file.read().splitlines()
    p_sm_embedding_joint_file.close()
    p_sm_embedding_joint = p_sm_embedding_joint_list[0].split(";")
    
    model_predict = torch.load('F:\\Cross-Modal Retrieval Model IN Linux\\Cross-Modal Retrieval Model Triple Loss\\models\\model3', map_location=torch.device('cpu'))
    model_predict.eval()

    index = 0
    predict_result_distance = 10000.0
    predict_result_index = 0
    for i in p_sm_embedding_joint:
        with torch.no_grad():
            p_sm_embedding = embedding_string2array(i)
            source_embedding_predict, p_sm_embedding_predict, n_sm_embedding_predict = model_predict(torch.tensor(np.expand_dims(source_embedding, axis=0)), torch.tensor(np.expand_dims(p_sm_embedding, axis=0)), torch.tensor(np.expand_dims(p_sm_embedding, axis=0)))

            Pos_dist = torch.sqrt((source_embedding_predict - p_sm_embedding_predict).pow(2).sum(1))
            predict_result = Pos_dist.numpy()
        if predict_result[0] < predict_result_distance:
            predict_result_distance = predict_result[0]
            predict_result_index = index
        index += 1
    print(predict_result_index)
