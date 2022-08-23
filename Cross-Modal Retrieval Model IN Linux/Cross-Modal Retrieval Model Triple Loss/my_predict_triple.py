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
    p_sm_embedding = embedding_string2array(args_input[1])
    # n_sm_embedding = embedding_string2array(args_input[1])
    # print("source_embedding.size:{}||sm_embedding.size:{}".format(len(source_embedding), len(sm_embedding)))
    # print('...Start predict...')
    model_predict = torch.load('F:\\Cross-Modal Retrieval Model IN Linux\\Cross-Modal Retrieval Model Triple Loss\\models\\model1', map_location=torch.device('cpu'))
    model_predict.eval()

    with torch.no_grad():
        source_embedding_predict, p_sm_embedding_predict, n_sm_embedding_predict = model_predict(torch.tensor(np.expand_dims(source_embedding, axis=0)), torch.tensor(np.expand_dims(p_sm_embedding, axis=0)), torch.tensor(np.expand_dims(p_sm_embedding, axis=0)))

        Pos_dist = torch.sqrt((source_embedding_predict - p_sm_embedding_predict).pow(2).sum(1))
        predict_result = Pos_dist.numpy()
    # print("predict_result:{}".format(predict_result[0], '.4f'))
    print(predict_result[0])
    # print("...Predict complete!...")
    # 给定source_embedding和sm_embedding 计算两者匹配度


    # print("...Load predict data...")
    # PREDICT_DATA_DIR = "F:\\Cross-Modal Retrieval Model IN Linux\\Cross-Modal Retrieval Model L1 Loss\\TriplesForCross-Modal-Retrieval-Model\\s02\\all_triples_for_predict.txt"
    # input_data_par = get_predict_data(PREDICT_DATA_DIR)
    # print("...Load predict data complete!...")

    # # # 7.11 查看数据
    # # # for i in input_data_par.keys():
    # # #     if i == 'score_predict':
    # # #         print("{}:{}".format(i, (input_data_par[i][0])))
    # # #     else:
    # # #         print("{}:{}".format(i, len(input_data_par[i])))
    # # # # print("score_test.type:{}".format(type(input_data_par['score_predict'])))
    # # # 7.11 查看数据
    
    # print('...Start predict...')
    # model_predict = torch.load('F:\\Cross-Modal Retrieval Model IN Linux\\Cross-Modal Retrieval Model L1 Loss\\models\\model8', map_location=torch.device('cpu'))
    # model_predict.eval()
    # # print(next(model_predict.parameters()).device)
    # with torch.no_grad():
    #     view_feature = model_predict(torch.tensor(np.expand_dims(input_data_par['source_predict'][10], axis=0)), torch.tensor(np.expand_dims(input_data_par['sm_predict'][10], axis=0)))
    #     score = torch.tensor(np.expand_dims(input_data_par['score_predict'][10], axis=0))
    #     predict_result = nn.Sigmoid()((view_feature).detach().cpu())
    #     predict_result = predict_result.numpy()
    #     score = score.numpy()
    #     results = zip(predict_result, score)
    # print("results:{}".format(list(results)))
    # print("predict_result:{}".format(predict_result[0], '.4f'))
    # print("...Predict complete!...")
