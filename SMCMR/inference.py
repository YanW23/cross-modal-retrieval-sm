import sys
import torch
import torch.nn as nn
from utils import *
from model import SMCMR
from get_info import getRegionInfo, get_table_initial_embedding_info

if __name__ == "__main__":
    args_input = []
    for i in range(1, len(sys.argv)):
        args_input.append(sys.argv[i])

    infer_semantic_model_file = args_input[0]
    infer_data_source_file = args_input[1]
    info_name = args_input[2]
    model_name = args_input[3]

    # print("infer_semantic_model_file: {}".format(infer_semantic_model_file))
    # print("infer_data_source_file: {}".format(infer_data_source_file))
    # print("info_name: {}".format(info_name))
    # print("model_name: {}".format(model_name))

    # infer_semantic_model_file = "semantic_models.txt"
    # infer_data_source_file = "s08/s08_Sub3_[TITLE,AUTHOR,DESCRIPTION].emb"
    # info_name = "info3.pt"
    # model_name = "model08"

    args = parse_args()

    """loading integration graph info"""
    load_info = torch.load('F:/SMCMR/integration_graph/info/' + info_name)
    vocab = load_info['vocab']
    index2layer_dict = load_info['index2layer_dict']
    num_nodes = load_info['num_nodes']
    edge_type_count = load_info['edge_type_count']
    features = load_info['features']
    nodes = load_info['nodes']
    labels = load_info['labels']
    node_neighs = load_info['node_neighs']

    # print("load_info success!")

    device = torch.device('cpu')

    model = SMCMR(args, num_nodes, edge_type_count, features).to(device)
    model = nn.DataParallel(model)

    state_dict = torch.load('F:/SMCMR/model/' + model_name, map_location=device)

    model.load_state_dict(state_dict)
    model.eval()

    # print("load state dict info success!")

    # for name, params in model.named_parameters():
    #     print(params)

    region_infos_semantic_models, max_region = getRegionInfo(args["semantic_model_path"] + infer_semantic_model_file, vocab, index2layer_dict)
    initial_table_embedding = get_table_initial_embedding_info(args, infer_data_source_file)

    # print("load region_infos_semantic_models and initial_table_embedding success!")

    score = model(nodes, labels, node_neighs, region_infos_semantic_models, max_region, initial_table_embedding)

    # print("score: {}".format(score))

    # print(torch.argmax(score))
    # print(type(torch.argmax(score)))

    print(torch.argmax(score).item())
    # print(type(torch.argmax(score).item()))
    # print("run success!")
