import os
import argparse
import torch
import numpy as np
from collections import defaultdict
from sklearn.preprocessing import LabelEncoder, OneHotEncoder
from torch.utils.hipify.hipify_python import bcolors

from tqdm import tqdm
from six import iteritems

class Vocab(object):

    def __init__(self, count, index):
        self.count = count
        self.index = index

def parse_args():
    # parser = argparse.ArgumentParser()

    # parser.add_argument('--gpuid', default=0, type=str,
    #                     help='gpuid')
    # parser.add_argument('--margin', default=0.2, type=float,
    #                     help='Rank loss margin.')
    # parser.add_argument('--embed_size', default=1024, type=int,
    #                     help='Dimensionality of the joint embedding.')
    # parser.add_argument('--workers', default=10, type=int,
    #                     help='Number of data loader workers.')

    # parser.add_argument('--no_smnorm', action='store_true',
    #                     help='Do not normalize the semantic model embeddings.')
    # parser.add_argument('--integration_info_path', type=str, default='F:/SMCMR/integration_graph/info/info.pt',
    #                     help='Integration graph info.')
    # parser.add_argument('--semantic_model_path', default='F:/SMCMR/semantic_model/',
    #                     help='Input semantic model path.')
    # parser.add_argument('--dimensions', type=int, default=200,
    #                     help='Number of dimensions. Default is 200.')
    # parser.add_argument('--edge-dim', type=int, default=10,
    #                     help='Number of edge embedding dimensions. Default is 10.')
    # parser.add_argument('--att-dim', type=int, default=20,
    #                     help='Number of attention dimensions. Default is 20.')

    # parser.add_argument('--no_tablenorm', action='store_true',
    #                     help='Do not normalize the table embeddings.')
    # parser.add_argument('--table_path', default='F:/SMCMR/data_source/',
    #                     help='Input table path')
    # parser.add_argument('--table_dim', default=300, type=int,
    #                     help='Dimensionality of the table embedding.')
    # parser.add_argument('--raw_feature_norm', default="clipped_l2norm",
    #                     help='clipped_l2norm|l2norm|clipped_l1norm|l1norm|no_norm|softmax')
    # parser.add_argument('--lambda_softmax', default=9., type=float,
    #                     help='Attention softmax temperature.')

    # parser.add_argument('--iteration_step', default=3, type=int,
    #                     help='routing_step')
    # parser.add_argument('--no_SMCMR_norm', action='store_true',
    #                     help='Do not normalize the routing feature.')
    # return parser.parse_args()

    parse_args = dict()
    parse_args["gpuid"] = 0
    parse_args["margin"] = 0.2
    parse_args["embed_size"] = 1024
    parse_args["workers"] = 10
    
    parse_args["no_smnorm"] = False
    parse_args["integration_info_path"] = 'F:/SMCMR/integration_graph/info/info.pt'
    parse_args["semantic_model_path"] = 'F:/SMCMR/semantic_model/'
    parse_args["dimensions"] = 200
    parse_args["edge_dim"] = 10
    parse_args["att_dim"] = 20

    parse_args["no_tablenorm"] = False
    parse_args["table_path"] = 'F:/SMCMR/data_source/'
    parse_args["table_dim"] = 300
    parse_args["raw_feature_norm"] = "clipped_l2norm"
    parse_args["lambda_softmax"] = 9.

    parse_args["iteration_step"] = 1
    parse_args["no_SMCMR_norm"] = False

    return parse_args
