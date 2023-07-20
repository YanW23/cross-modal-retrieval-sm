import math
import torch
import torch.nn as nn
import torch.nn.functional as F
import numpy as np
from numpy import random
from torch.nn.parameter import Parameter
from collections import OrderedDict

def l2norm(X, dim, eps=1e-8):
    """L2-normalize columns of X
    """
    # norm = torch.pow(X, 2).sum(dim=dim, keepdim=True).sqrt() + eps
    norm = torch.sqrt(torch.pow(X, 2).sum(dim=dim, keepdim=True) + eps) + eps
    X = torch.div(X, norm)
    return X

def cosine_similarity(x1, x2, dim=1, eps=1e-8):
    """Returns cosine similarity between x1 and x2, computed along dim."""
    w12 = torch.sum(x1 * x2, dim) # Multiplication of corresponding positions
    w1 = torch.norm(x1, 2, dim)
    w2 = torch.norm(x2, 2, dim)
    return (w12 / (w1 * w2).clamp(min=eps))

class GATNEModel(nn.Module):
    def __init__(
        self, num_nodes, embedding_size, embedding_u_size, edge_type_count, dim_a, features, embed_size, no_smnorm=False
    ):
        super(GATNEModel, self).__init__()
        self.num_nodes = num_nodes
        self.embedding_size = embedding_size
        self.embedding_u_size = embedding_u_size
        self.edge_type_count = edge_type_count
        self.dim_a = dim_a

        self.features = None
        if features is not None:
            self.features = features
            feature_dim = self.features.shape[-1]
            self.embed_trans = Parameter(torch.FloatTensor(feature_dim, embedding_size))
            self.u_embed_trans = Parameter(torch.FloatTensor(edge_type_count, feature_dim, embedding_u_size))
        else:
            self.node_embeddings = Parameter(torch.FloatTensor(num_nodes, embedding_size))
            self.node_type_embeddings = Parameter(
                torch.FloatTensor(num_nodes, edge_type_count, embedding_u_size)
            )
        self.trans_weights = Parameter(
            torch.FloatTensor(edge_type_count, embedding_u_size, embedding_size)
        )
        self.trans_weights_s1 = Parameter(
            torch.FloatTensor(edge_type_count, embedding_u_size, dim_a)
        )
        self.trans_weights_s2 = Parameter(torch.FloatTensor(edge_type_count, dim_a, 1))

        """add on 2023/06/11"""
        self.embed_size = embed_size
        self.no_smnorm = no_smnorm
        self.sm_fc_local = nn.Linear(embedding_size, embed_size)

        self.reset_parameters()

    def reset_parameters(self):
        if self.features is not None:
            self.embed_trans.data.normal_(std=1.0 / math.sqrt(self.embedding_size))
            self.u_embed_trans.data.normal_(std=1.0 / math.sqrt(self.embedding_size))
        else:
            self.node_embeddings.data.uniform_(-1.0, 1.0)
            self.node_type_embeddings.data.uniform_(-1.0, 1.0)
        self.trans_weights.data.normal_(std=1.0 / math.sqrt(self.embedding_size))
        self.trans_weights_s1.data.normal_(std=1.0 / math.sqrt(self.embedding_size))
        self.trans_weights_s2.data.normal_(std=1.0 / math.sqrt(self.embedding_size))

        """add on 2023/06/11"""
        """Xavier initialization for the fully connected layer"""
        r = np.sqrt(6.) / np.sqrt(self.sm_fc_local.in_features +
                                  self.sm_fc_local.out_features)
        self.sm_fc_local.weight.data.uniform_(-r, r)
        self.sm_fc_local.bias.data.fill_(0)

    def get_embeddings(self, last_node_embed, region_infos_semantic_models, max_region):
        sm_embeddings = torch.zeros((len(region_infos_semantic_models), max_region, self.embedding_size), dtype=torch.float32) # (semantic_model_num, max_region_num, embedding_size)

        # iterate and obtain the embedding for the semantic model
        for region_info_semantic_model_index, region_info_semantic_model in enumerate(region_infos_semantic_models):
            sm_embedding = torch.zeros((max_region, self.embedding_size), dtype=torch.float32)
            for region_info_index, region_info in region_info_semantic_model.items():
                embedding_index = list()
                for node_index in region_info["nodes"]:
                    for edge_index in region_info["edges"]:
                        embedding_index.append(node_index * self.edge_type_count + edge_index)
                region_embedding = last_node_embed[embedding_index]
                region_embedding = torch.mean(region_embedding, dim=0)
                sm_embedding[(int)(region_info_index.split("region")[-1]) - 1, :] = region_embedding

            sm_embedding = F.normalize(sm_embedding, dim=1)
            sm_embeddings[region_info_semantic_model_index, :, :] = sm_embedding

        return sm_embeddings


    def forward(self, train_inputs, train_types, node_neigh, region_infos_semantic_models, max_region):
        if self.features is None:
            node_embed = self.node_embeddings[train_inputs]
            node_embed_neighbors = self.node_type_embeddings[node_neigh]
        else:
            node_embed = torch.mm(self.features[train_inputs], self.embed_trans) # (train_input.size(0), sm_embedding_dim(200))
            node_embed_neighbors = torch.einsum('bijk,akm->bijam', self.features[node_neigh], self.u_embed_trans) # (train_input.size(0), edge_type_count, node_neigh_num, edge_type_count, edge_type_embedding_dim(10))
        node_embed_tmp = torch.diagonal(node_embed_neighbors, dim1=1, dim2=3).permute(0, 3, 1, 2) # (train_input.size(0), edge_type_count, node_neigh_num, edge_type_embedding_dim(10))
        node_type_embed = torch.sum(node_embed_tmp, dim=2) # (train_input.size(0), edge_type_count, edge_type_embedding_dim(10))

        trans_w = self.trans_weights[train_types] # (train_input.size(0), edge_type_embedding_dim(10), sm_embedding_dim(200))
        trans_w_s1 = self.trans_weights_s1[train_types] # (train_input.size(0), edge_type_embedding_dim(10), attn_embedding_dim(20))
        trans_w_s2 = self.trans_weights_s2[train_types] # (train_input.size(0), attn_embedding_dim(20), 1)

        attention = F.softmax(
            torch.matmul(
                torch.tanh(torch.matmul(node_type_embed, trans_w_s1)), trans_w_s2
            ).squeeze(2),
            dim=1,
        ).unsqueeze(1)
        node_type_embed = torch.matmul(attention, node_type_embed) # (train_input.size(0), 1, edge_type_embedding_dim(10))
        node_embed = node_embed + torch.matmul(node_type_embed, trans_w).squeeze(1) # (train_input.size(0), sm_embedding_dim(200))

        last_node_embed = F.normalize(node_embed, dim=1) # (train_input.size(0), sm_embedding_dim(200))

        """obtain all embeddings for input semantic models"""
        sm_embeddings = self.get_embeddings(last_node_embed, region_infos_semantic_models, max_region) # (region_infos_semantic_models.size(0), max_region, sm_embedding_dim(200))

        if torch.cuda.is_available():
            sm_embeddings = sm_embeddings.cuda()

        sm_feat_local = self.sm_fc_local(sm_embeddings)# (region_infos_semantic_models.size(0), max_region, embed_size(1024))
        # normalize in the joint embedding space
        if not self.no_smnorm:
            sm_feat_local = l2norm(sm_feat_local, dim=-1)

        return sm_feat_local # (region_infos_semantic_models.size(0), embed_size(1024)); (region_infos_semantic_models.size(0), max_region, embed_size(1024))

    def load_state_dict(self, state_dict):
        """Copies parameters. overwritting the default one to accept state_dict from Full model"""
        own_state = self.state_dict()
        new_state = OrderedDict()
        for name, param in state_dict.items():
            if name in own_state:
                new_state[name] = param

        super(GATNEModel, self).load_state_dict(new_state)

class EncoderTable(nn.Module):
    def __init__(self, table_dim, embed_size, no_tablenorm=False):
        super(EncoderTable, self).__init__()
        self.embed_size = embed_size
        self.no_tablenorm = no_tablenorm

        self.table_fc_local = nn.Linear(table_dim, embed_size)

        self.reset_parameters()

    def reset_parameters(self):
        """Xavier initialization for the fully connected layer"""
        r = np.sqrt(6.) / np.sqrt(self.table_fc_local.in_features +
                                  self.table_fc_local.out_features)
        self.table_fc_local.weight.data.uniform_(-r, r)
        self.table_fc_local.bias.data.fill_(0)

    def forward(self, initial_table_embeddings):
        table_feat_local = self.table_fc_local(initial_table_embeddings)

        # normalize in the joint embedding space
        if not self.no_tablenorm:
            table_feat_local = l2norm(table_feat_local, dim=-1)

        return table_feat_local

    def load_state_dict(self, state_dict):
        """Copies parameters. overwritting the default one to accept state_dict from Full model"""
        own_state = self.state_dict()
        new_state = OrderedDict()
        for name, param in state_dict.items():
            if name in own_state:
                new_state[name] = param

        super(EncoderTable, self).load_state_dict(new_state)

def func_attention(query, context, opt, smooth, eps=1e-8, weight=None):
    """
    :param query: (n_context, queryL, d)
    :param context: (n_context, sourceL, d)
    :return: weightedContext (batch, queryL, d), attn_out (batch, sourceL, queryL)
    """
    batch_size_q, queryL = query.size(0), query.size(1)
    batch_size, sourceL = context.size(0), context.size(1)

    # Get attention
    # --> (batch, d, queryL)
    queryT = torch.transpose(query, 1, 2)

    # (batch, sourceL, d)(batch, d, queryL) -> (batch, sourceL, queryL)
    attn = torch.bmm(context, queryT)

    if opt["raw_feature_norm"] == "softmax":
        # --> (batch*sourceL, queryL)
        attn = attn.view(batch_size*sourceL, queryL)
        attn = F.softmax(attn, dim=1)
        # --> (batch, sourceL, queryL)
        attn = attn.view(batch_size, sourceL, queryL)
    elif opt["raw_feature_norm"] == "l2norm":
        attn = l2norm(attn, 2)
    elif opt["raw_feature_norm"] == "clipped_l2norm":
        attn = nn.LeakyReLU(0.1)(attn)
        attn = l2norm(attn, 2)
    elif opt["raw_feature_norm"] == "clipped":
        attn = nn.LeakyReLU(0.1)(attn)
    elif opt["raw_feature_norm"] == "no_norm":
        pass
    else:
        raise ValueError("unknown first norm type:", opt["raw_feature_norm"])

    if weight is not None:
      attn = attn + weight

    attn_out = attn.clone()

    # --> (batch, queryL, sourceL)
    attn = torch.transpose(attn, 1, 2).contiguous()
    # --> (batch*queryL, sourceL)
    attn = attn.view(batch_size * queryL, sourceL)

    attn = F.softmax(attn * smooth, dim=1)
    # --> (batch, queryL, sourceL)
    attn = attn.view(batch_size, queryL, sourceL)
    # --> (batch, sourceL, queryL)
    attnT = torch.transpose(attn, 1, 2).contiguous()

    # --> (batch, d, sourceL)
    contextT = torch.transpose(context, 1, 2)
    # (batch x d x sourceL)(batch x sourceL x queryL)
    # --> (batch, d, queryL)
    weightedContext = torch.bmm(contextT, attnT)
    # --> (batch, queryL, d)
    weightedContext = torch.transpose(weightedContext, 1, 2)

    return weightedContext, attn_out

class SMCMR(nn.Module):
    def __init__(self, opt, num_nodes, edge_type_count, features):
        super(SMCMR, self).__init__()

        if torch.cuda.is_available():
            features = features.cuda()

        self.opt = opt
        self.sm_enc = GATNEModel(num_nodes, opt["dimensions"], opt["edge_dim"], edge_type_count, opt["att_dim"], features, opt["embed_size"], opt["no_smnorm"])
        self.table_enc = EncoderTable(opt["table_dim"], opt["embed_size"], opt["no_tablenorm"])

        # print("*********using gate to fusion information**************")
        self.linear_t2s = nn.Linear(opt["embed_size"] * 2, opt["embed_size"])
        self.gate_t2s = nn.Linear(opt["embed_size"] * 2, opt["embed_size"])

    def gated_memory_t2s(self, input_0, input_1):

        input_cat = torch.cat([input_0, input_1], 2)
        input_1 = F.tanh(self.linear_t2s(input_cat))
        gate = torch.sigmoid(self.gate_t2s(input_cat))
        output = input_0 * gate + input_1 * (1-gate)

        return output

    def forward_emb(self, input_nodes, input_edge_types, input_node_neigh, region_infos_semantic_models, max_region, initial_table_embeddings):
        """Compute the semantic model and table embeddings"""

        if torch.cuda.is_available():
            input_nodes = input_nodes.cuda()
            input_edge_types = input_edge_types.cuda()
            input_node_neigh = input_node_neigh.cuda()
            initial_table_embeddings = initial_table_embeddings.cuda()

        # print("enter forward_emb!")

        sm_emb = self.sm_enc(input_nodes, input_edge_types, input_node_neigh, region_infos_semantic_models, max_region)
        table_emb = self.table_enc(initial_table_embeddings)

        # print("forward_emb success!")

        return sm_emb, table_emb

    def forward_score(self, sm_emb, table_emb, **kwargs):
        """Compute the loss given pairs of semantic model and table embeddings"""
        score_t2i = self.xattn_score_Table_SMCMR(sm_emb, table_emb, self.opt)
        score_t2i = torch.stack(score_t2i, 0).sum(0)
        score = torch.sigmoid(score_t2i.squeeze(0))
        # score = torch.squeeze(score_t2i, 0)

        return score

    def forward(self, input_nodes, input_edge_types, input_node_neigh, region_infos_semantic_models, max_region, initial_table_embeddings):
        """One training step given semantic models and tables"""
        # print("forward success!")
        sm_emb, table_emb = self.forward_emb(input_nodes, input_edge_types, input_node_neigh, region_infos_semantic_models, max_region, initial_table_embeddings)
        scores = self.forward_score(sm_emb, table_emb)
        return scores

    def xattn_score_Table_SMCMR(self, sm_emb, table_emb, opt):
        """
        :param sm_emb:
        :param table_emb:
        :return:
        """
        similarities = [[] for _ in range(opt["iteration_step"])]
        n_semantic_model = sm_emb.size(0)
        n_table = table_emb.size(0)
        semantic_models = sm_emb.float()
        tables = table_emb.float()

        for i in range(n_table):
            table_i = tables[i]
            table_i_expand = table_i.repeat(n_semantic_model, 1, 1)

            query = table_i_expand
            context = semantic_models
            for j in range(opt["iteration_step"]):
                # "feature_update" by default
                attn_feat, _ = func_attention(query, context, opt, smooth=opt["lambda_softmax"])

                # print("define the cosine_similarity function")
                row_sim = cosine_similarity(table_i_expand, attn_feat, dim=2)
                row_sim = row_sim.mean(dim=1, keepdim=True)
                similarities[j].append(row_sim)

                query = self.gated_memory_t2s(query, attn_feat)

                if not opt["no_SMCMR_norm"]:
                    query = l2norm(query, dim=-1)

        new_similarities = []
        # print("compute new_similarities")
        for j in range(opt["iteration_step"]):
            if len(similarities[j]) == 0:
                new_similarities.append([])
                continue
            similarities_one = torch.cat(similarities[j], 1).double()
            if self.training:
                similarities_one = similarities_one.transpose(0,1)
            new_similarities.append(similarities_one)

        return new_similarities
