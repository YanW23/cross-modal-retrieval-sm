import torch
import numpy as np

def getRegionInfo(f_name, vocab, index2layer_dict):
    max_region = 0
    region_infos_semantic_models = list()

    with open(f_name, "r") as fp:
        for sub_semantic_model_label, sub_semantic_model_region_info_line in enumerate(fp):  # head1,edge1,tail1;head2,edge2,tail2||head3,edge3,tail3;head4,edge4,tail4;head5,edge5,tail5
            region_info_dict = dict()
            region_info_split_list = sub_semantic_model_region_info_line[:-1].split("||")
            for region_label, region_info in enumerate(region_info_split_list):
                region_info_dict["region" + str(region_label + 1)] = {_: set() for _ in ["nodes", "edges"]}
                for triple in region_info.split(";"):
                    head_edge_tail = triple.split(",")
                    head = head_edge_tail[0]
                    edge = head_edge_tail[1]
                    tail = head_edge_tail[2]

                    region_info_dict["region" + str(region_label + 1)]["nodes"].add(vocab[head].index)
                    region_info_dict["region" + str(region_label + 1)]["nodes"].add(vocab[tail].index)
                    region_info_dict["region" + str(region_label + 1)]["edges"].add(index2layer_dict[edge])

            if len(region_info_dict) > max_region:
                max_region = len(region_info_dict)

            region_infos_semantic_models.append(region_info_dict)

    return region_infos_semantic_models, max_region


def get_table_initial_embedding_info(opt, file_name):
    initial_table_embeddings = list()
    with open(opt["table_path"] + file_name, "r") as f:
        for region_emb in f:
            table_region_embedding = np.array((region_emb[:-1].split(" "))[1:], dtype=np.float32)
            assert table_region_embedding.shape[0] == opt["table_dim"], "invalid table_region_embedding"
            initial_table_embeddings.append(table_region_embedding)
    initial_table_embeddings = torch.tensor(initial_table_embeddings, dtype=torch.float32).unsqueeze(0)
    return initial_table_embeddings
