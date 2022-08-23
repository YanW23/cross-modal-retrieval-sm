import torch
import torch.nn as nn
import torch.nn.functional as F
from torchvision import models


# class VGGNet(nn.Module):
#     def __init__(self):
#         """Select conv1_1 ~ conv5_1 activation maps."""
#         super(VGGNet, self).__init__()
#         self.vgg = models.vgg19_bn(pretrained=True)
#         self.vgg_features = self.vgg.features
#         self.fc_features = nn.Sequential(*list(self.vgg.classifier.children())[:-2])

#     def forward(self, x):
#         """Extract multiple convolutional feature maps."""
#         features = self.vgg_features(x).view(x.shape[0], -1)
#         features = self.fc_features(features)
#         return features


class SourceNN(nn.Module):
    """Network to learn source representations"""  # 学习source表示的网络
    def __init__(self, input_dim=300, output_dim=250):
        super(SourceNN, self).__init__()
        self.denseL1 = nn.Linear(input_dim, output_dim)
        
    def forward(self, x):
        out = F.relu(self.denseL1(x))
        return out


class SMNN(nn.Module):
    """Network to learn sm representations"""  # 学习p_sm和n_sm表示的网络
    def __init__(self, input_dim=200, output_dim=250):
        super(SMNN, self).__init__()
        self.denseL1 = nn.Linear(input_dim, output_dim)

    def forward(self, x):
        out = F.relu(self.denseL1(x))
        return out


class IDCM_NN(nn.Module):
    """Network to learn source-sm representations"""  # 学习source-sm表示
    def __init__(self, source_input_dim=300, source_output_dim=1024,
                 sm_input_dim=200, sm_output_dim=1024, minus_one_dim=512):
        super(IDCM_NN, self).__init__()
        self.source_net = SourceNN(source_input_dim, source_output_dim)  # source embedding(300->1024)
        self.sm_net = SMNN(sm_input_dim, sm_output_dim)  # sm embedding(200->1024)
        self.linearLayer = nn.Linear(source_output_dim, minus_one_dim)  # source or sm embedding(1024->512)

    def forward(self, source, p_sm, n_sm):
        view1_feature = self.source_net(source)  # source embedding(300->1024)
        view2_feature = self.sm_net(p_sm)  # p_sm embedding(200->1024)
        view3_feature = self.sm_net(n_sm)  # n_sm embedding(200->1024)
        view1_feature = self.linearLayer(view1_feature)  # source embedding(1024->512)
        view2_feature = self.linearLayer(view2_feature)  # p_sm embedding(1024->512)
        view3_feature = self.linearLayer(view3_feature)  # n_sm embedding(1024->512)
        # #-------------------------#
        # #   相减取绝对值
        # #-------------------------#     
        # view_feature = torch.abs(view1_feature - view2_feature)
        # view_feature = self.linearLayer2(view_feature)
        # # view_feature = self.linearLayer3(view_feature)
        # view_feature = view_feature.squeeze(-1)
        # # feature = self.linearLayer3(torch.cat([view1_feature, view2_feature], dim=1))
        # # feature = self.linearLayer4(feature)
        # # feature = self.linearLayer5(feature)
        # # view_feature = feature.squeeze(-1)
        
        return view1_feature, view2_feature, view3_feature

# net = IDCM_NN()
# print(net)
