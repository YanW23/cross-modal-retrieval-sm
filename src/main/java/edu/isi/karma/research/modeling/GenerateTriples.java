package edu.isi.karma.research.modeling;

import com.opencsv.CSVReader;
import com.opencsv.CSVReaderBuilder;
import edu.isi.karma.modeling.alignment.GraphVizLabelType;
import edu.isi.karma.modeling.alignment.GraphVizUtil;
import edu.isi.karma.modeling.alignment.SemanticModel;
import edu.isi.karma.modeling.alignment.learner.ModelReader;
import edu.isi.karma.modeling.research.Params;
import edu.isi.karma.rep.alignment.*;
import org.python.antlr.ast.Dict;

import java.io.*;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.util.*;

import static edu.isi.karma.research.modeling.EliminateNodes.getRegionSemanticModels;
import static edu.isi.karma.research.modeling.EliminateNodes.getSemanticModelRootList;
import static edu.isi.karma.research.modeling.FindPaths.findAllPathNode;
import static edu.isi.karma.research.modeling.PartitionSamples.*;
import static edu.isi.karma.research.modeling.SearchForSemanticModels.CreateFile;
import static edu.isi.karma.research.modeling.SearchForSemanticModels.deleteFile;
import static edu.isi.karma.research.modeling.SortUtils.getSubDataSourceTxtName;
import static edu.isi.karma.research.modeling.SortUtils.sortMapByValues;

public class GenerateTriples {

    public static Integer getAttributeNum(String SubInt){ // Sub1
        Integer subAttributesNum = Integer.parseInt(SubInt.split("Sub")[1]);
        System.out.println("subAttributesNum:" + subAttributesNum);
        return subAttributesNum;
    }

    public static Map<String,Set<String>> getRegionTriplesAfterPartitionForOneSemanticModel(List<SemanticModel> regionSemanticModels, Integer linksNumForOneSemanticModel){
        String headNode, edge, tailNode;
        String triple, regionTriples;
        List<LabeledLink> linkList = new ArrayList<LabeledLink>();
        List<String> triplesForRegionSemanticModels = new ArrayList<String>();
        String triplesStringForRegionSemanticModels = "";
        Set<String> allTriplesStrSet = new HashSet<String>();
        Map<String,Set<String>> regionTriplesInfoMap = new HashMap<String,Set<String>>();
        int regionSemanticModelIndex = 0;

        for(SemanticModel regionSemanticModel: regionSemanticModels){
            ++regionSemanticModelIndex;
            regionTriples = "";
            linkList = new ArrayList<LabeledLink>(regionSemanticModel.getGraph().edgeSet());
            for(int i = 0; i < linkList.size(); i++){
                triple = null;
                headNode = null;
                edge = null;
                tailNode = null;

                headNode = getLabelName(linkList.get(i).getSource().getId());

                edge = getLabelName(linkList.get(i).getUri());

                if(linkList.get(i).getTarget() instanceof ColumnNode){
                    tailNode = (((ColumnNode) linkList.get(i).getTarget()).getColumnName());
                }
                else{
                    tailNode = getLabelName(linkList.get(i).getTarget().getId());
                }

                triple = headNode + "," + edge + "," + tailNode;

                if(regionSemanticModelIndex == regionSemanticModels.size())
                    allTriplesStrSet.add(triple);

                if(i < (linkList.size()-1)) {
                    regionTriples = regionTriples + triple + ";";
                }
                else{
                    regionTriples = regionTriples + triple;
                }
            }
            triplesForRegionSemanticModels.add(regionTriples);
            if(regionSemanticModelIndex < regionSemanticModels.size())
                triplesStringForRegionSemanticModels = triplesStringForRegionSemanticModels + regionTriples + "||";
            else
                triplesStringForRegionSemanticModels = triplesStringForRegionSemanticModels + regionTriples;
        }
        assert triplesForRegionSemanticModels.size() == regionSemanticModels.size(): "triplesForRegionSemanticModels.size != regionSemanticModels.size";
        assert allTriplesStrSet.size() == linksNumForOneSemanticModel: "obtain the wrong all triples info for the given semantic model";

        regionTriplesInfoMap.put(triplesStringForRegionSemanticModels, allTriplesStrSet);

        return regionTriplesInfoMap;
    }

    public static Map<String,Set<String>> getPartitionRegionTriplesStringForOneSemanticModel(SemanticModel sm, String partitionGraphSavePath, Boolean flag, String dataSetName) throws Exception {
        String SM_Graphviz_Path = partitionGraphSavePath + "partition-models-graphviz";
        String SM_Json_Path = partitionGraphSavePath + "partition-models-json";
        String SM_Graphviz_Path_color = partitionGraphSavePath + "partition-models-graphviz-color";
        String SM_Json_Path_color = partitionGraphSavePath + "partition-models-json-color";

        deleteFile(SM_Graphviz_Path);
        deleteFile(SM_Json_Path);
        deleteFile(SM_Graphviz_Path_color);
        deleteFile(SM_Json_Path_color);

        CreateFile(SM_Graphviz_Path);
        CreateFile(SM_Json_Path);
        CreateFile(SM_Graphviz_Path_color);
        CreateFile(SM_Json_Path_color);

//        String triplesStringForRegionSemanticModels;
        Map<String,Set<String>> regionTriplesInfoMap = new HashMap<String,Set<String>>();

        Map<String,Integer> outgoingLinksForNode = new HashMap<String,Integer>();
        List<String> regionColumnNamesList = new ArrayList<String>();
        List<SemanticModel> regionSemanticModels = new ArrayList<SemanticModel>();
        SemanticModel regionSemanticModel = null;
        int numOfOutgoingLinks = 0;
        Map<String,List<String>> regionColumnNames = new HashMap<String,List<String>>();
        int regionIndex = 0;
        SemanticModel cloneSM = null;
        List<String> temp_columnNames = new ArrayList<String>();
        List<ColumnNode> columnNodes = new ArrayList<ColumnNode>(sm.getColumnNodes());
        List<String> columnNames = new ArrayList<String>();
        List<Node> rootNodeList = null;
        List<String> rootNameList = new ArrayList<String>();
        Map<String,Integer> regionInterNodeDepth = new HashMap<String,Integer>();
        Map<String,Integer> sortedRegionInterNodeDepth = new HashMap<String,Integer>();
        int shortestPath = 100;
        Map<List<String>,String> columnNamesWithRegionNode = new HashMap<List<String>,String>();
        Integer linksNumForOneSemanticModel = sm.getGraph().edgeSet().size();

        System.out.println("sm.nodes.size:" + sm.getGraph().vertexSet().size());
        System.out.println("sm.links.size:" + linksNumForOneSemanticModel);

        for(ColumnNode column_node:columnNodes){
            columnNames.add(column_node.getColumnName());
        }

        //if there is 1 column node and 2 nodes and 1 edge, there is only one partition region
        if((columnNodes.size() == 1) && (sm.getGraph().vertexSet().size() == 2) && (sm.getGraph().edgeSet().size() == 1)){
            InternalNode internalNode = null;
            regionSemanticModels.add(sm);
            for(Node node: sm.getGraph().vertexSet()){
                if(node instanceof ColumnNode)
                    continue;
                else{
                    internalNode = (InternalNode) node;
                    break;
                }
            }
            if(dataSetName == "CRM") {
                GraphVizUtil.exportSemanticModelToGraphvizForPartition(sm, sm.getGraph().vertexSet(), GraphVizLabelType.LocalId,
                        GraphVizLabelType.LocalUri, true, true, SM_Graphviz_Path_color + "/region1-" + getInternalNodeName(internalNode.getId()) + Params.GRAPHVIS_MAIN_FILE_EXT);
            }
            else{
                GraphVizUtil.exportSemanticModelToGraphvizForPartition(sm, sm.getGraph().vertexSet(), GraphVizLabelType.LocalId,
                        GraphVizLabelType.LocalUri, true, true, SM_Graphviz_Path_color + "/region1-" + getInternalNodeNameEDM(internalNode.getId()) + Params.GRAPHVIS_MAIN_FILE_EXT);
            }
        }
        //otherwise, we need to identify their regions for the given semantic model
        else{
            //obtain all internal nodes with two or more outgoing links
            for(Node inter_node: sm.getInternalNodes()){
                numOfOutgoingLinks = 0;
                for (DefaultLink link : sm.getGraph().edgeSet()) {
                    if (link.getSource().getId().equals(inter_node.getId())) {
                        ++numOfOutgoingLinks;
                    }
                }
                if(numOfOutgoingLinks > 1){
                    regionColumnNamesList = new ArrayList<String>();
                    outgoingLinksForNode.put(inter_node.getId(), numOfOutgoingLinks);
                    for (ColumnNode column_node : columnNodes) {
                        //check whether there is a path between the internal node and specific column node
                        FindPaths.connectedPathsNode = new ArrayList<List<Node>>();
                        findAllPathNode(new ArrayList<DefaultLink>(sm.getGraph().edgeSet()), inter_node.getId(), column_node.getId(), 100);
                        if (FindPaths.connectedPathsNode.size() > 0) {
                            regionColumnNamesList.add(column_node.getColumnName());
                        }
                    }
                    regionColumnNames.put(inter_node.getId(), regionColumnNamesList);
                }
            }

            for(String region_node_name : regionColumnNames.keySet()) {
                System.out.println("region_node_name:" + region_node_name + "|" + regionColumnNames.get(region_node_name));
            }

            //if there is only one internal nodes with more than one outgoing links, we identify there is only one region for the given semantic model
            if(outgoingLinksForNode.keySet().size() == 1){
                ++regionIndex;
                for(String key : outgoingLinksForNode.keySet()) {
                    try {
//                        GraphVizUtil.exportSemanticModelToGraphviz(sm, GraphVizLabelType.LocalId,
//                                GraphVizLabelType.LocalUri, true, true, SM_Graphviz_Path + "/" + "region" + regionIndex + "-" + getInternalNodeName(key) + Params.GRAPHVIS_MAIN_FILE_EXT);
                        if(dataSetName == "CRM") {
                            GraphVizUtil.exportSemanticModelToGraphvizForPartition(sm, sm.getGraph().vertexSet(), GraphVizLabelType.LocalId,
                                    GraphVizLabelType.LocalUri, true, true, SM_Graphviz_Path_color + "/" + "region" + regionIndex + "-" + getInternalNodeName(key) + Params.GRAPHVIS_MAIN_FILE_EXT);
                        }else{
                            GraphVizUtil.exportSemanticModelToGraphvizForPartition(sm, sm.getGraph().vertexSet(), GraphVizLabelType.LocalId,
                                    GraphVizLabelType.LocalUri, true, true, SM_Graphviz_Path_color + "/" + "region" + regionIndex + "-" + getInternalNodeNameEDM(key) + Params.GRAPHVIS_MAIN_FILE_EXT);
                        }
                    } catch (Exception e) {
                        e.printStackTrace();
                    }
                    regionSemanticModels.add(sm);
                }
            }
            else{
                /**sort region_inter_node by depth**/
                rootNodeList = getSemanticModelRootList(sm);
                for (Node root_node : rootNodeList) {
                    rootNameList.add(root_node.getId());
                }
                for(String inter_node : regionColumnNames.keySet()){
                    if (rootNameList.contains(inter_node)) {
                        System.out.println("root depth equals 1:" + inter_node);
                        regionInterNodeDepth.put(inter_node, 1);
                    }
                    else{
                        shortestPath = 100;
                        for(Node root : rootNodeList){
                            //find all paths from root to delColumnNode
                            System.out.println("root for depth:" + root.getId());
                            FindPaths.connectedPathsNode = new ArrayList<List<Node>>();
                            findAllPathNode(new ArrayList<DefaultLink>(sm.getGraph().edgeSet()), root.getId(), inter_node, 100);
                            if (FindPaths.connectedPathsNode.size() > 0) {
                                for (List<Node> path : FindPaths.connectedPathsNode) {
                                    if (path.size() < shortestPath) {
                                        shortestPath = path.size();
                                    }
                                }
                            }
                        }
                        regionInterNodeDepth.put(inter_node, shortestPath);
                    }
                }

                sortedRegionInterNodeDepth = SortMap(regionInterNodeDepth);

                for(String region_node_name : regionColumnNames.keySet()){
                    if (columnNamesWithRegionNode.keySet().contains(regionColumnNames.get(region_node_name))) {
                        //judge whether to change the region node with the same columnNamesList
                        if (sortedRegionInterNodeDepth.get(columnNamesWithRegionNode.get(regionColumnNames.get(region_node_name))) > sortedRegionInterNodeDepth.get(region_node_name)) {
                            flag = false;
                            columnNamesWithRegionNode.put(regionColumnNames.get(region_node_name), region_node_name);
                        }
                    } else {
                        columnNamesWithRegionNode.put(regionColumnNames.get(region_node_name), region_node_name);
                    }
                }

                for (String inter_node : sortedRegionInterNodeDepth.keySet()){
                    if (columnNamesWithRegionNode.values().contains(inter_node)) {
                        System.out.println("inter_node:" + inter_node + "|nodes.num:" + regionColumnNames.get(inter_node));
                        ++regionIndex;
                        temp_columnNames = new ArrayList<String>(columnNames);
                        temp_columnNames.removeAll(regionColumnNames.get(inter_node));
                        cloneSM = sm.clone();
                        if(dataSetName == "CRM") {
                            regionSemanticModel = getRegionSemanticModels(cloneSM, getInternalNodeName(inter_node), regionIndex, temp_columnNames, SM_Graphviz_Path, SM_Json_Path, flag);
                        }else{
                            regionSemanticModel = getRegionSemanticModels(cloneSM, getInternalNodeNameEDM(inter_node), regionIndex, temp_columnNames, SM_Graphviz_Path, SM_Json_Path, flag);
                        }
                        regionSemanticModels.add(regionSemanticModel);

                        /**NullPointerException annotate on 2023/06/21**/
//                        GraphVizUtil.exportSemanticModelToGraphvizForPartition(sm, regionSemanticModel.getGraph().vertexSet(), GraphVizLabelType.LocalId,
//                                GraphVizLabelType.LocalUri, true, true, SM_Graphviz_Path_color + "/" + "region" + regionIndex + "-" + getInternalNodeName(inter_node) + Params.GRAPHVIS_MAIN_FILE_EXT);
                    }
                }
            }
        }

        regionTriplesInfoMap = getRegionTriplesAfterPartitionForOneSemanticModel(regionSemanticModels, linksNumForOneSemanticModel);

        assert regionTriplesInfoMap.size() == 1: "obtain the wrong regionTriplesInfoMap";

        return regionTriplesInfoMap;
    }

//    public static Set<String> getAllTriplesForOneSemanticModel(SemanticModel sm){
//        Set<String> allTriples = new HashSet<String>();
//        for()
//        return null;
//    }

    public static List<String> getSimilarityScoresForOneSubNegativeSemanticModel(String filePath) throws IOException {
        List<String> simScoresList = new LinkedList<String>();
        File simFile = new File(filePath);

        try {
            InputStreamReader read = new InputStreamReader(new FileInputStream(simFile));
            BufferedReader bufferedReader = new BufferedReader(read);

            String lineScore = null;
            while ((lineScore = bufferedReader.readLine()) != null)
                simScoresList.add(lineScore);
        } catch (IOException e) {
            e.printStackTrace();
        }

        return simScoresList;
    }

    public static void getDataSetForOneDataSource(String positiveSMPath, String negativeSMPath, String partitionModelsPath, Map<String,Integer> attribute_index_dict, String subDataSourceTxtPath, String dataSetName) throws Exception {
        System.out.println("positiveSMPath:" + positiveSMPath);
        Boolean getAttributesFlag = null;

        File subDataSources = new File(positiveSMPath);

        int negative_sm_sub_same_index;
        List<String> negativeSimScoresList = new ArrayList<String>();

        Set<String> allSaveRegionTriplesForOneSubSemanticModel = new HashSet<String>();
        Set<Set<String>> triplesSetForSubSemanticModels = new HashSet<Set<String>>();

        Map<String,Set<String>> regionTriplesInfo = new HashMap<String,Set<String>>();
        String regionTriplesForOneSubSemanticModel;
        Set<String> allTriplesForOneSubSemanticModel = new HashSet<String>();


        for(File sub_data_source: Objects.requireNonNull(subDataSources.listFiles())){ // sub_data_source = s01_Sub1_1
            /** obtain and make .txt file (s01_Sub1_["Attribution","Title"].txt)
             * by read the first .model.json (s01_Sub1_1_Same1.model.json) **/
            String[] sub_data_source_file_info = sub_data_source.getName().split("_"); //["s01","Sub1","1"]
            getAttributesFlag = false;
            File sub_data_source_txt_file = null;

            /**应该在这里定义当前sub data source所有不重复的sub semantic models的存储列表（主要是判断negative semantic models） 利用triples**/
            allSaveRegionTriplesForOneSubSemanticModel = new HashSet<String>();// store all sub negative semantic models that needed to save into .txt file
            triplesSetForSubSemanticModels = new HashSet<Set<String>>();//judge this sub negative semantic model should be saved in .txt file or not

            for(File positive_sm_sub_data_source: Objects.requireNonNull(sub_data_source.listFiles())){ // positive_sm_sub_data_source = s01_Sub1_1_Same1.model.json
                // create .txt path and file by the given first s01_Sub1_1_Same1.model.json positive semantic model file
                SemanticModel sm = ModelReader.importSemanticModelFromJsonFile(positive_sm_sub_data_source.getPath(), Params.MODEL_MAIN_FILE_EXT); //read the one of sub positive semantic models for the given sub data source
                assert (sm != null) && (sm.getMappingToSourceColumns().size() == getAttributeNum(sub_data_source_file_info[1])): "invalid semantic model"; //check if the column nodes num equals to the num given by the sub data source file name

//                regionTriplesInfo = getPartitionRegionTriplesStringForOneSemanticModel(sm, partitionModelsPath, true );
                regionTriplesInfo = getPartitionRegionTriplesStringForOneSemanticModel(sm, partitionModelsPath, true ,dataSetName);
                regionTriplesForOneSubSemanticModel = (String) regionTriplesInfo.keySet().toArray()[0]; //obtain the region triples for one sub semantic model ("head1,edge1,tail1;head2,edge2,tail2||head3,edge3,tail3;head4,edge4,tail4;head5,edge5,tail5")
//                allTriplesForOneSubSemanticModel = (Set<String>) regionTriplesInfo.values().toArray()[0]; //obtain all triples for one sub semantic model ("head1,edge1,tail1","head2,edge2,tail2","head3,edge3,tail3","head4,edge4,tail4","head5,edge5,tail5")


                /**write sub positive semantic models info into s01_Sub1_[attr1,attr2,attr3].txt file
                 * if the current sub positive semantic model is the first one, we need to create .txt file and write the corresponding info
                 * else, we need to continue writing corresponding info into .txt file**/
                if(!getAttributesFlag){
                    System.out.println("create a .txt file to save all region triples info for " + sub_data_source.getName() + " success!");
                    Map<String,Integer> columnNodesMap = new HashMap<String,Integer>();//save the column nodes info for obtaining the attributes name in order
                    for(DefaultLink link: sm.getGraph().edgeSet()){
                        if(link.getTarget() instanceof ColumnNode){
                            columnNodesMap.put(((ColumnNode) link.getTarget()).getColumnName(),attribute_index_dict.get(((ColumnNode) link.getTarget()).getColumnName()));//save the column nodes info
                        }
                    }
                    // create dataset path and .txt file
                    sub_data_source_txt_file = new File(subDataSourceTxtPath + "/" + sub_data_source_file_info[0] + "_" + sub_data_source_file_info[1] + "_" + getSubDataSourceTxtName(columnNodesMap) + ".txt");
//                    if(!sub_data_source_txt_file.exists()){
////                        sub_data_source_txt_file.createNewFile();
//                        try{
//                            FileWriter fileWriter = new FileWriter(sub_data_source_txt_file);
//                            //write regionTriplesForOneSubSemanticModel into .txt file
//                            fileWriter.write(regionTriplesForOneSubSemanticModel);
//                            fileWriter.write("\n");
//                            fileWriter.close();
//                        } catch (Exception e) {
//                            e.printStackTrace();
//                        }
//                    }

                    try{
                        FileWriter fileWriter = new FileWriter(sub_data_source_txt_file);
                        //write regionTriplesForOneSubSemanticModel into .txt file
                        fileWriter.write(regionTriplesForOneSubSemanticModel + "||1.0");
                        fileWriter.write("\n");
                        fileWriter.close();
                    } catch (Exception e) {
                        e.printStackTrace();
                    }

                    getAttributesFlag = true;
                }
                else{
                    try{
                        FileWriter fileWriter = new FileWriter(sub_data_source_txt_file,true);
                        //write regionTriplesForOneSubSemanticModel into .txt file
                        fileWriter.write(regionTriplesForOneSubSemanticModel + "||1.0");
                        fileWriter.write("\n");
                        fileWriter.close();
                    } catch (Exception e) {
                        e.printStackTrace();
                    }
                }

                /**write sub negative semantic models info into s01_Sub1_[attr1,attr2,attr3].txt file**/
                File negative_sm_sub_data_source = new File(negativeSMPath + "/" + sub_data_source.getName() + "/" + positive_sm_sub_data_source.getName().split(".model.json")[0]);

                if(Objects.requireNonNull(negative_sm_sub_data_source.listFiles()).length == 0)
                    continue;
                negative_sm_sub_same_index = 0;
                //obtain the corresponding similarity scores for one sub same negative semantic model
                negativeSimScoresList = getSimilarityScoresForOneSubNegativeSemanticModel(negative_sm_sub_data_source.getPath() + "/similarity_scores.txt");
                for(File negative_sm_sub_same: Objects.requireNonNull(negative_sm_sub_data_source.listFiles())){
                    if(negative_sm_sub_same.getName().contains(".txt"))
                        continue;
                    SemanticModel n_sm = ModelReader.importSemanticModelFromJsonFile(negative_sm_sub_same.getPath(), Params.MODEL_MAIN_FILE_EXT); //read the one of sub negative semantic models for the given sub same positive semantic model
                    assert (n_sm != null) && (n_sm.getMappingToSourceColumns().size() == sm.getMappingToSourceColumns().size()): "invalid sub negative semantic model"; //check if the column nodes num equals to the num given by the sub negative semantic model
//                    regionTriplesInfo = getPartitionRegionTriplesStringForOneSemanticModel(n_sm, partitionModelsPath, true );
                    regionTriplesInfo = getPartitionRegionTriplesStringForOneSemanticModel(n_sm, partitionModelsPath, true , dataSetName);

                    regionTriplesForOneSubSemanticModel = (String) regionTriplesInfo.keySet().toArray()[0]; //obtain the region triples for one sub negative semantic model ("head1,edge1,tail1;head2,edge2,tail2||head3,edge3,tail3;head4,edge4,tail4;head5,edge5,tail5")
                    allTriplesForOneSubSemanticModel = (Set<String>) regionTriplesInfo.values().toArray()[0]; //obtain all triples for one sub negative semantic model ("head1,edge1,tail1","head2,edge2,tail2","head3,edge3,tail3","head4,edge4,tail4","head5,edge5,tail5")
                    if(!triplesSetForSubSemanticModels.contains(allTriplesForOneSubSemanticModel)){
                        triplesSetForSubSemanticModels.add(allTriplesForOneSubSemanticModel);
                        regionTriplesForOneSubSemanticModel = regionTriplesForOneSubSemanticModel + "||" + negativeSimScoresList.get(negative_sm_sub_same_index);
                        allSaveRegionTriplesForOneSubSemanticModel.add(regionTriplesForOneSubSemanticModel);
                    }
                    ++negative_sm_sub_same_index;
                }
            }

            if(allSaveRegionTriplesForOneSubSemanticModel.size() > 0) {
                try {
                    FileWriter fileWriter = new FileWriter(sub_data_source_txt_file, true);
                    //write regionTriplesForOneSubSemanticModel into .txt file
                    for (String info : allSaveRegionTriplesForOneSubSemanticModel) {
                        fileWriter.write(info);
                        fileWriter.write("\n");
                    }
                    fileWriter.close();
                } catch (Exception e) {
                    e.printStackTrace();
                }
            }

            System.out.println("sub_data_source:" + sub_data_source.getName() + " finished!");
        }
        System.out.println("subDataSource.size:" + Objects.requireNonNull(subDataSources.listFiles()).length);
    }

    public static void main(String[] args) throws Exception {
        String dataSetName = "EDM";
        String dataSourceName = "s05";
//        String positiveSMPath = "D:/ASM/CRM/positive-models/sub-same-positive-models-json-all/" + dataSourceName;
//        String negativeSMPath = "D:/ASM/CRM/negative-models/sub-same-negative-models-json-all/" + dataSourceName;
//        String subDataSourceTxtPath = "D:/ASM/CRM/DataSet/" + dataSourceName;
//        String partitionModelsPath = "D:/ASM/CRM/partition-models/";

//        String positiveSMPath = "/home/ykyang/XuProgram/Project/GenerateExamples/karma_research_23/ASM/CRM/positive-models/sub-same-positive-models-json-all/" + dataSourceName;
//        String negativeSMPath = "/home/ykyang/XuProgram/Project/GenerateExamples/karma_research_23/ASM/CRM/negative-models/sub-same-negative-models-json-all/" + dataSourceName;
//        String subDataSourceTxtPath = "/home/ykyang/XuProgram/Project/GenerateExamples/karma_research_23/ASM/CRM/DataSet/" + dataSourceName;
//        String partitionModelsPath = "/home/ykyang/XuProgram/Project/GenerateExamples/karma_research_23/ASM/CRM/partition-models/";

//        String positiveSMPath = Params.EDM_ROOT_DIR_2023 + "positive-models/sub-same-positive-models-json-all/" + dataSourceName;
//        String negativeSMPath = Params.EDM_ROOT_DIR_2023 + "negative-models/sub-same-negative-models-json-all/" + dataSourceName;
//        String subDataSourceTxtPath = Params.EDM_ROOT_DIR_2023 + "DataSet/" + dataSourceName;
//        String partitionModelsPath = Params.EDM_ROOT_DIR_2023 + "partition-models/";

        String positiveSMPath = Params.EDM_ROOT_DIR_2023_LINUX + "positive-models/sub-same-positive-models-json-all/" + dataSourceName;
        String negativeSMPath = Params.EDM_ROOT_DIR_2023_LINUX + "negative-models/sub-same-negative-models-json-all/" + dataSourceName;
        String subDataSourceTxtPath = Params.EDM_ROOT_DIR_2023_LINUX + "DataSet/" + dataSourceName;
        String partitionModelsPath = Params.EDM_ROOT_DIR_2023_LINUX + "partition-models/";


        if(!(new File(subDataSourceTxtPath).exists()))
            new File(subDataSourceTxtPath).mkdirs();

        /**read attributes in order from the original data source**/
//        InputStreamReader reader = new InputStreamReader(new FileInputStream("D:/ASM/CRM/sources20230313/"+dataSourceName+".csv"), StandardCharsets.UTF_8);
//        InputStreamReader reader = new InputStreamReader(new FileInputStream("/home/ykyang/XuProgram/Project/GenerateExamples/sources20230313/"+dataSourceName+".csv"), StandardCharsets.UTF_8);
//        InputStreamReader reader = new InputStreamReader(new FileInputStream(Params.EDM_ROOT_DIR_2023 + "sources20230711/"+dataSourceName+".csv"), StandardCharsets.UTF_8);
        InputStreamReader reader = new InputStreamReader(new FileInputStream(Params.EDM_ROOT_DIR_2023_LINUX + "sources20230711/"+dataSourceName+".csv"), StandardCharsets.UTF_8);

        CSVReader csvReader = new CSVReaderBuilder(reader).build();
        List<String[]> list = csvReader.readAll();
        String[] attributes = list.get(0);
        System.out.println("attributes:" + attributes);
        Map<String,Integer> attribute_index_dict = new HashMap<String,Integer>();
        int attribute_index = 0;
        for(String attribute: attributes){
            System.out.println("attribute:" + attribute);
            attribute_index_dict.put(attribute,attribute_index++);
        }

        getDataSetForOneDataSource(positiveSMPath, negativeSMPath, partitionModelsPath, attribute_index_dict, subDataSourceTxtPath, dataSetName);
        System.out.println("run generate triples success!");
    }
}
