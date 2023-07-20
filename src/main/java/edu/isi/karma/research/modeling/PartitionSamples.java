package edu.isi.karma.research.modeling;

import edu.isi.karma.modeling.alignment.GraphUtil;
import edu.isi.karma.modeling.alignment.GraphVizLabelType;
import edu.isi.karma.modeling.alignment.GraphVizUtil;
import edu.isi.karma.modeling.alignment.SemanticModel;
import edu.isi.karma.modeling.alignment.learner.ModelReader;
import edu.isi.karma.modeling.research.Params;
import edu.isi.karma.rep.alignment.*;
import jnr.ffi.annotations.In;
import org.hsqldb.Column;
import org.jgrapht.graph.DirectedWeightedMultigraph;
import org.opengis.util.CodeList;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

import static edu.isi.karma.research.modeling.EliminateNodes.*;
import static edu.isi.karma.research.modeling.FindPaths.findAllPathNode;
import static edu.isi.karma.research.modeling.GenerateSamples.*;
import static edu.isi.karma.research.modeling.SearchForSemanticModels.CreateFile;
import static edu.isi.karma.research.modeling.SearchForSemanticModels.deleteFile;

public class PartitionSamples {
    private static List<SemanticModel> SemanticModels = null;

    /**
     * find ancestor nodes for column node in semantic model
     **/
    public static Set<Node> findAncestorNodes(SemanticModel sm, ColumnNode beSearchedNode) throws Exception {
        //存储integration graph中的所有links
        List<DefaultLink> LinkList = new ArrayList<DefaultLink>(sm.getGraph().edgeSet());
        //存储BeSearchedNode的ancestor nodes
        Set<Node> AncestorNodes = new HashSet<Node>();

        //遍历integration graph中的所有links
        for (DefaultLink link : LinkList) {
            if (link.getTarget().equals(beSearchedNode)) {
                AncestorNodes.add(link.getSource());
            }
        }
        System.out.println("输出" + beSearchedNode.getColumnName() + "的ancestor nodes的个数:" + AncestorNodes.size());
//        if(BeSearchedNode.getId().equals("http://erlangen-crm.org/current/E30_Right1")){
//            for(Node node: AncestorNodes){
//                System.out.println("输出E30_Right1的ancestornode:" + node.getId());
//            }
//        }
        return AncestorNodes;
    }

    public static String getInternalNodeName(String nodeName) {
//        System.out.println("nodeName:" + nodeName);
//        for(String split_name: nodeName.split("_",2)){
//            System.out.println("split_name:" + split_name);
//        }
        return nodeName.split("_", 2)[1];
    }

    public static String getInternalNodeNameEDM(String nodeName) {
        String[] splitStringArray = nodeName.split("/");
        return splitStringArray[splitStringArray.length - 1];
    }

    public static List<String> getSemanticModelRootNameList(SemanticModel sm) {
        List<Node> targetNodes = new ArrayList<Node>();//存储semantic model中所有的target nodes
        Set<String> rootSet = new HashSet<String>();//使用Set存储semantic model中所有的root
        List<String> rootList = new ArrayList<String>();//使用List存储semantic model中所有的root
        //存储semantic model中的target nodes
        for (LabeledLink smlink : sm.getGraph().edgeSet()) {
            targetNodes.add(smlink.getTarget());
        }
        for (Node internalnode : sm.getInternalNodes()) {
            if (!targetNodes.contains(internalnode))
                rootSet.add(internalnode.getId());
        }
        rootList.addAll(rootSet);
        return rootList;
    }

    /**
     * sort descent
     **/
    public static Map SortMap(Map<String, Integer> map) {
        //获取entrySet
        Set<Map.Entry<String, Integer>> mapEntries = map.entrySet();
        //使用链表来对集合进行排序 使用LinkedList 利于传入元素
        List<Map.Entry<String, Integer>> result = new LinkedList<>(mapEntries);
        //自定义比较器来比较链表中的元素
        Collections.sort(result, new Comparator<Map.Entry<String, Integer>>() {
            //基于entry的值（Entry.getValue()），来排序链表
            public int compare(Map.Entry<String, Integer> o1, Map.Entry<String, Integer> o2) {
                return o2.getValue().compareTo(o1.getValue());
            }
        });
        //将排好序的存入到LinkedHashMap(可保持顺序)中，需要存储键和值信息对到新的映射中。
        Map<String, Integer> LinkMap = new LinkedHashMap<>();
        for (Map.Entry<String, Integer> newEntry : result) {
            LinkMap.put(newEntry.getKey(), newEntry.getValue());
        }
        return LinkMap;
    }

    public static Map<String, List<String>> getInternalNodesWithMoreOutgoingLinks(SemanticModel sm) {
        int numOfOutgoingLinks = 0;
        List<String> regionColumnNamesList = new ArrayList<String>();
        Map<String, Integer> outgoingLinksForNode = new HashMap<String, Integer>();
        Map<String, List<String>> regionColumnNames = new HashMap<String, List<String>>();
        List<ColumnNode> columnNodes = new ArrayList<ColumnNode>(sm.getColumnNodes());

        //obtain all nodes with two or more outgoing links
        for (Node inter_node : sm.getInternalNodes()) {
            numOfOutgoingLinks = 0;
            for (DefaultLink link : sm.getGraph().edgeSet()) {
                if (link.getSource().getId().equals(inter_node.getId())) {
                    ++numOfOutgoingLinks;
                }
            }
            if (numOfOutgoingLinks > 1) {
//                regionColumnNodesList = new ArrayList<ColumnNode>();
                regionColumnNamesList = new ArrayList<String>();
                outgoingLinksForNode.put(inter_node.getId(), numOfOutgoingLinks);
                for (ColumnNode column_node : columnNodes) {
                    //check whether there is a path between the internal node and specific column node
                    FindPaths.connectedPathsNode = new ArrayList<List<Node>>();
                    findAllPathNode(new ArrayList<DefaultLink>(sm.getGraph().edgeSet()), inter_node.getId(), column_node.getId(), 100);
                    if (FindPaths.connectedPathsNode.size() > 0) {
//                        regionColumnNodesList.add(column_node);
                        regionColumnNamesList.add(column_node.getColumnName());
                    }
                }
//                regionColumnNodes.put(inter_node.getId(),regionColumnNodesList);
                regionColumnNames.put(inter_node.getId(), regionColumnNamesList);
            }
        }
        return regionColumnNames;
    }

    public static List<SemanticModel> getPartitionRegions(SemanticModel sm, String savePath, Boolean flag) throws Exception {
        String SM_Graphviz_Path = savePath + "partition-models-graphviz";
        String SM_Json_Path = savePath + "partition-models-json";

        String SM_Graphviz_Path_color = savePath + "partition-models-graphviz-color";
        String SM_Json_Path_color = savePath + "partition-models-json-color";

        deleteFile(SM_Graphviz_Path);
        deleteFile(SM_Json_Path);

        deleteFile(SM_Graphviz_Path_color);
        deleteFile(SM_Json_Path_color);

        CreateFile(SM_Graphviz_Path);
        CreateFile(SM_Json_Path);

        CreateFile(SM_Graphviz_Path_color);
        CreateFile(SM_Json_Path_color);

        List<Node> nodeWithMoreOutgoingLinks = new ArrayList<Node>();
        Map<String, Integer> outgoingLinksForNode = new HashMap<String, Integer>();
        List<List<String>> partitionRegionsStr = new ArrayList<List<String>>();
        List<String> regionColumnNamesList = new ArrayList<String>();
        List<ColumnNode> regionColumnNodesList = new ArrayList<ColumnNode>();
        List<SemanticModel> regionSemanticModels = new ArrayList<SemanticModel>();
        SemanticModel regionSemanticModel = null;
        int numOfOutgoingLinks = 0;
        List<List<Node>> allPathsPerColumnNode = new ArrayList<List<Node>>();
        Map<String, List<ColumnNode>> regionColumnNodes = new HashMap<String, List<ColumnNode>>();
        Map<String, List<String>> regionColumnNames = new HashMap<String, List<String>>();
        int regionIndex = 0;
        SemanticModel cloneSM = null;
        List<String> temp_columnNames = new ArrayList<String>();
        List<ColumnNode> columnNodes = new ArrayList<ColumnNode>(sm.getColumnNodes());
        List<String> columnNames = new ArrayList<String>();
        List<Node> rootNodeList = null;
        List<String> rootNameList = new ArrayList<String>();
        Map<String, Integer> regionInterNodeDepth = new HashMap<String, Integer>();
        Map<String, Integer> sortedRegionInterNodeDepth = new HashMap<String, Integer>();
        int shortestPath = 100;
        Map<List<String>, String> columnNamesWithRegionNode = new HashMap<List<String>, String>();

        System.out.println("sm.nodes.size:" + sm.getGraph().vertexSet().size());
        System.out.println("sm.links.size:" + sm.getGraph().edgeSet().size());

        for (ColumnNode column_node : columnNodes) {
            columnNames.add(column_node.getColumnName());
        }

        //obtain all node with two or more outgoing links
        for (Node inter_node : sm.getInternalNodes()) {
            numOfOutgoingLinks = 0;
            for (DefaultLink link : sm.getGraph().edgeSet()) {
                if (link.getSource().getId().equals(inter_node.getId())) {
                    ++numOfOutgoingLinks;
                }
            }
            if (numOfOutgoingLinks > 1) {
//                regionColumnNodesList = new ArrayList<ColumnNode>();
                regionColumnNamesList = new ArrayList<String>();
                outgoingLinksForNode.put(inter_node.getId(), numOfOutgoingLinks);
                for (ColumnNode column_node : columnNodes) {
                    //check whether there is a path between the internal node and specific column node
                    FindPaths.connectedPathsNode = new ArrayList<List<Node>>();
                    findAllPathNode(new ArrayList<DefaultLink>(sm.getGraph().edgeSet()), inter_node.getId(), column_node.getId(), 100);
                    if (FindPaths.connectedPathsNode.size() > 0) {
//                        regionColumnNodesList.add(column_node);
                        regionColumnNamesList.add(column_node.getColumnName());
                    }
                }
//                regionColumnNodes.put(inter_node.getId(),regionColumnNodesList);
                regionColumnNames.put(inter_node.getId(), regionColumnNamesList);
            }
        }

//        System.out.println("outgoingLinksForNode.size:" + outgoingLinksForNode.size());
//        for(String key: outgoingLinksForNode.keySet()){
//            System.out.println("key:" + key + "|num:" + outgoingLinksForNode.get(key));
//        }

        for (String region_node_name : regionColumnNames.keySet()) {
            System.out.println("region_node_name:" + region_node_name + "|" + regionColumnNames.get(region_node_name));
        }

        if (outgoingLinksForNode.keySet().size() == 1) {
            ++regionIndex;
            for (String key : outgoingLinksForNode.keySet()) {
                /**store the generated sub semantic model**/
                try {
                    DirectedWeightedMultigraph smJson = sm.getGraph();
//            GraphUtil.exportJson(smJson, graphNameJson,true,true);
                    GraphVizUtil.exportSemanticModelToGraphviz(sm, GraphVizLabelType.LocalId,
                            GraphVizLabelType.LocalUri, true, true, SM_Graphviz_Path + "/" + "region" + regionIndex + "-" + getInternalNodeName(key) + Params.GRAPHVIS_MAIN_FILE_EXT);
                    GraphVizUtil.exportSemanticModelToGraphvizForPartition(sm, sm.getGraph().vertexSet(), GraphVizLabelType.LocalId,
                            GraphVizLabelType.LocalUri, true, true, SM_Graphviz_Path_color + "/" + "region" + regionIndex + "-" + getInternalNodeName(key) + Params.GRAPHVIS_MAIN_FILE_EXT);
                } catch (Exception e) {
                    e.printStackTrace();
                }
                regionSemanticModels.add(sm);
                System.out.println("one partition region for the semantic model:" + sm.getColumnNodes().size());
            }
        } else {
            /**sort region_inter_node by depth**/
            rootNodeList = getSemanticModelRootList(sm);
            for (Node root_node : rootNodeList) {
                rootNameList.add(root_node.getId());
            }
            for (String inter_node : regionColumnNames.keySet()) {
                if (rootNameList.contains(inter_node)) {
                    System.out.println("root depth equals 1:" + inter_node);
                    regionInterNodeDepth.put(inter_node, 1);
                } else {
//                    allPathsPerColumnNode = new ArrayList<List<Node>>();
                    shortestPath = 100;
                    for (Node root : rootNodeList) {
                        //find all paths from root to delColumnNode
                        System.out.println("root for depth:" + root.getId());
                        FindPaths.connectedPathsNode = new ArrayList<List<Node>>();
                        findAllPathNode(new ArrayList<DefaultLink>(sm.getGraph().edgeSet()), root.getId(), inter_node, 100);
                        if (FindPaths.connectedPathsNode.size() > 0) {
//                            allPathsPerColumnNode.addAll(FindPaths.connectedPathsNode);
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
            System.out.println("sortedRegionInterNodeDepth.size:" + sortedRegionInterNodeDepth.size());

//            for(String key: sortedRegionInterNodeDepth.keySet()){
//                System.out.println("inter_node_depth:" + key + "|" + sortedRegionInterNodeDepth.get(key));
//            }
//            System.out.println("regionColumnNames.size:" + regionColumnNames.size());

            for (String region_node_name : regionColumnNames.keySet()) {
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

//            for(List<String> column_node_list:columnNamesWithRegionNode.keySet()){
//                System.out.println("column_node_list:" + column_node_list + "|region_node:" + columnNamesWithRegionNode.get(column_node_list));
//            }
//            System.out.println("flag:" + flag);

            for (String inter_node : sortedRegionInterNodeDepth.keySet()) {
                if (columnNamesWithRegionNode.values().contains(inter_node)) {
                    System.out.println("inter_node:" + inter_node + "|nodes.num:" + regionColumnNames.get(inter_node));
                    ++regionIndex;
                    temp_columnNames = new ArrayList<String>(columnNames);
                    temp_columnNames.removeAll(regionColumnNames.get(inter_node));
                    cloneSM = sm.clone();
                    regionSemanticModel = getRegionSemanticModels(cloneSM, getInternalNodeName(inter_node), regionIndex, temp_columnNames, SM_Graphviz_Path, SM_Json_Path, flag);
                    regionSemanticModels.add(regionSemanticModel);

                    GraphVizUtil.exportSemanticModelToGraphvizForPartition(sm, regionSemanticModel.getGraph().vertexSet(), GraphVizLabelType.LocalId,
                            GraphVizLabelType.LocalUri, true, true, SM_Graphviz_Path_color + "/" + "region" + regionIndex + "-" + getInternalNodeName(inter_node) + Params.GRAPHVIS_MAIN_FILE_EXT);
                }
            }
        }
        System.out.println("regionSemanticModels.size:" + regionSemanticModels.size());

        return regionSemanticModels;
    }

    public static List<String> getTriplesForOnePartitionRegion(List<SemanticModel> regionSemanticModels, String saveTriplesPath) {
        String headNode, edge, tailNode;
        String triple, regionTriples;
        List<LabeledLink> linkList = new ArrayList<LabeledLink>();
        List<String> triplesForRegionSemanticModels = new ArrayList<String>();
        for (SemanticModel regionSemanticModel : regionSemanticModels) {
            regionTriples = "";
            linkList = new ArrayList<LabeledLink>(regionSemanticModel.getGraph().edgeSet());
            for (int i = 0; i < linkList.size(); i++) {
                triple = null;
                headNode = null;
                edge = null;
                tailNode = null;

                headNode = getLabelName(linkList.get(i).getSource().getId());

                edge = getLabelName(linkList.get(i).getUri());

                if (linkList.get(i).getTarget() instanceof ColumnNode) {
                    tailNode = (((ColumnNode) linkList.get(i).getTarget()).getColumnName());
                } else {
                    tailNode = getLabelName(linkList.get(i).getTarget().getId());
                }

                triple = headNode + "," + edge + "," + tailNode;

                if (i < (linkList.size() - 1)) {
                    regionTriples = regionTriples + triple + ";";
                } else {
                    regionTriples = regionTriples + triple;
                }

            }
            triplesForRegionSemanticModels.add(regionTriples);

        }
        assert triplesForRegionSemanticModels.size() == regionSemanticModels.size() : "triplesForRegionSemanticModels.size != regionSemanticModels.size";

        //save triples to txt
        BufferedWriter bw;
        try {
            bw = new BufferedWriter(new FileWriter(saveTriplesPath));
            for (String triplesForOneRegionSemanticModel : triplesForRegionSemanticModels) {
//                System.out.println("triplesForOneRegionSemanticModels:" + triplesForOneRegionSemanticModel);
                bw.write(triplesForOneRegionSemanticModel);
                bw.newLine();
                bw.flush();
            }
            bw.close();
        } catch (IOException e) {
            e.printStackTrace();
        }

        return null;
    }


//    public static List<List<List<String>>> getTriplesForOnePartitionRegion(List<SemanticModel> regionSemanticModels){
//        List<String> triple = new ArrayList<String>();
//        List<List<String>> triplesForOneRegionSemanticModel = new ArrayList<List<String>>();
//        List<List<List<String>>> triplesForRegionSemanticModels = new ArrayList<List<List<String>>>();
//        for(SemanticModel regionSemanticModel: regionSemanticModels){
//            triplesForOneRegionSemanticModel = new ArrayList<List<String>>();
//            for(DefaultLink link: regionSemanticModel.getGraph().edgeSet()){
//                triple = new ArrayList<String>();
//                triple.add(link.getSource().getId());
//                triple.add(link.getUri());
//                triple.add(link.getTarget().getId());
//                triplesForOneRegionSemanticModel.add(triple);
//            }
//            triplesForRegionSemanticModels.add(triplesForOneRegionSemanticModel);
//            assert triplesForRegionSemanticModels.size() == regionSemanticModel.getGraph().edgeSet().size(): "triplesForRegionSemanticModels.size != regionSemanticModel.getGraph.edgeset.size";
//        }
//        System.out.println("triplesForOneRegionSemanticModel:" + triplesForOneRegionSemanticModel);
//        return null;
//    }

    public static List<SemanticModel> getPartitionRegionsUsingTriple(SemanticModel sm, String savePath, String saveTriplesPath, Boolean flag) throws Exception {
        String SM_Graphviz_Path = savePath + "partition-models-graphviz";
        String SM_Json_Path = savePath + "partition-models-json";

        String SM_Graphviz_Path_color = savePath + "partition-models-graphviz-color";
        String SM_Json_Path_color = savePath + "partition-models-json-color";

        deleteFile(SM_Graphviz_Path);
        deleteFile(SM_Json_Path);

        deleteFile(SM_Graphviz_Path_color);
        deleteFile(SM_Json_Path_color);

        CreateFile(SM_Graphviz_Path);
        CreateFile(SM_Json_Path);

        CreateFile(SM_Graphviz_Path_color);
        CreateFile(SM_Json_Path_color);

        List<Node> nodeWithMoreOutgoingLinks = new ArrayList<Node>();
        Map<String, Integer> outgoingLinksForNode = new HashMap<String, Integer>();
        List<List<String>> partitionRegionsStr = new ArrayList<List<String>>();
        List<String> regionColumnNamesList = new ArrayList<String>();
        List<ColumnNode> regionColumnNodesList = new ArrayList<ColumnNode>();
        List<SemanticModel> regionSemanticModels = new ArrayList<SemanticModel>();
        SemanticModel regionSemanticModel = null;
        int numOfOutgoingLinks = 0;
        List<List<Node>> allPathsPerColumnNode = new ArrayList<List<Node>>();
        Map<String, List<ColumnNode>> regionColumnNodes = new HashMap<String, List<ColumnNode>>();
        Map<String, List<String>> regionColumnNames = new HashMap<String, List<String>>();
        int regionIndex = 0;
        SemanticModel cloneSM = null;
        List<String> temp_columnNames = new ArrayList<String>();
        List<ColumnNode> columnNodes = new ArrayList<ColumnNode>(sm.getColumnNodes());
        List<String> columnNames = new ArrayList<String>();
        List<Node> rootNodeList = null;
        List<String> rootNameList = new ArrayList<String>();
        Map<String, Integer> regionInterNodeDepth = new HashMap<String, Integer>();
        Map<String, Integer> sortedRegionInterNodeDepth = new HashMap<String, Integer>();
        int shortestPath = 100;
        Map<List<String>, String> columnNamesWithRegionNode = new HashMap<List<String>, String>();

        System.out.println("sm.nodes.size:" + sm.getGraph().vertexSet().size());
        System.out.println("sm.links.size:" + sm.getGraph().edgeSet().size());

        for (ColumnNode column_node : columnNodes) {
            columnNames.add(column_node.getColumnName());
        }

        //if there is 1 column node and 2 nodes and 1 edge, there is one partition region
        if (sm.getColumnNodes().size() == 1 && sm.getGraph().vertexSet().size() == 2 && sm.getGraph().edgeSet().size() == 1) {
            InternalNode internalNode = null;
//            SemanticModel reginSemanticModel = sm.clone();
            regionSemanticModels.add(sm);
            for (Node node : sm.getGraph().vertexSet()) {
                if (node instanceof ColumnNode) {
                    continue;
                } else {
                    internalNode = (InternalNode) node;
                    break;
                }
            }

            GraphVizUtil.exportSemanticModelToGraphvizForPartition(sm, sm.getGraph().vertexSet(), GraphVizLabelType.LocalId,
                    GraphVizLabelType.LocalUri, true, true, SM_Graphviz_Path_color + "/" + "region" + "1" + "-" + getInternalNodeName(internalNode.getId()) + Params.GRAPHVIS_MAIN_FILE_EXT);
        } else {
            //obtain all node with two or more outgoing links
            for (Node inter_node : sm.getInternalNodes()) {
                numOfOutgoingLinks = 0;
                for (DefaultLink link : sm.getGraph().edgeSet()) {
                    if (link.getSource().getId().equals(inter_node.getId())) {
                        ++numOfOutgoingLinks;
                    }
                }
                if (numOfOutgoingLinks > 1) {
//                regionColumnNodesList = new ArrayList<ColumnNode>();
                    regionColumnNamesList = new ArrayList<String>();
                    outgoingLinksForNode.put(inter_node.getId(), numOfOutgoingLinks);
                    for (ColumnNode column_node : columnNodes) {
                        //check whether there is a path between the internal node and specific column node
                        FindPaths.connectedPathsNode = new ArrayList<List<Node>>();
                        findAllPathNode(new ArrayList<DefaultLink>(sm.getGraph().edgeSet()), inter_node.getId(), column_node.getId(), 100);
                        if (FindPaths.connectedPathsNode.size() > 0) {
//                        regionColumnNodesList.add(column_node);
                            regionColumnNamesList.add(column_node.getColumnName());
                        }
                    }
//                regionColumnNodes.put(inter_node.getId(),regionColumnNodesList);
                    regionColumnNames.put(inter_node.getId(), regionColumnNamesList);
                }
            }

//        System.out.println("outgoingLinksForNode.size:" + outgoingLinksForNode.size());
//        for(String key: outgoingLinksForNode.keySet()){
//            System.out.println("key:" + key + "|num:" + outgoingLinksForNode.get(key));
//        }

            for (String region_node_name : regionColumnNames.keySet()) {
                System.out.println("region_node_name:" + region_node_name + "|" + regionColumnNames.get(region_node_name));
            }

            if (outgoingLinksForNode.keySet().size() == 1) {
                ++regionIndex;
                for (String key : outgoingLinksForNode.keySet()) {
                    /**store the generated sub semantic model**/
                    try {
                        DirectedWeightedMultigraph smJson = sm.getGraph();
//            GraphUtil.exportJson(smJson, graphNameJson,true,true);
                        GraphVizUtil.exportSemanticModelToGraphviz(sm, GraphVizLabelType.LocalId,
                                GraphVizLabelType.LocalUri, true, true, SM_Graphviz_Path + "/" + "region" + regionIndex + "-" + getInternalNodeName(key) + Params.GRAPHVIS_MAIN_FILE_EXT);
                        GraphVizUtil.exportSemanticModelToGraphvizForPartition(sm, sm.getGraph().vertexSet(), GraphVizLabelType.LocalId,
                                GraphVizLabelType.LocalUri, true, true, SM_Graphviz_Path_color + "/" + "region" + regionIndex + "-" + getInternalNodeName(key) + Params.GRAPHVIS_MAIN_FILE_EXT);
                    } catch (Exception e) {
                        e.printStackTrace();
                    }
                    regionSemanticModels.add(sm);
                    System.out.println("one partition region for the semantic model:" + sm.getColumnNodes().size());
                }
            } else {
                /**sort region_inter_node by depth**/
                rootNodeList = getSemanticModelRootList(sm);
                for (Node root_node : rootNodeList) {
                    rootNameList.add(root_node.getId());
                }
                for (String inter_node : regionColumnNames.keySet()) {
                    if (rootNameList.contains(inter_node)) {
                        System.out.println("root depth equals 1:" + inter_node);
                        regionInterNodeDepth.put(inter_node, 1);
                    } else {
//                    allPathsPerColumnNode = new ArrayList<List<Node>>();
                        shortestPath = 100;
                        for (Node root : rootNodeList) {
                            //find all paths from root to delColumnNode
                            System.out.println("root for depth:" + root.getId());
                            FindPaths.connectedPathsNode = new ArrayList<List<Node>>();
                            findAllPathNode(new ArrayList<DefaultLink>(sm.getGraph().edgeSet()), root.getId(), inter_node, 100);
                            if (FindPaths.connectedPathsNode.size() > 0) {
//                            allPathsPerColumnNode.addAll(FindPaths.connectedPathsNode);
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
                System.out.println("sortedRegionInterNodeDepth.size:" + sortedRegionInterNodeDepth.size());

//            for(String key: sortedRegionInterNodeDepth.keySet()){
//                System.out.println("inter_node_depth:" + key + "|" + sortedRegionInterNodeDepth.get(key));
//            }
//            System.out.println("regionColumnNames.size:" + regionColumnNames.size());

                for (String region_node_name : regionColumnNames.keySet()) {
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

//            for(List<String> column_node_list:columnNamesWithRegionNode.keySet()){
//                System.out.println("column_node_list:" + column_node_list + "|region_node:" + columnNamesWithRegionNode.get(column_node_list));
//            }
//            System.out.println("flag:" + flag);

                for (String inter_node : sortedRegionInterNodeDepth.keySet()) {
                    if (columnNamesWithRegionNode.values().contains(inter_node)) {
                        System.out.println("inter_node:" + inter_node + "|nodes.num:" + regionColumnNames.get(inter_node));
                        ++regionIndex;
                        temp_columnNames = new ArrayList<String>(columnNames);
                        temp_columnNames.removeAll(regionColumnNames.get(inter_node));
                        cloneSM = sm.clone();
                        regionSemanticModel = getRegionSemanticModels(cloneSM, getInternalNodeName(inter_node), regionIndex, temp_columnNames, SM_Graphviz_Path, SM_Json_Path, flag);
                        regionSemanticModels.add(regionSemanticModel);

                        GraphVizUtil.exportSemanticModelToGraphvizForPartition(sm, regionSemanticModel.getGraph().vertexSet(), GraphVizLabelType.LocalId,
                                GraphVizLabelType.LocalUri, true, true, SM_Graphviz_Path_color + "/" + "region" + regionIndex + "-" + getInternalNodeName(inter_node) + Params.GRAPHVIS_MAIN_FILE_EXT);
                    }
                }
            }
        }
        getTriplesForOnePartitionRegion(regionSemanticModels, saveTriplesPath);
        System.out.println("regionSemanticModels.size:" + regionSemanticModels.size());

        return regionSemanticModels;
    }

    public static String getLabelName(String httpLabel) {
        String[] splitName = new String[]{};
        if (httpLabel.contains("#")) {
            splitName = httpLabel.split("#");
        } else {
            splitName = httpLabel.split("/");
        }
//        System.out.println("splitName.size:" + splitName.length);
//        for(String name: splitName){
//            System.out.println("name:" + name);
//        }
        List<String> nameList = Arrays.asList(splitName);
        String labelName = nameList.get(nameList.size() - 1);
        return labelName;
    }

    public static void main(String[] args) throws Exception {

        /**get partition regions**/
//        List<String> unique_columns = new ArrayList<String>();
//        Boolean flag = true;
//        List<SemanticModel> PositiveSamples = new ArrayList<SemanticModel>();
//
//        String SemanticMoldes_Path = "D:\\ASM\\CRM\\";
//        int sourceIndex = 5;
//        String sourcePath = "D:\\ASM\\CRM\\sources20230313\\";
//
//        if (SemanticModels == null){
//            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(SemanticMoldes_Path + "models-json-20230313", Params.MODEL_MAIN_FILE_EXT);
//        }
//
//        /**generate samples**/
////        if(sourceIndex < 9) {
////            sourcePath = sourcePath + "s0" + String.valueOf(++sourceIndex) + ".csv";
////        }
////        else{
////            sourcePath = sourcePath + "s" + String.valueOf(++sourceIndex) + ".csv";
////        }
////
////
////        if(flag){
////            PositiveSamples = getAllPositiveSemanticModels(SemanticModels.get(--sourceIndex),--sourceIndex,unique_columns,SemanticMoldes_Path + "positive-models/");
////        }
////        else{
////            unique_columns = getMainColumnNames(sourcePath);
////            PositiveSamples = getPositiveSemanticModels(SemanticModels.get(--sourceIndex),--sourceIndex,unique_columns,SemanticMoldes_Path + "positive-models/");
////        }
//        /**generate samples**/
//
////        GraphVizUtil.exportSemanticModelToGraphviz(SemanticModels.get(sourceIndex), GraphVizLabelType.LocalId,
////                GraphVizLabelType.LocalUri, true, true, "D:\\ASM\\CRM\\partition-models\\partition-models-graphviz" + "/" + "region-" + Params.GRAPHVIS_MAIN_FILE_EXT);
//
////        DirectedWeightedMultigraph smJson = SemanticModels.get(sourceIndex).getGraph();
////            GraphUtil.exportJson(smJson, "D:\\ASM\\CRM\\json-saver-test\\"+SemanticModels.get(sourceIndex).getName() + Params.MODEL_MAIN_FILE_EXT,true,true);
//
//        /**partition samples**/
//        // test for original sm
//        getPartitionRegions(SemanticModels.get(28),"D:\\ASM\\CRM\\partition-models\\",true);
//
////        // test for sub-positive sm
////        getPartitionRegions(PositiveSamples.get(1),"D:\\ASM\\CRM\\partition-models\\",true);
//
////        // test for ["Image","AquisitionDate","Owner"]
////        SemanticModel sm = SemanticModels.get(5);
////        List<String> subset = new ArrayList<String>(Arrays.asList("Image","AquisitionDate","Owner"));
////        System.out.println("subset:" + subset);
////        List<String> temp_columnNames = new ArrayList<String>();
////        List<String> columnNames = new ArrayList<String>();
////        SemanticModel cloneSM, positiveSemanticModel = null;
////
////        for(ColumnNode column_node: sm.getColumnNodes()) {
////            columnNames.add(column_node.getColumnName());
////        }
////
////        temp_columnNames = new ArrayList<String>(columnNames);
////        temp_columnNames.removeAll(subset);
////        System.out.println("temp_columnNames:" + temp_columnNames);
////        cloneSM = sm.clone();
////        positiveSemanticModel = getSubSemanticModels(cloneSM, 1, temp_columnNames, SemanticMoldes_Path + "positive-models/" + "positive-models-graphviz-test/" + sm.getName(), SemanticMoldes_Path + "positive-models/" + "positive-models-json-test/" + sm.getName());
////
////        getPartitionRegions(positiveSemanticModel,"D:\\ASM\\CRM\\partition-models\\",true);
        /**get partition regions**/


        /**get partition region list whose elements are triple list added on 2023/05/29**/
        String dataSource = "s01";
        String subDataSource = "s01_Sub3_6";
        String sameSubDataSource = "s01_Sub3_6_Same2";
        String saveTriplesPath = "D:/ASM/CRM/partition-models/partition-models-triples/sub-same-positive-models/" + dataSource + "/" + subDataSource + "/";
//        String saveTriplesPath = "D:/ASM/CRM/partition-models/partition-models-triples/sub-same-negative-models/" + dataSource + "/" + subDataSource + "/" + sameSubDataSource + "/";
        File Path = new File(saveTriplesPath);
        if (!Path.exists()) {
            Path.mkdirs();
        }
        String saveTriplesFile = saveTriplesPath + sameSubDataSource + ".txt";
//        String saveTriplesFile = saveTriplesPath + sameSubDataSource + "_negative32.txt";

//        SemanticModel sm = ModelReader.importSemanticModelFromJsonFile("D:/ASM/CRM/positive-models/sub-same-positive-models-json-all/s01/s01_Sub7_1/s01_Sub7_1_Same1.model.json",Params.MODEL_MAIN_FILE_EXT);
//        SemanticModel sm = ModelReader.importSemanticModelFromJsonFile("D:/ASM/CRM/positive-models/sub-same-positive-models-json-all/s01/s01_Sub2_1/s01_Sub2_1_Same1.model.json",Params.MODEL_MAIN_FILE_EXT);
        SemanticModel sm = ModelReader.importSemanticModelFromJsonFile("D:/ASM/CRM/positive-models/sub-same-positive-models-json-all/" + dataSource + "/" + subDataSource + "/" + sameSubDataSource + ".model.json", Params.MODEL_MAIN_FILE_EXT);
//        SemanticModel sm = ModelReader.importSemanticModelFromJsonFile("D:/ASM/CRM/negative-models/sub-same-negative-models-json-all/" + dataSource + "/" + subDataSource + "/" + sameSubDataSource + "/" + sameSubDataSource + "_negative32.model.json",Params.MODEL_MAIN_FILE_EXT);

        getPartitionRegionsUsingTriple(sm, "D:/ASM/CRM/partition-models/", saveTriplesFile, true);

        /**test for get label name for a node and edge**/
////        String httpLabel = "http://erlangen-crm.org/current/E21_Person1";
//        String httpLabel = "http://erlangen-crm.org/current/P98i_was_born";
//        String labelName = getLabelName(httpLabel);
//        System.out.println("labelName:" + labelName);
    }
}
