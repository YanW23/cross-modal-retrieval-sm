package edu.isi.karma.research.modeling;

import edu.isi.karma.config.ModelingConfiguration;
import edu.isi.karma.config.ModelingConfigurationRegistry;
import edu.isi.karma.modeling.alignment.*;
import edu.isi.karma.modeling.alignment.learner.*;
import edu.isi.karma.modeling.ontology.OntologyManager;
import edu.isi.karma.modeling.research.Params;
import edu.isi.karma.modeling.steiner.topk.SteinerNode;
import edu.isi.karma.rep.alignment.*;
import edu.isi.karma.rep.alignment.SemanticType.Origin;
import edu.isi.karma.util.RandomGUID;
import edu.isi.karma.webserver.ContextParametersRegistry;
import edu.isi.karma.webserver.ServletContextParameterMap;
import org.apache.hadoop.util.hash.Hash;
import org.apache.poi.util.SystemOutLogger;
import org.jgrapht.graph.AsUndirectedGraph;
import org.jgrapht.graph.DirectedWeightedMultigraph;
import org.jgrapht.graph.WeightedMultigraph;
import org.python.core.PyFunction;
import org.python.core.PyInteger;
import org.python.core.PyList;
import org.python.google.common.collect.Lists;
import org.python.util.PythonInterpreter;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.text.DecimalFormat;
import java.util.*;

import static edu.isi.karma.research.modeling.SearchForSemanticModels.findAllPathNode;

public class EliminateNodes {
    private static Logger logger = LoggerFactory.getLogger(EliminateNodes.class);
    private static OntologyManager ontologyManager = null;
    private static List<SemanticModel> semanticModels = null;
    private static List<SemanticModel> SemanticModels = null;
    private static SemanticModel newsemanticmodel = null;
    private static List<List<Node>> connectedPathsNode;//存储路径上的节点
    private static List<Node> nowPathNode = new ArrayList<Node>();
    private static Map<Node,Integer> NodeOutgoingLinksNum = new HashMap<Node,Integer>();
    private static Boolean IsDelFlag = true;

    /**获取node的semantic types**/
    private static List<SemanticType> getCandidateSteinerSets(ColumnNode steinerNode, boolean useCorrectTypes, int numberOfCandidates) {

        if (steinerNode == null)
            return null;

        List<SemanticType> candidateSemanticTypes = null;

        if (!useCorrectTypes) {
            candidateSemanticTypes = steinerNode.getTopKLearnedSemanticTypes(numberOfCandidates);//获得斯坦纳树节点的前numberOfCandidates个候选语义模型
            if(candidateSemanticTypes.size() == 0){
                candidateSemanticTypes = steinerNode.getUserSemanticTypes();
            }
        } else if (steinerNode.getSemanticTypeStatus() == ColumnSemanticTypeStatus.UserAssigned) {
            candidateSemanticTypes = steinerNode.getUserSemanticTypes();
        }

        if (candidateSemanticTypes == null) {
            logger.error("No candidate semantic type found for the column " + steinerNode.getColumnName());
            return null;
        }

        return candidateSemanticTypes;
    }

    /**5.18 获取semantic model中所有的root节点**/
    private static List<Node> getSemanticModelRootList(SemanticModel sm){
        List<Node> SMTargetNodes = new ArrayList<Node>();//存储semantic model中所有的target nodes
        Set<Node> RootSet = new HashSet<Node>();//使用Set存储semantic model中所有的root
        List<Node> RootList = new ArrayList<>();//使用List存储semantic model中所有的root
        //存储semantic model中的target nodes
        for(LabeledLink smlink: sm.getGraph().edgeSet()){
            SMTargetNodes.add(smlink.getTarget());
        }
        for(Node internalnode: sm.getInternalNodes()){
            if(!SMTargetNodes.contains(internalnode))
                RootSet.add(internalnode);
        }
        RootList.addAll(RootSet);
        return RootList;
    }

    /**获取semantic model中的root节点**/
    private static Node getSemanticModelRoot(SemanticModel sm){
        List<Node> SMTargetNodes = new ArrayList<Node>();//存储semantic model中所有的target nodes
        Node Root = null;//存储semantic model中所有的root
        //存储semantic model中的target nodes
        for(LabeledLink smlink: sm.getGraph().edgeSet()){
            SMTargetNodes.add(smlink.getTarget());
        }
        for(Node internalnode: sm.getInternalNodes()){
            if(!SMTargetNodes.contains(internalnode))
                Root = internalnode;
        }
        return Root;
    }

    /**存储Node信息的findAllPathNode函数**/
    public static void findAllPathNode(List<DefaultLink> LinkList,String source,String target,int length){
        for(Node node: nowPathNode){
            if(node.getId().equals(source)){
                nowPathNode.remove(nowPathNode.size()-1);//返回上一个node
                return;
            }
        }

        //遍历图中的所有link
        for(int i=0;i<LinkList.size();i++) {
            DefaultLink link = LinkList.get(i);
            if (link.getSource().getId().equals(source)) {//如果此边的source为要查找路径的起始source
                nowPathNode.add(link.getSource());
                if(nowPathNode.size() >= length){
                    nowPathNode.remove(nowPathNode.size()-1);
                    continue;
                }
                if(link.getTarget().getId().equals(target)){//如果此边的target为要查找路径的最终target
                    nowPathNode.add(link.getTarget());
                    nowPathNode.toArray();
                    connectedPathsNode.add(Arrays.asList(Arrays.copyOf(nowPathNode.toArray(), nowPathNode.toArray().length, Node[].class)));

                    System.out.println("输出路径：" + nowPathNode);

                    /**因为添加了终点路径，所以要返回两次**/
                    nowPathNode.remove(nowPathNode.size() - 1);
                    nowPathNode.remove(nowPathNode.size() - 1);
                    /**已经找到路径，返回上层找其他路径**/
                    continue;
                }
                findAllPathNode(LinkList, link.getTarget().getId(), target, length);
            }
        }
        /**如果找不到下个节点，返回上层**/
        if(nowPathNode.size()>0){
            nowPathNode.remove(nowPathNode.size()-1);
        }
    }


    /**删除预测阶段不正确的nodes  获取new source sematic model**/
    public static SemanticModel GenerateNewSM(int SourceIndex) throws Exception{

        SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);

        SemanticModel Source = SemanticModels.get(SourceIndex);

        /**保存语义模型图的路径**/
        String graphPath = Params.Generate_New_SM;
        String graphPathJson = Params.Generate_New_SM;
        /**生成train graph文件名**/
        String graphName = graphPath + SemanticModels.get(SourceIndex).getName() + ".new" + Params.GRAPH_JSON_FILE_EXT;
        String graphNameJson = graphPathJson + SemanticModels.get(SourceIndex).getName() + ".new" + Params.GRAPH_JSON_FILE_EXT;


        logger.info("======================================================");
        logger.info(Source.getName() + "(#attributes:" + Source.getColumnNodes().size() + ")");//获取语义模型的数据节点数目
        System.out.println(Source.getName() + "(#attributes:" + Source.getColumnNodes().size() + ")");
        logger.info("======================================================");

        //将语义模型的数据节点存储到列表中
        List<ColumnNode> columnNodes = Source.getColumnNodes();
        //存储正确的语义类型和得分最高的候选语义类型
        SemanticType correctSemanticType,topcandidateSemanticType;
        //存储能否正确预测语义类型的结果
        List<Boolean> label_true_or_false = new LinkedList<Boolean>();
        //存储要删除的节点（在语义标注阶段不能被正确预测的节点）
        /**打印每次要删除的节点列表**/
        Set<DefaultLink> dellabeledges = new HashSet<DefaultLink>();//定义要删除的边列表集合
//        List<Node> dellabelcolumnnodes = new LinkedList<Node>();//////////////////////////////////////
        Set<Node> dellabelcolumnnodes = new HashSet<Node>();
        Set<String> dellabelcolumnnodesName = new HashSet<String>();
        Boolean true_false = false;
        Node Root = null;


        /**获取当前semantic model的root节点**/
        Root = getSemanticModelRoot(Source);
        System.out.println("Root.id:" + Root.getId());
//        for(Node root: RootSet){
//            System.out.println("Root.list:" + root.getId());
//        }

        /**获取当前semantic model的links**/
        List<DefaultLink> SMLinkList = new ArrayList<DefaultLink>();
        for(DefaultLink link: Source.getGraph().edgeSet()){
            SMLinkList.add(link);
        }

        /**存储当前semantic model的node及其Outgoing links的数量**/
        //遍历semantic model中的所有node
        for(Node node: Source.getInternalNodes()){
            int num = 0;
            for(DefaultLink link: Source.getGraph().edgeSet()){
                if(link.getSource().equals(node))
                    num++;
            }
            NodeOutgoingLinksNum.put(node,num);
        }
//        for(Node node: NodeOutgoingLinksNum.keySet()){
//            System.out.println("NodeOutgoingLinksNum:" + node.getId()+"||"+NodeOutgoingLinksNum.get(node));
//        }



        /**找出在semantic labeling阶段没有被正确预测semantic type的columnnodes**/
        for(ColumnNode i: columnNodes){
            System.out.println("ColumnName:"+i.getColumnName());
            List<SemanticType> correctSemanticTypes = getCandidateSteinerSets(i, true, 2);
            List<SemanticType> candidateSemanticTypes = getCandidateSteinerSets(i, false,1);

            correctSemanticType = correctSemanticTypes.get(0);
            topcandidateSemanticType = candidateSemanticTypes.get(0);


            if((!(correctSemanticType.getDomain()).equals(topcandidateSemanticType.getDomain()))||(!(correctSemanticType.getType()).equals(topcandidateSemanticType.getType()))){
                dellabelcolumnnodes.add(i);
                dellabelcolumnnodesName.add(i.getColumnName());
            }
            label_true_or_false.add((correctSemanticType.getDomain()).equals(topcandidateSemanticType.getDomain()));

        }

//        for(int i=0;i<label_true_or_false.size();i++) {
//            System.out.println("label_true_or_false:" + label_true_or_false.get(i));
//        }


        /**2022.5.7**/
//        for(Node i: dellabelcolumnnodes){
//            System.out.println(i.getId());
//            //找到Root到i的path
//            connectedPathsNode = new ArrayList<List<Node>>();
//            findAllPathNode(SMLinkList,Root.getId(),i.getId(),100);
//            System.out.println("connectedPathsNode:"+connectedPathsNode);//保存root到待删除节点之间的节点
//            //遍历每一条路径
//            for(List<Node> pathnodes: connectedPathsNode){
//                System.out.println("pathnodes:"+pathnodes);
//                for(int k=0;k<pathnodes.size()-1;k++){
//                    System.out.println("pathnode:"+pathnodes.get(k).getId());
//                    int node_num;
//                    if(NodeOutgoingLinksNum.keySet().contains(pathnodes.get(k))){
//                        node_num =  NodeOutgoingLinksNum.get(pathnodes.get(k))-1;
//                        NodeOutgoingLinksNum.put(pathnodes.get(k),node_num);
//                    }
//                }
//            }
//        }
        System.out.println("dellabelcolumnnodesName:" + dellabelcolumnnodesName);
//        for(Node node: NodeOutgoingLinksNum.keySet()){
//            System.out.println("NodeOutgoingLinksNum:" + node.getId()+"||"+NodeOutgoingLinksNum.get(node));
//            if(NodeOutgoingLinksNum.get(node) == 0){
//                dellabelcolumnnodes.add(node);
//                dellabelcolumnnodesName.add(node.getId());
//            }
//        }
//        System.out.println("dellabelcolumnnodesName1:" + dellabelcolumnnodesName);


        /**2020.5.7**/
//        for(Node node: dellabelcolumnnodes){
//            System.out.println("打印要删除的节点:" + node);
//            for(DefaultLink link: Source.getGraph().edgeSet()){
//
//                if(link.getTarget().equals(node)){
//                    System.out.println("打印要删除的边"+link.getTarget());
////                  needEliminateSource.getGraph().removeEdge(link);
//                    dellabeledges.add(link);
//                }
////            else{
////                System.out.println("false");
////            }
//            }
//        }

        System.out.println("未删除节点前的边数目："+Source.getGraph().edgeSet().size());
        System.out.println("未删除节点前的节点数目："+Source.getGraph().vertexSet().size());
        System.out.println("未删除节点前的columnnode数目："+Source.getColumnNodes().size());

        Source = NewEliminatedSemanticModels(Source,0,0,dellabelcolumnnodesName,graphName,graphNameJson);///////5.18开


//        /**删除节点**/
//        for(Node needeliminationNodes: dellabelcolumnnodes) {
//            Source.getGraph().removeVertex(needeliminationNodes);
//        }
//        /**删除边**/
//        for(DefaultLink link: dellabeledges){
//            if(link instanceof LabeledLink) {
////                System.out.println(link);
//                Source.getGraph().removeEdge((LabeledLink) link);
//            }
//        }

        System.out.println("删除节点后的边数目："+Source.getGraph().edgeSet().size());
        System.out.println("删除节点后的节点数目："+Source.getGraph().vertexSet().size());
        System.out.println("删除节点后的columnnode数目："+Source.getColumnNodes().size());

//        /**保存语义模型图的路径**/
//        String graphPath = Params.Generate_New_SM;
//        String graphPathJson = Params.Generate_New_SM;
//        /**生成train graph文件名**/
//        String graphName = graphPath + SemanticModels.get(SourceIndex).getName() + ".new" + Params.GRAPH_JSON_FILE_EXT;
//        String graphNameJson = graphPathJson + SemanticModels.get(SourceIndex).getName() + ".new" + Params.GRAPH_JSON_FILE_EXT;

//        /**保存语义模型**/
//        try {
//////                GraphUtil.exportJson(modelLearningGraph.getGraphBuilder().getGraph(), graphName + ".json",true,true);
////            GraphUtil.exportJson(needEliminateSource.getGraph(), graphName + ".json",true,true);
////            /**Visualize the merged graph (model learning graph). 18 June 2018.**/
////            for (Node node : modelLearner.graphBuilder.getGraph().vertexSet()) {
////                System.out.println(node);
////            }
////
////
//            GraphVizUtil.exportSemanticModelToGraphviz(Source,GraphVizLabelType.LocalId,
//                    GraphVizLabelType.LocalUri,true,true,graphName + ".dot");
//
//        } catch (Exception e) {
//            e.printStackTrace();
//        }

        return Source;
    }

    /**原始semantic model生成初始search states**/
    public static List<SemanticModel> getStartStatesSemanticModel(int newSourceIndex) throws Exception {
        semanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json", Params.MODEL_MAIN_FILE_EXT);

        SemanticModel newSource = semanticModels.get(newSourceIndex);

        logger.info("======================================================");
        logger.info(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");//获取新源的数据节点
        System.out.println(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");
        logger.info("======================================================");

        //将新源语义模型的数据节点存储到列表中
        List<ColumnNode> columnNodes = newSource.getColumnNodes();
        //存储能否正确预测语义类型的结果
        List<Boolean> a = new LinkedList<Boolean>();
        //存储要删除的节点（在语义标注阶段不能被正确预测的节点）
        List<ColumnNode> dellabelcolumnnodes = new LinkedList<ColumnNode>();

        Boolean true_false = false;

        for(ColumnNode i: columnNodes){
            System.out.println(i.getColumnName());
            List<SemanticType> correctSemanticTypes = getCandidateSteinerSets(i, true, 2);
            List<SemanticType> candidateSemanticTypes = getCandidateSteinerSets(i, false,1);
            for(SemanticType j: correctSemanticTypes) {
                System.out.println(j.getDomain());
//                System.out.println(j.getConfidenceScore());
                for(SemanticType k: candidateSemanticTypes){
                    System.out.println(k.getDomain());
                    if((!(j.getDomain()).equals(k.getDomain()))||(!(j.getType()).equals(k.getType()))){
                        dellabelcolumnnodes.add(i);
                    }
//                    System.out.println((j.getDomain()).equals(o.getDomain()));

                    a.add((j.getDomain()).equals(k.getDomain()));
                }
            }
        }

        for(int i=0;i<a.size();i++) {
            System.out.println(a.get(i));
        }

        for(int i=0;i<dellabelcolumnnodes.size();i++){
            System.out.println((dellabelcolumnnodes.get(i)).getColumnName());
        }

        SemanticModel SMnew = semanticModels.get(0);
        //存储新语义模型的数据节点
        List<ColumnNode> newcolumnNodes = SMnew.getColumnNodes();
        String semantictype = null;
        String possiblesemantictype=null;

        //存储新语义模型数据节点的正确语义类型
        HashMap<String,String> correctsemantictyes= new HashMap<String,String>();
        //存储要删除的节点列表
        List<List> delcolumnnodeslist = new LinkedList<List>();

        Set<String> DelcolumnnodesList = new HashSet<String>();

        List<Set> DELcolumnnodesList = new LinkedList<Set>();

        Set<Set<String>> DelColumnnodesList = new HashSet<Set<String>>();
        Set<Set<String>> FinalDelColumnnodesList = new HashSet<Set<String>>();

        List<Set<Set<String>>> DelColumnNodesList = new LinkedList<Set<Set<String>>>();

        System.out.println("新语义模型数据节点正确的语义类型,以hashmap数据结构进行存储;key:数据节点名,value:语义类型");
        for(ColumnNode n: newcolumnNodes){
//            System.out.println(n.getColumnName());
            List<SemanticType> correctSemanticTypes = getCandidateSteinerSets(n, true, 2);
            for(SemanticType j: correctSemanticTypes){
                semantictype = ((j.getDomain()).toString())+";"+((j.getType()).toString());
            }
            correctsemantictyes.put(n.getColumnName(),semantictype);
        }
        for (String i : correctsemantictyes.keySet()) {
                System.out.println("key: " + i + " value: " + correctsemantictyes.get(i));
        }

//        System.out.println(correctsemantictyes);
        System.out.println("输出每个数据节点4种可能语义类型");
        for(ColumnNode o: newcolumnNodes){
//            DelcolumnnodesList.add(o.getColumnName());
            DelColumnnodesList = new HashSet<Set<String>>();
            FinalDelColumnnodesList = new HashSet<Set<String>>();
//            DelcolumnnodesList = new HashSet<String>(Arrays.asList(o.getColumnName()));
            List<SemanticType> possibleSemanticTypes = getCandidateSteinerSets(o, false, 4);
            System.out.println(o.getColumnName());//输出遍历到的数据节点名
            for(SemanticType p: possibleSemanticTypes){
                possiblesemantictype=((p.getDomain()).toString())+";"+((p.getType()).toString());
                System.out.println("输出数据节点的候选语义类型："+possiblesemantictype);//输出数据节点的候选语义类型
//                System.out.println("下面是要删除的节点");
                for (String i : correctsemantictyes.keySet()) {
                    DelcolumnnodesList=new HashSet<String>();
                    if((correctsemantictyes.get(i)).equals(possiblesemantictype)){
                        DelcolumnnodesList.add(o.getColumnName());
                        DelcolumnnodesList.add(i);
                        DelColumnnodesList.add(DelcolumnnodesList);
//                        System.out.println(i);
                    }

//                    System.out.println("key: " + i + " value: " + correctsemantictyes.get(i));
                }
            }
            if(DelColumnnodesList.size()>1){
                for(Set<String> columnnodesList: DelColumnnodesList){
                    if(columnnodesList.size()>1){
                        FinalDelColumnnodesList.add(columnnodesList);
//                        System.out.println("true");
                    }
//                    else{
//                        System.out.println("false");
//                    }
                }
            }
            else{
                FinalDelColumnnodesList=DelColumnnodesList;
            }

            System.out.println("DelColumnnodesList:"+DelColumnnodesList);
            System.out.println("FinalDelColumnnodesList"+FinalDelColumnnodesList);

            DelColumnNodesList.add(FinalDelColumnnodesList);
            System.out.println("一轮结束");
        }

        System.out.println("最后的列表："+DelColumnNodesList);

        /**遍历存储删除数据节点列表的列表**/
        System.out.println("遍历存储删除数据节点列表的列表：");
        int Index=0;
        int Count=0;
        int count=0;
        for(Set<Set<String>> hashSet_hashSet: DelColumnNodesList){
            Index++;
            System.out.println("hashSet_hashSet:"+hashSet_hashSet);
            Count=0;
            for(Set<String> hashSet: hashSet_hashSet){
                Count++;
                System.out.println("hashSet_"+Index+hashSet);
                /**删除节点和边操作**/
                EliminatedSemanticModels(newSourceIndex,Index,Count,hashSet);
            }
        }

//        for(int i=0;i<DELcolumnnodesList.size();i++){
//            count++;
//            System.out.println(DELcolumnnodesList.get(i));
//            /**删除节点和边操作**/
////            EliminatedSemanticModels(newSourceIndex,count,DELcolumnnodesList.get(i));
//        }

//        List<ColumnNode> clumnnodes = new LinkedList<ColumnNode>();
//        for (Node n : steinerNodes) {
//            if (n instanceof ColumnNode) {
//                ColumnNode steinerNode = (ColumnNode)n;
//        for(ColumnNode n : columnNodes)
//        List<SemanticType> candidateSemanticTypes = getCandidateSteinerSets(steinerNode, useCorrectTypes, numberOfCandidates);
//                addSteinerNodeToTheGraph(steinerNode, candidateSemanticTypes);
//            }
//        }

        return null;
    }

    /**判断一个Set<Set<String>> a 中是否包含 Set<String> b**/
    public static Boolean Judge(Set<Set<String>> A, Set<String> B){

        for(Set<String> set: A){
            Set<String> newset = new HashSet<String>();
            newset.addAll(set);
            newset.retainAll(B);
            if(newset.size()==set.size()){
                return true;
            }
        }

        return false;
    }

    /**6.24 给定SemanticModel 通过删除操作获得其正确的SubSemanticModels**/
    public static SemanticModel NewEliminatedSemanticModelsForSubSM(SemanticModel sm, int Index,Set<String> DELcolumnnodes, String graphPath, String graphPathJson) throws Exception {

        /**先读进语义模型**/
        SemanticModel needEliminateSource = sm;
        /**生成train graph文件名**/
        String graphName = graphPath + "/" + "Sub" + Index + Params.GRAPHVIS_MAIN_FILE_EXT;
        String graphNameJson = graphPathJson + "/" + "Sub" + Index + Params.MODEL_MAIN_FILE_EXT;

        logger.info("======================================================");
        logger.info(needEliminateSource.getName() + "(#attributes:" + needEliminateSource.getColumnNodes().size() + ")");//获取新源的数据节点
        System.out.println(needEliminateSource.getName() + "(#attributes:" + needEliminateSource.getColumnNodes().size() + ")");
        System.out.println(needEliminateSource.getName() + "(#links:" + needEliminateSource.getGraph().edgeSet().size() + ")");
        logger.info("======================================================");


        List<ColumnNode> steinerNodes = new ArrayList<>(needEliminateSource.getColumnNodes());
        for(ColumnNode i: steinerNodes){
            System.out.println("打印删除nodes前的SMnodes.name:"+i.getColumnName());
        }
        /**定义每次要删除的link列表和node列表**/
        Set<Node> eliminationColumnNodes = new HashSet<Node>();//存储语义模型中要删除的columnnodes
        Set<DefaultLink> eliminationEdges = null;//定义要删除的边列表集合
        Set<Node> eliminationNodes = null;//针对每个待删除的columnnode 存储其所有需要删除的nodes
        for(ColumnNode i: steinerNodes){
            for(String columnnodename: DELcolumnnodes){
                if(i.getColumnName().equals(columnnodename)){
                    eliminationColumnNodes.add(i);
                }
            }
        }


        for(Node i: eliminationColumnNodes){
            System.out.println("打印要删除的nodes.id:"+i.getId());
        }

        List<Node> RootList = null;


        /**5.18**/
        int loopnum = eliminationColumnNodes.size();
        Node ColumnNodeNeededDelete = null;
        while(eliminationColumnNodes.size()>0){
            /**获取当前semantic model的所有root节点**/
            RootList = getSemanticModelRootList(needEliminateSource);
            for(Node root: RootList) {
                System.out.println("Rootlist:" + root.getId());
            }
            /**将当前semantic model中的links保存到List<DefaultLink>中**/
            List<DefaultLink> LinkList = new ArrayList<DefaultLink>();
            LinkList.addAll(needEliminateSource.getGraph().edgeSet());
            /**获取当前semantic model的internal及其outgoinglinks数量**/
            Map<Node,Integer> NodeOutgoingLinksNum1 = new HashMap<Node,Integer>();
            /**初始化eliminationEdges及eliminationNodes**/
            eliminationEdges = new HashSet<DefaultLink>();//每次循环要删除的links
            eliminationNodes = new HashSet<Node>();//每次循环要删除的nodes
            //取eliminationColumnNodes的第一个node
            ColumnNodeNeededDelete = new ArrayList<Node>(eliminationColumnNodes).get(0);
            /**将ColumnNodeNeedeDelete及其要删除的相关nodes和links存储到eliminationNodes和eliminationEdges中**/
            eliminationNodes.add(ColumnNodeNeededDelete);//首先添加ColumnNodeNeedeDelete
            //找到需要删除的相关nodes
            //首先存储当前Semantic model中的所有internalnodes及其outgoinglinks数量
            for(Node node: needEliminateSource.getInternalNodes()){
                int num = 0;
                for(DefaultLink link: needEliminateSource.getGraph().edgeSet()){
                    if(link.getSource().equals(node))
                        num++;
                }
                NodeOutgoingLinksNum1.put(node,num);
            }
            //遍历当前semantic model中internal nodes及其outgoinglinks数量
            for(Node node: NodeOutgoingLinksNum1.keySet()){
                System.out.println("NodeOutgoingLinksNum1:" + node.getId()+"||"+NodeOutgoingLinksNum1.get(node));
            }
            //遍历所有的root
            List<List<Node>> AllPathsPerColumnnode = new ArrayList<List<Node>>();
            for(Node root: RootList) {
                //找到root到ColumnNodeNeededDelete的paths
                connectedPathsNode = new ArrayList<List<Node>>();
                findAllPathNode(LinkList,root.getId(),ColumnNodeNeededDelete.getId(),100);
                if(connectedPathsNode.size()>0) {
                    AllPathsPerColumnnode.addAll(connectedPathsNode);
                }
            }
            System.out.println("AllPathsPerColumnnode.size:"+AllPathsPerColumnnode.size());
            //找到最长的一条path
            int pathlength = 0;
            List<Node> LongPath = new ArrayList<Node>();
            for(List<Node> path: AllPathsPerColumnnode){
                if(path.size()>pathlength){
                    pathlength = path.size();
                    LongPath = path;
                }
            }

            for(int i=LongPath.size()-2;i>=0;i--){
                Boolean flag = false;
                int node_num;
                for(Node nodemapoutgoingnum: NodeOutgoingLinksNum1.keySet()){
                    if(LongPath.get(i).equals(nodemapoutgoingnum)){
                        node_num = NodeOutgoingLinksNum1.get(nodemapoutgoingnum)-1;
                        if(node_num==0){
                            eliminationNodes.add(LongPath.get(i));
                        }
                        if(node_num>0){
                            flag=true;
                        }
                        break;
                    }
                }
                if(flag){
                    break;
                }
            }


            for(Node node: eliminationNodes) {
                for (DefaultLink link : needEliminateSource.getGraph().edgeSet()) {
                    if (link.getTarget().equals(node)) {
                        eliminationEdges.add(link);
                    }
                }
            }

            /**删除节点**/
            for(Node needeliminationNodes: eliminationNodes) {
                needEliminateSource.getGraph().removeVertex(needeliminationNodes);
            }
            /**删除边**/
            for(DefaultLink link: eliminationEdges){
                if(link instanceof LabeledLink) {
                    needEliminateSource.getGraph().removeEdge((LabeledLink) link);
                }
            }
            System.out.println("循环中needEliminateSource的nodes:" + needEliminateSource.getGraph().vertexSet().size());
            System.out.println("循环中needEliminateSource的links:" + needEliminateSource.getGraph().edgeSet().size());
            /**检查是否需要删除root**/
            /**获取当前needEliminateSource的所有root节点**/
            RootList = getSemanticModelRootList(needEliminateSource);
            System.out.println("循环中NewRootList.get(0):"+ RootList.get(0).getId());
            while(RootList.size()>0){
                Boolean IsDelRoot = false;
                for(Node root: RootList){
                    int rootoutgoinglinks = 0;
                    DefaultLink deletelink = null;
                    for(DefaultLink link: needEliminateSource.getGraph().edgeSet()){
                        if(link.getSource().equals(root)){
                            ++rootoutgoinglinks;
                            deletelink = link;
                        }
                    }
                    if(rootoutgoinglinks==1){
                        IsDelRoot = true;
                        needEliminateSource.getGraph().removeVertex(root);
                        needEliminateSource.getGraph().removeEdge((LabeledLink) deletelink);
                    }
//                    RootList.remove(root);
                }
                if(IsDelRoot) {
                    RootList = getSemanticModelRootList(needEliminateSource);
                }
                else{
                    RootList = new ArrayList<Node>();
                }
            }


            /**完成一个ColumnNodeNeedDelete及其相关nodes和links的删除工作  从eliminationColumnNodes中删除此ColumnNodeNeedDelete**/
            eliminationColumnNodes.remove(ColumnNodeNeededDelete);
        }


        /**保存语义模型**/
        try {
            DirectedWeightedMultigraph needEliminateSourceJson = needEliminateSource.getGraph();
            GraphUtil.exportJson(needEliminateSourceJson, graphNameJson,true,true);
            GraphVizUtil.exportSemanticModelToGraphviz(needEliminateSource,GraphVizLabelType.LocalId,
                    GraphVizLabelType.LocalUri,true,true,graphName);
        } catch (Exception e) {
            e.printStackTrace();
        }

        System.out.println("打印图信息-------");
        System.out.println("# of nodes in model learning graph: " + needEliminateSource.getGraph().vertexSet().size());
        System.out.println("# of links in model learning graph: " +needEliminateSource.getGraph().edgeSet().size());

        return needEliminateSource;
    }

    /**6.23 给定SemanticModel 获取初始的搜索semantic models  每一个搜索状态为在原始正确SemanticModel的基础上删除一个属性**/
    public static List<SemanticModel> getNewStartStatesSemanticModelForEmbedding(SemanticModel sm) throws Exception {

        System.out.println("进入getNewStartStatesSemanticModelForEmbedding");
        List<SemanticModel> NewStartStatesSemanticModels = new LinkedList<SemanticModel>();

        SemanticModel newSource = sm;

        SemanticModel NewSource = null;//待删除的semantic model

        logger.info("======================================================");
        logger.info(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");//获取新源的数据节点
        System.out.println(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");
        System.out.println(newSource.getName() + "(#links:" + newSource.getGraph().edgeSet().size() + ")");
        logger.info("======================================================");

        Set<Set<String>> DelColumnNodesList = new HashSet<Set<String>>();
        Set<String> ColumnNodes = new HashSet<String>();
        //遍历SemanticModel的columnode
        for(ColumnNode node: newSource.getColumnNodes()){
            ColumnNodes.add(node.getColumnName());
            DelColumnNodesList.add(ColumnNodes);
            ColumnNodes = new HashSet<String>();
        }

        /**遍历存储删除数据节点列表的列表**/
        System.out.println("遍历存储删除数据节点列表的列表：");
        int Index=0;
        int Count=0;
        for(Set<String> hashSet: DelColumnNodesList){
            Count++;
            System.out.println("ColumnNodes_hashSet:"+Index+"_"+hashSet);
            /**删除节点和边操作**/
            NewSource =  newSource.clone();
            newsemanticmodel = NewEliminatedSemanticModels1(NewSource,Index,Count,hashSet,null,null);
            NewStartStatesSemanticModels.add(newsemanticmodel);
        }
        System.out.println("输出NewStartStatesSemanticModels大小："+NewStartStatesSemanticModels.size());

        return NewStartStatesSemanticModels;
    }


    /**5.18 Added**/
    public static List<SemanticModel> getNewStartStatesSemanticModel1(int newSourceIndex) throws Exception {

        System.out.println("进入getNewStartStatesSemanticModel");
        List<SemanticModel> NewStartStatesSemanticModels = new LinkedList<SemanticModel>();

        SemanticModel NewSource = null;//待删除的semantic model

        SemanticModel newSource = GenerateNewSM1(newSourceIndex);

        System.out.println("GenerateNewSM结束,进行下一步操作-----");


        GraphVizUtil.exportSemanticModelToGraphviz(newSource,GraphVizLabelType.LocalId,
                GraphVizLabelType.LocalUri,true,true,"E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\train-graph\\GenerateNewSM\\" + "GenerateNewSM.dot");


        logger.info("======================================================");
        logger.info(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");//获取新源的数据节点
        System.out.println(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");
        System.out.println(newSource.getName() + "(#links:" + newSource.getGraph().edgeSet().size() + ")");
        logger.info("======================================================");

        //将新源语义模型的数据节点存储到列表中
        List<ColumnNode> columnNodes = newSource.getColumnNodes();
        //存储要删除的节点（在语义标注阶段不能被正确预测的节点）
        List<ColumnNode> dellabelcolumnnodes = new LinkedList<ColumnNode>();

        System.out.println("目前已经删除在语义标记阶段不能正确标记的column node了！");

        //存储要执行删除操作的新语义模型的数据节点
        List<ColumnNode> newcolumnNodes = newSource.getColumnNodes();
        String semantictype = null;
        String possiblesemantictype=null;

        //存储新语义模型数据节点的正确语义类型
        Map<String,String> correctsemantictyes= new HashMap<String,String>();
        //存储要删除的节点列表
        List<List> delcolumnnodeslist = new LinkedList<List>();

        Set<String> DelcolumnnodesList = new HashSet<String>();

        List<Set> DELcolumnnodesList = new LinkedList<Set>();

        Set<Set<String>> JudgeDelcolumnnodesList = new HashSet<Set<String>>();//用以判断是否已存在相同的删除列表
        Set<Set<String>> DelColumnnodesList = new HashSet<Set<String>>();//用以保存每个columnnode对应要删除的节点列表
        Set<Set<String>> FinalDelColumnnodesList = new HashSet<Set<String>>();//用以保存每个columnnode最终对应的要删除的节点列表

        List<Set<Set<String>>> DelColumnNodesList = new LinkedList<Set<Set<String>>>();//用以保存这一semantic model最终要删除的所有节点列表

        System.out.println("新语义模型数据节点正确的语义类型,以hashmap数据结构进行存储;key:数据节点名,value:语义类型");

        for(ColumnNode n: newcolumnNodes){//遍历新语义模型的column node
//            System.out.println("遍历新语义模型的column node:"+n.getColumnName());
            List<SemanticType> correctSemanticTypes = getCandidateSteinerSets(n, true, 2);
//            if(correctSemanticTypes!=null) {
//                System.out.println("true:"+correctSemanticTypes.size());
//            }
            semantictype = (correctSemanticTypes.get(0).getDomain().toString()+";"+correctSemanticTypes.get(0).getType().toString());

            correctsemantictyes.put(n.getColumnName(),semantictype);//存储column node及其semantic type
        }
        for (String i : correctsemantictyes.keySet()) {
            System.out.println("key: " + i + " value: " + correctsemantictyes.get(i));
        }

        System.out.println("新语义模型数据节点的可能语义类型");
        for(ColumnNode o: newcolumnNodes){
//            DelcolumnnodesList.add(o.getColumnName());
            DelColumnnodesList = new HashSet<Set<String>>();//关于每个数据节点要删除的多个节点集合
            FinalDelColumnnodesList = new HashSet<Set<String>>();//最终要删除的所有节点集合
//            DelcolumnnodesList = new HashSet<String>(Arrays.asList(o.getColumnName()));
            List<SemanticType> possibleSemanticTypes = getCandidateSteinerSets(o, false, 4);

            System.out.println(o.getColumnName());//输出遍历到的数据节点名
            for(SemanticType p: possibleSemanticTypes){
                possiblesemantictype=((p.getDomain()).toString())+";"+((p.getType()).toString());
                System.out.println("输出数据节点的候选语义类型："+possiblesemantictype);//输出数据节点的候选语义类型

                for (String i : correctsemantictyes.keySet()) {
                    DelcolumnnodesList=new HashSet<String>();
                    if((correctsemantictyes.get(i)).equals(possiblesemantictype)){
                        DelcolumnnodesList.add(o.getColumnName());
                        DelcolumnnodesList.add(i);
                        DelColumnnodesList.add(DelcolumnnodesList);
                        continue;//////////5.13
//                        System.out.println(i);
                    }
//                    System.out.println("key: " + i + " value: " + correctsemantictyes.get(i));
                }
            }
            if(DelColumnnodesList.size()>1){
                for(Set<String> columnnodesList: DelColumnnodesList){
                    if(columnnodesList.size()>1&&(!Judge(JudgeDelcolumnnodesList,columnnodesList))){
                        FinalDelColumnnodesList.add(columnnodesList);
                        JudgeDelcolumnnodesList.add(columnnodesList);
//                        System.out.println("true");
                    }
                }
            }
            else{
//                FinalDelColumnnodesList = DelColumnnodesList;
                if(IsDelFlag&&(possibleSemanticTypes.size()>1)) {
                    FinalDelColumnnodesList = DelColumnnodesList;
                }
                else{
                    FinalDelColumnnodesList = new HashSet<Set<String>>();
                }
            }

            System.out.println("DelColumnnodesList:"+DelColumnnodesList);
            System.out.println("FinalDelColumnnodesList"+FinalDelColumnnodesList);

            if(FinalDelColumnnodesList.size()!=0) {
                DelColumnNodesList.add(FinalDelColumnnodesList);
            }
            System.out.println("一轮结束");
        }

        System.out.println("最后的列表："+DelColumnNodesList);
//        System.out.println("JudgeDelcolumnnodesList:" + JudgeDelcolumnnodesList);


        /**遍历存储删除数据节点列表的列表**/
        System.out.println("遍历存储删除数据节点列表的列表：");
        int Index=0;
        int Count=0;
        int count=0;
        for(Set<Set<String>> hashSet_hashSet: DelColumnNodesList){
            Index++;
            System.out.println("hashSet_hashSet:"+hashSet_hashSet);
            Count=0;
            for(Set<String> hashSet: hashSet_hashSet){
                Count++;
                System.out.println("hashSet_"+Index+hashSet);
                /**删除节点和边操作**/
                NewSource =  newSource.clone();
                newsemanticmodel = NewEliminatedSemanticModels1(NewSource,Index,Count,hashSet,null,null);
                NewStartStatesSemanticModels.add(newsemanticmodel);
            }
        }

        System.out.println("输出NewStartStatesSemanticModels大小："+NewStartStatesSemanticModels.size());


        return NewStartStatesSemanticModels;
    }
    public static SemanticModel GenerateNewSM1(int SourceIndex) throws Exception{

        SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);

        SemanticModel Source = SemanticModels.get(SourceIndex);
        SemanticModel InitialSource = Source.clone();

        /**保存语义模型图的路径**/
        String graphPath = Params.Generate_New_SM;
        String graphPathJson = Params.Generate_New_SM;
        /**生成train graph文件名**/
        String graphName = graphPath + SemanticModels.get(SourceIndex).getName() + ".new" + Params.GRAPH_JSON_FILE_EXT;
        String graphNameJson = graphPathJson + SemanticModels.get(SourceIndex).getName() + ".new" + Params.GRAPH_JSON_FILE_EXT;


        logger.info("======================================================");
        logger.info(Source.getName() + "(#attributes:" + Source.getColumnNodes().size() + ")");//获取语义模型的数据节点数目
        System.out.println(Source.getName() + "(#attributes:" + Source.getColumnNodes().size() + ")");
        logger.info("======================================================");

        //将语义模型的数据节点存储到列表中
        List<ColumnNode> columnNodes = Source.getColumnNodes();
        //存储正确的语义类型和得分最高的候选语义类型
        SemanticType correctSemanticType,topcandidateSemanticType;
        //存储能否正确预测语义类型的结果
        List<Boolean> label_true_or_false = new LinkedList<Boolean>();
        //存储要删除的节点（在语义标注阶段不能被正确预测的节点）
        /**打印每次要删除的节点列表**/
        Set<DefaultLink> dellabeledges = new HashSet<DefaultLink>();//定义要删除的边列表集合
//        List<Node> dellabelcolumnnodes = new LinkedList<Node>();//////////////////////////////////////
        Set<Node> dellabelcolumnnodes = new HashSet<Node>();
        Set<String> dellabelcolumnnodesName = new HashSet<String>();
        Boolean true_false = false;


        /**获取当前semantic model的links**/
        List<DefaultLink> SMLinkList = new ArrayList<DefaultLink>();
        for(DefaultLink link: Source.getGraph().edgeSet()){
            SMLinkList.add(link);
        }


        /**找出在semantic labeling阶段没有被正确预测semantic type的columnnodes**/
        for(ColumnNode i: columnNodes){
            System.out.println("ColumnName:"+i.getColumnName());
            List<SemanticType> correctSemanticTypes = getCandidateSteinerSets(i, true, 2);
            List<SemanticType> candidateSemanticTypes = getCandidateSteinerSets(i, false,1);

            correctSemanticType = correctSemanticTypes.get(0);
            topcandidateSemanticType = candidateSemanticTypes.get(0);


            if((!(correctSemanticType.getDomain()).equals(topcandidateSemanticType.getDomain()))||(!(correctSemanticType.getType()).equals(topcandidateSemanticType.getType()))){
                dellabelcolumnnodes.add(i);
                dellabelcolumnnodesName.add(i.getColumnName());
            }
            label_true_or_false.add((correctSemanticType.getDomain()).equals(topcandidateSemanticType.getDomain()));

        }

        System.out.println("dellabelcolumnnodesName:" + dellabelcolumnnodesName);


        System.out.println("未删除节点前的边数目："+Source.getGraph().edgeSet().size());
        System.out.println("未删除节点前的节点数目："+Source.getGraph().vertexSet().size());
        System.out.println("未删除节点前的columnnode数目："+Source.getColumnNodes().size());

        Source = NewEliminatedSemanticModels1(Source,0,0,dellabelcolumnnodesName,graphName,graphNameJson);///////5.18开

        //判断GenerateNewSM阶段有没有删除不正确预测的node 如果有 则将IsDelFlag设置为true  如果没有 则将IsDelFalg设置为false
        if(Source.getColumnNodes().size()==InitialSource.getColumnNodes().size()){
            IsDelFlag = false;
        }

        System.out.println("删除节点后的边数目："+Source.getGraph().edgeSet().size());
        System.out.println("删除节点后的节点数目："+Source.getGraph().vertexSet().size());
        System.out.println("删除节点后的columnnode数目："+Source.getColumnNodes().size());

//        /**保存语义模型图的路径**/
//        String graphPath = Params.Generate_New_SM;
//        String graphPathJson = Params.Generate_New_SM;
//        /**生成train graph文件名**/
//        String graphName = graphPath + SemanticModels.get(SourceIndex).getName() + ".new" + Params.GRAPH_JSON_FILE_EXT;
//        String graphNameJson = graphPathJson + SemanticModels.get(SourceIndex).getName() + ".new" + Params.GRAPH_JSON_FILE_EXT;

//        /**保存语义模型**/
//        try {
//////                GraphUtil.exportJson(modelLearningGraph.getGraphBuilder().getGraph(), graphName + ".json",true,true);
////            GraphUtil.exportJson(needEliminateSource.getGraph(), graphName + ".json",true,true);
////            /**Visualize the merged graph (model learning graph). 18 June 2018.**/
////            for (Node node : modelLearner.graphBuilder.getGraph().vertexSet()) {
////                System.out.println(node);
////            }
////
////
//            GraphVizUtil.exportSemanticModelToGraphviz(Source,GraphVizLabelType.LocalId,
//                    GraphVizLabelType.LocalUri,true,true,graphName + ".dot");
//
//        } catch (Exception e) {
//            e.printStackTrace();
//        }

        return Source;
    }

    public static SemanticModel NewEliminatedSemanticModels1(SemanticModel sm, int Index, int index,Set<String> DELcolumnnodes, String graphName, String graphNameJson) throws Exception {
        System.out.println("进入NewEliminatedSemanticModels1");
        /**保存语义模型图的路径**/
        String graphPath = Params.TRAIN_MODEL_DIR + "new-train-graph-for-embedding/";
        String graphPathJson = Params.TRAIN_MODEL_DIR + "new-train-graph-json-for-embedding/";

        /**先读进语义模型**/
//        semanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json", Params.MODEL_MAIN_FILE_EXT);
        SemanticModel needEliminateSource = sm;
        /**生成train graph文件名**/
        if(graphName == null) {
            graphName = graphPath + sm.getName() + ".Train_" + Index + ".train_" + index + Params.GRAPH_JSON_FILE_EXT;
        }
        if(graphNameJson == null) {
            graphNameJson = graphPathJson + sm.getName() + ".Train_" + Index + ".train_" + index + Params.GRAPH_JSON_FILE_EXT;
        }

        logger.info("======================================================");
        logger.info(needEliminateSource.getName() + "(#attributes:" + needEliminateSource.getColumnNodes().size() + ")");//获取新源的数据节点
        System.out.println(needEliminateSource.getName() + "(#attributes:" + needEliminateSource.getColumnNodes().size() + ")");
        System.out.println(needEliminateSource.getName() + "(#links:" + needEliminateSource.getGraph().edgeSet().size() + ")");
        logger.info("======================================================");


        List<ColumnNode> steinerNodes = new ArrayList<>(needEliminateSource.getColumnNodes());
        for(ColumnNode i: steinerNodes){
            System.out.println("打印删除nodes前的SMnodes.name:"+i.getColumnName());
        }
        /**定义每次要删除的link列表和node列表**/
        Set<Node> eliminationColumnNodes = new HashSet<Node>();//存储语义模型中要删除的columnnodes
        Set<DefaultLink> eliminationEdges = null;//定义要删除的边列表集合
        Set<Node> eliminationNodes = null;//针对每个待删除的columnnode 存储其所有需要删除的nodes
        for(ColumnNode i: steinerNodes){
            for(String columnnodename: DELcolumnnodes){
                if(i.getColumnName().equals(columnnodename)){
                    eliminationColumnNodes.add(i);
                }
            }
        }


        for(Node i: eliminationColumnNodes){
            System.out.println("打印要删除的nodes.id:"+i.getId());
        }

        List<Node> RootList = null;


        /**5.18**/
        int loopnum = eliminationColumnNodes.size();
        Node ColumnNodeNeededDelete = null;
        while(eliminationColumnNodes.size()>0){
            /**获取当前semantic model的所有root节点**/
            RootList = getSemanticModelRootList(needEliminateSource);
            for(Node root: RootList) {
                System.out.println("Rootlist:" + root.getId());
            }
            /**将当前semantic model中的links保存到List<DefaultLink>中**/
            List<DefaultLink> LinkList = new ArrayList<DefaultLink>();
            LinkList.addAll(needEliminateSource.getGraph().edgeSet());
            /**获取当前semantic model的internal及其outgoinglinks数量**/
            Map<Node,Integer> NodeOutgoingLinksNum1 = new HashMap<Node,Integer>();
            /**初始化eliminationEdges及eliminationNodes**/
            eliminationEdges = new HashSet<DefaultLink>();//每次循环要删除的links
            eliminationNodes = new HashSet<Node>();//每次循环要删除的nodes
            //取eliminationColumnNodes的第一个node
            ColumnNodeNeededDelete = new ArrayList<Node>(eliminationColumnNodes).get(0);
            /**将ColumnNodeNeedeDelete及其要删除的相关nodes和links存储到eliminationNodes和eliminationEdges中**/
            eliminationNodes.add(ColumnNodeNeededDelete);//首先添加ColumnNodeNeedeDelete
            //找到需要删除的相关nodes
            //首先存储当前Semantic model中的所有internalnodes及其outgoinglinks数量
            for(Node node: needEliminateSource.getInternalNodes()){
                int num = 0;
                for(DefaultLink link: needEliminateSource.getGraph().edgeSet()){
                    if(link.getSource().equals(node))
                        num++;
                }
                NodeOutgoingLinksNum1.put(node,num);
            }
            //遍历当前semantic model中internal nodes及其outgoinglinks数量
            for(Node node: NodeOutgoingLinksNum1.keySet()){
                System.out.println("NodeOutgoingLinksNum1:" + node.getId()+"||"+NodeOutgoingLinksNum1.get(node));
            }
            //遍历所有的root
            List<List<Node>> AllPathsPerColumnnode = new ArrayList<List<Node>>();
            for(Node root: RootList) {
                //找到root到ColumnNodeNeededDelete的paths
                connectedPathsNode = new ArrayList<List<Node>>();
                findAllPathNode(LinkList,root.getId(),ColumnNodeNeededDelete.getId(),100);
                if(connectedPathsNode.size()>0) {
                    AllPathsPerColumnnode.addAll(connectedPathsNode);
                }
            }
            System.out.println("AllPathsPerColumnnode.size:"+AllPathsPerColumnnode.size());
            //找到最长的一条path
            int pathlength = 0;
            List<Node> LongPath = new ArrayList<Node>();
            for(List<Node> path: AllPathsPerColumnnode){
                if(path.size()>pathlength){
                    pathlength = path.size();
                    LongPath = path;
                }
            }
//            for(int k=0;k<LongPath.size()-1;k++){
//                //如果没有node,则添加该node及其value
//                if(!(PathNodeNum.keySet().contains(LongPath.get(k)))){
//                    PathNodeNum.put(LongPath.get(k),1);
//                }
//                //如果有node,则只需要改变其value
//                else{
//                    int path_node_num;
//                    path_node_num = PathNodeNum.get(LongPath.get(k))+1;
//                    PathNodeNum.put(LongPath.get(k),path_node_num);
//                }
//            }
//            for(Node node: PathNodeNum.keySet()){
//                System.out.println("PathNodeNum:" + node.getId()+"||"+PathNodeNum.get(node));
//            }
//            //遍历PathNodeNum
//            int node_new_num;
//            for(Node node: PathNodeNum.keySet()){
//                for(Node nodemapoutgoingnum: NodeOutgoingLinksNum.keySet()){
//                    if(node.equals(nodemapoutgoingnum)){
//                        node_new_num = NodeOutgoingLinksNum.get(nodemapoutgoingnum)-PathNodeNum.get(node);
//                        NodeOutgoingLinksNum.put(nodemapoutgoingnum,node_new_num);
//                        break;
//                    }
//                }
//            }
            for(int i=LongPath.size()-2;i>=0;i--){
                Boolean flag = false;
                int node_num;
                for(Node nodemapoutgoingnum: NodeOutgoingLinksNum1.keySet()){
                    if(LongPath.get(i).equals(nodemapoutgoingnum)){
                        node_num = NodeOutgoingLinksNum1.get(nodemapoutgoingnum)-1;
                        if(node_num==0){
                            eliminationNodes.add(LongPath.get(i));
                        }
                        if(node_num>0){
                            flag=true;
                        }
                        break;
                    }
                }
                if(flag){
                    break;
                }
            }

//            for(Node node: LongPath){
//                int node_num;
//                for(Node nodemapoutgoingnum: NodeOutgoingLinksNum1.keySet()){
//                    if(node.equals(nodemapoutgoingnum)){
//                        node_num = NodeOutgoingLinksNum1.get(nodemapoutgoingnum)-1;
//                        if(node_num==0){
//                            eliminationNodes.add(node);
//                        }
//                        break;
//                    }
//                }
//            }

            for(Node node: eliminationNodes) {
                for (DefaultLink link : needEliminateSource.getGraph().edgeSet()) {
                    if (link.getTarget().equals(node)) {
                        eliminationEdges.add(link);
                    }
                }
            }

            /**删除节点**/
            for(Node needeliminationNodes: eliminationNodes) {
                needEliminateSource.getGraph().removeVertex(needeliminationNodes);
            }
            /**删除边**/
            for(DefaultLink link: eliminationEdges){
                if(link instanceof LabeledLink) {
                    needEliminateSource.getGraph().removeEdge((LabeledLink) link);
                }
            }
            System.out.println("循环中needEliminateSource的nodes:" + needEliminateSource.getGraph().vertexSet().size());
            System.out.println("循环中needEliminateSource的links:" + needEliminateSource.getGraph().edgeSet().size());
            /**检查是否需要删除root**/
            /**获取当前needEliminateSource的所有root节点**/
            RootList = getSemanticModelRootList(needEliminateSource);
            System.out.println("循环中NewRootList.get(0):"+ RootList.get(0).getId());
            while((needEliminateSource.getGraph().vertexSet().size()>2)&&(RootList.size()>0)){
                Boolean IsDelRoot = false;
                for(Node root: RootList){
                    int rootoutgoinglinks = 0;
                    DefaultLink deletelink = null;
                    for(DefaultLink link: needEliminateSource.getGraph().edgeSet()){
                        if(link.getSource().equals(root)){
                            ++rootoutgoinglinks;
                            deletelink = link;
                        }
                    }
                    if(rootoutgoinglinks==1){
                        IsDelRoot = true;
                        needEliminateSource.getGraph().removeVertex(root);
                        needEliminateSource.getGraph().removeEdge((LabeledLink) deletelink);
                    }
//                    RootList.remove(root);
                }
                if(IsDelRoot) {
                    RootList = getSemanticModelRootList(needEliminateSource);
                }
                else{
                    RootList = new ArrayList<Node>();
                }
            }

//            for(Node root: NewRootList){
//                int rootoutgoinglinks = 0;
//                DefaultLink deletelink = null;
//                for(DefaultLink link: needEliminateSource.getGraph().edgeSet()){
//                    if(link.getSource().equals(root)){
//                        ++rootoutgoinglinks;
//                        deletelink = link;
//                    }
//                }
//                if(rootoutgoinglinks==1){
//                    needEliminateSource.getGraph().removeVertex(root);
//                    needEliminateSource.getGraph().removeEdge((LabeledLink) deletelink);
//                }
//            }

            /**完成一个ColumnNodeNeedDelete及其相关nodes和links的删除工作  从eliminationColumnNodes中删除此ColumnNodeNeedDelete**/
            eliminationColumnNodes.remove(ColumnNodeNeededDelete);
        }


        /**保存语义模型**/
        try {
            DirectedWeightedMultigraph needEliminateSourceJson = needEliminateSource.getGraph();
            GraphUtil.exportJson(needEliminateSourceJson, graphNameJson + ".json",true,true);
            GraphVizUtil.exportSemanticModelToGraphviz(needEliminateSource,GraphVizLabelType.LocalId,
                    GraphVizLabelType.LocalUri,true,true,graphName + ".dot");
        } catch (Exception e) {
            e.printStackTrace();
        }

        System.out.println("打印图信息-------");
        System.out.println("# of nodes in model learning graph: " + needEliminateSource.getGraph().vertexSet().size());
        System.out.println("# of links in model learning graph: " +needEliminateSource.getGraph().edgeSet().size());

        return needEliminateSource;
    }
    /**5.18 Added**/

    /**new semantic model生成初始search states**/
    public static List<SemanticModel> getNewStartStatesSemanticModel(int newSourceIndex) throws Exception {

        System.out.println("进入getNewStartStatesSemanticModel");
        List<SemanticModel> NewStartStatesSemanticModels = new LinkedList<SemanticModel>();

        SemanticModel NewSource = null;//待删除的semantic model

        SemanticModel newSource = GenerateNewSM(newSourceIndex);

        System.out.println("GenerateNewSM结束,进行下一步操作-----");


        logger.info("======================================================");
        logger.info(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");//获取新源的数据节点
        System.out.println(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");
        System.out.println(newSource.getName() + "(#links:" + newSource.getGraph().edgeSet().size() + ")");
        logger.info("======================================================");

        //将新源语义模型的数据节点存储到列表中
        List<ColumnNode> columnNodes = newSource.getColumnNodes();
        //存储要删除的节点（在语义标注阶段不能被正确预测的节点）
        List<ColumnNode> dellabelcolumnnodes = new LinkedList<ColumnNode>();

        System.out.println("目前已经删除在语义标记阶段不能正确标记的column node了！");

        //存储要执行删除操作的新语义模型的数据节点
        List<ColumnNode> newcolumnNodes = newSource.getColumnNodes();
        String semantictype = null;
        String possiblesemantictype=null;

        //存储新语义模型数据节点的正确语义类型
        Map<String,String> correctsemantictyes= new HashMap<String,String>();
        //存储要删除的节点列表
        List<List> delcolumnnodeslist = new LinkedList<List>();

        Set<String> DelcolumnnodesList = new HashSet<String>();

        List<Set> DELcolumnnodesList = new LinkedList<Set>();

        Set<Set<String>> JudgeDelcolumnnodesList = new HashSet<Set<String>>();//用以判断是否已存在相同的删除列表
        Set<Set<String>> DelColumnnodesList = new HashSet<Set<String>>();//用以保存每个columnnode对应要删除的节点列表
        Set<Set<String>> FinalDelColumnnodesList = new HashSet<Set<String>>();//用以保存每个columnnode最终对应的要删除的节点列表

        List<Set<Set<String>>> DelColumnNodesList = new LinkedList<Set<Set<String>>>();//用以保存这一semantic model最终要删除的所有节点列表

        System.out.println("新语义模型数据节点正确的语义类型,以hashmap数据结构进行存储;key:数据节点名,value:语义类型");

        for(ColumnNode n: newcolumnNodes){//遍历新语义模型的column node
//            System.out.println("遍历新语义模型的column node:"+n.getColumnName());
            List<SemanticType> correctSemanticTypes = getCandidateSteinerSets(n, true, 2);
//            if(correctSemanticTypes!=null) {
//                System.out.println("true:"+correctSemanticTypes.size());
//            }
            semantictype = (correctSemanticTypes.get(0).getDomain().toString()+";"+correctSemanticTypes.get(0).getType().toString());

            correctsemantictyes.put(n.getColumnName(),semantictype);//存储column node及其semantic type
        }
        for (String i : correctsemantictyes.keySet()) {
            System.out.println("key: " + i + " value: " + correctsemantictyes.get(i));
        }

        System.out.println("新语义模型数据节点的可能语义类型");
        for(ColumnNode o: newcolumnNodes){
//            DelcolumnnodesList.add(o.getColumnName());
            DelColumnnodesList = new HashSet<Set<String>>();//关于每个数据节点要删除的多个节点集合
            FinalDelColumnnodesList = new HashSet<Set<String>>();//最终要删除的所有节点集合
//            DelcolumnnodesList = new HashSet<String>(Arrays.asList(o.getColumnName()));
            List<SemanticType> possibleSemanticTypes = getCandidateSteinerSets(o, false, 4);

            System.out.println(o.getColumnName());//输出遍历到的数据节点名
            for(SemanticType p: possibleSemanticTypes){
                possiblesemantictype=((p.getDomain()).toString())+";"+((p.getType()).toString());
                System.out.println("输出数据节点的候选语义类型："+possiblesemantictype);//输出数据节点的候选语义类型

                for (String i : correctsemantictyes.keySet()) {
                    DelcolumnnodesList=new HashSet<String>();
                    if((correctsemantictyes.get(i)).equals(possiblesemantictype)){
                        DelcolumnnodesList.add(o.getColumnName());
                        DelcolumnnodesList.add(i);
                        DelColumnnodesList.add(DelcolumnnodesList);
                        continue;//////////5.13
//                        System.out.println(i);
                    }
//                    System.out.println("key: " + i + " value: " + correctsemantictyes.get(i));
                }
            }
            if(DelColumnnodesList.size()>1){
                for(Set<String> columnnodesList: DelColumnnodesList){
                    if(columnnodesList.size()>1&&(!Judge(JudgeDelcolumnnodesList,columnnodesList))){
                        FinalDelColumnnodesList.add(columnnodesList);
                        JudgeDelcolumnnodesList.add(columnnodesList);
//                        System.out.println("true");
                    }
//                    else{
//                        System.out.println("false");
//                    }
                }
            }
            else{
                FinalDelColumnnodesList=DelColumnnodesList;
            }

            System.out.println("DelColumnnodesList:"+DelColumnnodesList);
            System.out.println("FinalDelColumnnodesList"+FinalDelColumnnodesList);

            if(FinalDelColumnnodesList.size()!=0) {
                DelColumnNodesList.add(FinalDelColumnnodesList);
            }
            System.out.println("一轮结束");
        }

        System.out.println("最后的列表："+DelColumnNodesList);
//        System.out.println("JudgeDelcolumnnodesList:" + JudgeDelcolumnnodesList);


        /**遍历存储删除数据节点列表的列表**/
        System.out.println("遍历存储删除数据节点列表的列表：");
        int Index=0;
        int Count=0;
        int count=0;
        for(Set<Set<String>> hashSet_hashSet: DelColumnNodesList){
            Index++;
            System.out.println("hashSet_hashSet:"+hashSet_hashSet);
            Count=0;
            for(Set<String> hashSet: hashSet_hashSet){
                Count++;
                System.out.println("hashSet_"+Index+hashSet);
                /**删除节点和边操作**/
                NewSource =  newSource.clone();
                newsemanticmodel = NewEliminatedSemanticModels(NewSource,Index,Count,hashSet,null,null);
                NewStartStatesSemanticModels.add(newsemanticmodel);
            }
        }

        System.out.println("输出NewStartStatesSemanticModels大小："+NewStartStatesSemanticModels.size());


        return NewStartStatesSemanticModels;
    }

    /**此函数的作用是给定一个移除数据节点的列表，根据列表中每个集合给定的信息来删除数据节点和输入边，并将完成删除操作后的语义模型存储起来
     * EliminatedSemanticModels针对原始semantic model
     * NewEliminatedSemanticModels针对new semantic model**/
    static HashSet<String> correcta = new HashSet<String>(Arrays.asList("Artist_Appellation_URI","Actor_URI"));
    static HashSet<String> correctb = new HashSet<String>(Arrays.asList("Title"));
    static List<HashSet> correctc = new LinkedList<HashSet>(Arrays.asList(correcta,correctb));
    public static List<SemanticModel> EliminatedSemanticModels(int newSourceIndex, int Index, int index, Set<String> DELcolumnnodes) throws Exception {
        /**保存语义模型图的路径**/
        String graphPath = Params.TRAIN_MODEL_DIR + "Train-graph/";

        /**先读进语义模型**/
        semanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json", Params.MODEL_MAIN_FILE_EXT);

        /**生成train graph文件名**/
        String graphName = graphPath + semanticModels.get(newSourceIndex).getName() + ".Train_" + Index + ".train_" + index + Params.GRAPH_JSON_FILE_EXT;

        SemanticModel needEliminateSource = semanticModels.get(newSourceIndex);
        logger.info("======================================================");
        logger.info(needEliminateSource.getName() + "(#attributes:" + needEliminateSource.getColumnNodes().size() + ")");//获取新源的数据节点
        System.out.println(needEliminateSource.getName() + "(#attributes:" + needEliminateSource.getColumnNodes().size() + ")");
        logger.info("======================================================");
//        SteinerNode steinerNode1 = new SteinerNode("HN868");
//        System.out.println(steinerNode1.getNeighbors());

        System.out.println("打印语义模型的数据节点");

        List<ColumnNode> steinerNodes = new ArrayList<>(needEliminateSource.getColumnNodes());
        for(ColumnNode i: steinerNodes){
            System.out.println(i);
        }
        /**打印每次要删除的节点列表**/
        Set<DefaultLink> eliminationEdges = new HashSet<DefaultLink>();//定义要删除的边列表集合
        Set<ColumnNode> eliminationNodes = new HashSet<ColumnNode>();//存储语义模型中要删除的节点
        for(ColumnNode i: steinerNodes){
            for(String columnnodename: DELcolumnnodes){
                if(i.getColumnName().equals(columnnodename)){
                    eliminationNodes.add(i);
                }
            }
        }

        System.out.println("打印要删除的节点"+eliminationNodes);
        System.out.println("未删除节点前的边数目："+needEliminateSource.getGraph().edgeSet().size());
        System.out.println("未删除节点前的节点数目："+needEliminateSource.getGraph().vertexSet().size());
        System.out.println(needEliminateSource.getColumnNodes().size());

        for(ColumnNode columnnode: eliminationNodes){
            System.out.println("打印要删除的节点"+columnnode);
            for(DefaultLink link: needEliminateSource.getGraph().edgeSet()){
//                System.out.println("打印语义模型中的边信息："+link);
//                System.out.println(link.getType());
//                DefaultLink copiedLink = link.clone();//copy the link
//                System.out.println(copiedLink.getTarget());
                if(link.getTarget().equals(columnnode)){
                    System.out.println("打印要删除的边"+link);
//                  needEliminateSource.getGraph().removeEdge(link);
                    eliminationEdges.add(link);
                }
//            else{
//                System.out.println("false");
//            }
            }
        }


//        System.out.println("从原始语义模型的有向权重图中去除第一个数据节点");
//        System.out.println(steinerNodes.get(0).getColumnName());
//        System.out.println("从原始语义模型的有向权重图中去除第一个数据节点的输入边");
//        System.out.println(needEliminateSource.getColumnNodes().get(0).getColumnName());
//        System.out.println("未删除节点前的边数目："+needEliminateSource.getGraph().edgeSet().size());

//        Set<LabeledLink> eliminationEdges= new HashSet<LabeledLink>();

//        for(LabeledLink link: needEliminateSource.getGraph().edgeSet()){
////            System.out.println(link);
////            System.out.println(link.getType());
//            LabeledLink copiedLink = link.clone();//copy the link
////            System.out.println(copiedLink.getTarget());
//            if(copiedLink.getTarget().equals(needEliminateSource.getColumnNodes().get(0))) {
////                System.out.println("true");
////                needEliminateSource.getGraph().removeEdge(link);
//                eliminationEdges.add(copiedLink);
//            }
////            else{
////                System.out.println("false");
////            }
//        }
//        Set<DefaultLink> eliminationEdges1= new HashSet<DefaultLink>();
//        for(DefaultLink link: needEliminateSource.getGraph().edgeSet()){
////            System.out.println(link);
////            System.out.println(link.getType());
////            DefaultLink copiedLink = link.clone();//copy the link
//////            System.out.println(copiedLink.getTarget());
//            if(link.getTarget().equals(needEliminateSource.getColumnNodes().get(0))) {
////                System.out.println("true");
//////                needEliminateSource.getGraph().removeEdge(link);
//                eliminationEdges1.add(link);
//            }
////            else{
////                System.out.println("false");
////            }
//        }

//        System.out.println("输出要删除的边"+eliminationEdges1);
//        System.out.println("输出要删除的边连接的节点"+needEliminateSource.getColumnNodes().get(0));





//        System.out.println("未删除节点前的节点数目："+needEliminateSource.getGraph().vertexSet().size());
//        System.out.println(needEliminateSource.getColumnNodes().size());
        /**删除节点**/
        for(ColumnNode needeliminationNodes: eliminationNodes) {
            needEliminateSource.getGraph().removeVertex(needeliminationNodes);
        }
        /**删除边**/
        for(DefaultLink link: eliminationEdges){
            if(link instanceof LabeledLink) {
//                System.out.println(link);
                needEliminateSource.getGraph().removeEdge((LabeledLink) link);
            }
        }

        System.out.println("删除节点后的边数目："+needEliminateSource.getGraph().edgeSet().size());
        System.out.println("删除节点后的节点数目："+needEliminateSource.getGraph().vertexSet().size());
        System.out.println(needEliminateSource.getColumnNodes().size());


        System.out.println("开始打印现在的图");
        System.out.println("# of nodes in model learning graph: " + needEliminateSource.getGraph().vertexSet().size());
        System.out.println("# of links in model learning graph: " +needEliminateSource.getGraph().edgeSet().size());

        System.out.println("打印语义模型中的边");
        Set<DefaultLink> DefaultLinks = new HashSet<DefaultLink>();
        for(LabeledLink link: needEliminateSource.getGraph().edgeSet()){
            DefaultLinks.add(link);
        }
        System.out.println("DefaultLinks:"+DefaultLinks);



        /**存储类节点**/
        Set<InternalNode> InternalNodes = new HashSet<InternalNode>();
        for(InternalNode node: needEliminateSource.getInternalNodes()){
            InternalNodes.add(node);
        }
        /**存储数据节点**/
        List<ColumnNode> columnNodes1 = needEliminateSource.getColumnNodes();
        List<Node> Nodes = new LinkedList<Node>(columnNodes1);


//        System.out.println("开始打印现在的图2");
//        System.out.println("# of nodes in model learning graph: " + currentGraph.vertexSet().size());
//        System.out.println("# of links in model learning graph: " + currentGraph.edgeSet().size());
        /**保存语义模型**/
        try {
////                GraphUtil.exportJson(modelLearningGraph.getGraphBuilder().getGraph(), graphName + ".json",true,true);
//            GraphUtil.exportJson(needEliminateSource.getGraph(), graphName + ".json",true,true);
//            /**Visualize the merged graph (model learning graph). 18 June 2018.**/
//            for (Node node : modelLearner.graphBuilder.getGraph().vertexSet()) {
//                System.out.println(node);
//            }
//
//
            GraphVizUtil.exportSemanticModelToGraphviz(needEliminateSource,GraphVizLabelType.LocalId,
                    GraphVizLabelType.LocalUri,true,true,graphName + ".dot");
//
        } catch (Exception e) {
            e.printStackTrace();
        }

        System.out.println("开始打印现在的图2");
        System.out.println("# of nodes in model learning graph: " + needEliminateSource.getGraph().vertexSet().size());
        System.out.println("# of links in model learning graph: " +needEliminateSource.getGraph().edgeSet().size());

        /**打印删除节点和边之后语义模型的节点和边信息**/
//        System.out.println("打印删除节点和边之后语义模型的节点和边信息");
//        //将语义模型的数据节点存储到列表中
//        List<ColumnNode> columnNodes = needEliminateSource.getColumnNodes();
//        for(ColumnNode i: columnNodes){
//            System.out.println(i.getColumnName()+":"+i.getId());
//        }
//
//        for(ColumnNode i: columnNodes){
//            System.out.println(i);
//        }
//
//        System.out.println(needEliminateSource.getGraph());
//        System.out.println(needEliminateSource.getColumnNodes());

        return null;
    }


    public static SemanticModel NewEliminatedSemanticModels(SemanticModel sm, int Index, int index,Set<String> DELcolumnnodes, String graphName, String graphNameJson) throws Exception {
        /**保存语义模型图的路径**/
        String graphPath = Params.TRAIN_MODEL_DIR + "new-train-graph/";
        String graphPathJson = Params.TRAIN_MODEL_DIR + "new-train-graph-json/";

        /**先读进语义模型**/
//        semanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json", Params.MODEL_MAIN_FILE_EXT);
        SemanticModel needEliminateSource = sm;
        /**生成train graph文件名**/
        if(graphName == null) {
            graphName = graphPath + sm.getName() + ".Train_" + Index + ".train_" + index + Params.GRAPH_JSON_FILE_EXT;
        }
        if(graphNameJson == null) {
            graphNameJson = graphPathJson + sm.getName() + ".Train_" + Index + ".train_" + index + Params.GRAPH_JSON_FILE_EXT;
        }

        logger.info("======================================================");
        logger.info(needEliminateSource.getName() + "(#attributes:" + needEliminateSource.getColumnNodes().size() + ")");//获取新源的数据节点
        System.out.println(needEliminateSource.getName() + "(#attributes:" + needEliminateSource.getColumnNodes().size() + ")");
        System.out.println(needEliminateSource.getName() + "(#links:" + needEliminateSource.getGraph().edgeSet().size() + ")");
        logger.info("======================================================");
//        SteinerNode steinerNode1 = new SteinerNode("HN868");
//        System.out.println(steinerNode1.getNeighbors());


        List<ColumnNode> steinerNodes = new ArrayList<>(needEliminateSource.getColumnNodes());
        for(ColumnNode i: steinerNodes){
            System.out.println("打印删除nodes前的sm-nodes.name:"+i.getColumnName());
        }
        /**打印每次要删除的节点列表**/
        Set<DefaultLink> eliminationEdges = new HashSet<DefaultLink>();//定义要删除的边列表集合
        Set<Node> eliminationNodes = new HashSet<Node>();//存储语义模型中要删除的节点
        for(ColumnNode i: steinerNodes){
            for(String columnnodename: DELcolumnnodes){
                if(i.getColumnName().equals(columnnodename)){
                    eliminationNodes.add(i);
                }
            }
        }


        for(Node i: eliminationNodes){
            System.out.println("打印要删除的nodes.id:"+i.getId());
        }

        Node Root = null;

        /**获取当前semantic model的root节点  改**/
        Root = getSemanticModelRoot(needEliminateSource);
        System.out.println("Root1:"+Root.getId());

        /**获取当前semantic model的links**/
        List<DefaultLink> SMLinkList = new ArrayList<DefaultLink>();
        for(DefaultLink link: needEliminateSource.getGraph().edgeSet()){
            SMLinkList.add(link);
        }
        System.out.println("SMLinkList.size1:"+SMLinkList.size());

        /**存储当前semantic model的internal nodes及其Outgoing links的数量**/
        //遍历semantic model中的所有node
        for(Node node: needEliminateSource.getInternalNodes()){
            int num = 0;
            for(DefaultLink link: needEliminateSource.getGraph().edgeSet()){
                if(link.getSource().equals(node))
                    num++;
            }
            NodeOutgoingLinksNum.put(node,num);
        }

        for(Node node: NodeOutgoingLinksNum.keySet()){
            System.out.println("NodeOutgoingLinksNum1:" + node.getId()+"||"+NodeOutgoingLinksNum.get(node));
        }

//        System.out.println("未删除节点前的边数目："+needEliminateSource.getGraph().edgeSet().size());
//        System.out.println("未删除节点前的节点数目："+needEliminateSource.getGraph().vertexSet().size());
//        System.out.println(needEliminateSource.getColumnNodes().size());

        Map<Node,Integer> Nodeoutgoinglinksnum = new HashMap<Node,Integer>();
        Nodeoutgoinglinksnum = NodeOutgoingLinksNum;
//        for(Node node: Nodeoutgoinglinksnum.keySet()){
//            System.out.println("NodeOutgoingLinksNum2:" + node.getId()+"||"+Nodeoutgoinglinksnum.get(node));
//        }
        Map<Node,Integer> PathNodeNum = new LinkedHashMap<Node,Integer>();

        /**改**/
        for(Node columnnode: eliminationNodes){
            System.out.println("打印要删除的节点2:"+columnnode.getId());
            //找到Root到i的path
            connectedPathsNode = new ArrayList<List<Node>>();
            findAllPathNode(SMLinkList,Root.getId(),columnnode.getId(),100);
            System.out.println("connectedPathsNode2:"+connectedPathsNode.size());//保存root到待删除节点之间的节点

            for(int k=0;k<connectedPathsNode.get(0).size()-1;k++){
                System.out.println("pathnode1:"+connectedPathsNode.get(0).get(k).getId());
                //如果没有node,则添加该node及其value
                if(!(PathNodeNum.keySet().contains(connectedPathsNode.get(0).get(k)))){
                    PathNodeNum.put(connectedPathsNode.get(0).get(k),1);
                }
                //如果有node,则只需要改变其value
                else{
                    int path_node_num;
                    path_node_num = PathNodeNum.get(connectedPathsNode.get(0).get(k))+1;
                    PathNodeNum.put(connectedPathsNode.get(0).get(k),path_node_num);
                }
            }
        }

        for(Node node: PathNodeNum.keySet()){
            System.out.println("PathNodeNum:" + node.getId()+"||"+PathNodeNum.get(node));
        }

        //如果合并得到的PathNodeNum的第一个元素值大于1,则需要对PathNodeNum中元素的value进行更改
        int changeindex = 0;
        if(PathNodeNum.values().stream().findFirst().get()>1){
            int firstpathnodenum = PathNodeNum.values().stream().findFirst().get();
            System.out.println("PathNodeNum.keySet:"+PathNodeNum.keySet());
            //遍历PathNodeNum中的元素,查看其对应的value是否与firstpathnodenum相等,找到最后一个与firstpathnodenum相等的node
            for(Node node: PathNodeNum.keySet()){
                if(PathNodeNum.get(node) == firstpathnodenum){
                    changeindex++;
                }
                else break;
            }
        }
        System.out.println("changeindex:"+changeindex);
        int node_num;
        if(changeindex > 0){
            for(Node node: PathNodeNum.keySet()){
                changeindex--;
                if(changeindex > 0){
                    node_num = PathNodeNum.get(node)-1;
                    PathNodeNum.put(node,node_num);
                }
            }
        }

        for(Node node: PathNodeNum.keySet()){
            System.out.println("PathNodeNum3:" + node.getId()+"||"+PathNodeNum.get(node));
        }

        //改变Nodeoutgoinglinksnum中node的value
        int node_new_num;
        //遍历PathNodeNum
        for(Node node: PathNodeNum.keySet()){
            for(Node nodemapoutgoingnum: Nodeoutgoinglinksnum.keySet()){
                if(node.equals(nodemapoutgoingnum)){
                    node_new_num = Nodeoutgoinglinksnum.get(nodemapoutgoingnum)-PathNodeNum.get(node);
                    Nodeoutgoinglinksnum.put(nodemapoutgoingnum,node_new_num);
                    break;
                }
            }
        }

        for(Node node: Nodeoutgoinglinksnum.keySet()){
            if(Nodeoutgoinglinksnum.get(node) == 0){
                eliminationNodes.add(node);
            }
            System.out.println("Nodeoutgoinglinksnum4:" + node.getId()+"||"+Nodeoutgoinglinksnum.get(node));
        }

        for(Node node: eliminationNodes) {
            for (DefaultLink link : needEliminateSource.getGraph().edgeSet()) {
                if (link.getTarget().equals(node)) {
                    eliminationEdges.add(link);
                }
            }
        }

        /**删除节点**/
        for(Node needeliminationNodes: eliminationNodes) {
            needEliminateSource.getGraph().removeVertex(needeliminationNodes);
        }
        /**删除边**/
        for(DefaultLink link: eliminationEdges){
            if(link instanceof LabeledLink) {
                needEliminateSource.getGraph().removeEdge((LabeledLink) link);
            }
        }


        Set<DefaultLink> DefaultLinks = new HashSet<DefaultLink>();
        for(LabeledLink link: needEliminateSource.getGraph().edgeSet()){
            DefaultLinks.add(link);
        }

        /**存储类节点**/
        Set<InternalNode> InternalNodes = new HashSet<InternalNode>();
        for(InternalNode node: needEliminateSource.getInternalNodes()){
            InternalNodes.add(node);
        }
        /**存储数据节点**/
        List<ColumnNode> columnNodes1 = needEliminateSource.getColumnNodes();
        List<Node> Nodes = new LinkedList<Node>(columnNodes1);


        /**保存语义模型**/
        try {
////                GraphUtil.exportJson(modelLearningGraph.getGraphBuilder().getGraph(), graphName + ".json",true,true);
//            GraphUtil.exportJson(needEliminateSource.getGraph(), graphName + ".json",true,true);
            DirectedWeightedMultigraph needEliminateSourceJson = needEliminateSource.getGraph();
            GraphUtil.exportJson(needEliminateSourceJson, graphNameJson + ".json",true,true);
//            /**Visualize the merged graph (model learning graph). 18 June 2018.**/
//            for (Node node : modelLearner.graphBuilder.getGraph().vertexSet()) {
//                System.out.println(node);
//            }
//
//
            GraphVizUtil.exportSemanticModelToGraphviz(needEliminateSource,GraphVizLabelType.LocalId,
                    GraphVizLabelType.LocalUri,true,true,graphName + ".dot");
//
        } catch (Exception e) {
            e.printStackTrace();
        }

        System.out.println("打印图信息-------");
        System.out.println("# of nodes in model learning graph: " + needEliminateSource.getGraph().vertexSet().size());
        System.out.println("# of links in model learning graph: " +needEliminateSource.getGraph().edgeSet().size());


        return needEliminateSource;
    }

    public static void main(String[] args) throws Exception {
        List<SemanticModel> FinalNewStartStatesSemanticModels = null;
//        GenerateNewSM(0);
//        System.out.println(correctc);
//        EliminatedSemanticModels(0,0, correcta);
//        getStartStatesSemanticModel(0);//依据原始语义模型来生成初始搜索语义模型
//        FinalNewStartStatesSemanticModels = getNewStartStatesSemanticModel(3);//依据去除不正确标记的语义模型来生成初始搜索语义模型   ////////5.18
        FinalNewStartStatesSemanticModels = getNewStartStatesSemanticModel1(26);//5.18 added
//        GenerateNewSM1(2);//5.18 added

        /**Judge函数测试**/
//        Set<Set<String>> A = new HashSet<Set<String>>();
//        Set<String> B = new HashSet<String>();
//        Set<String> C = new HashSet<String>();
//        Set<String> D = new HashSet<String>();
//        Set<String> E = new HashSet<String>();
//        C.add("Dated");
//        C.add("Begin Date");
//        D.add("End Date");
//        D.add("Dated");
//        A.add(C);
//        A.add(D);
//        B.add("Begin Date");
//        B.add("Dated");
//        E.add("Dated");
//        E.add("Attribution");
//        System.out.println(C);
//        System.out.println(D);
//        System.out.println(A);
//        System.out.println(B);
//        System.out.println(E);
//        Boolean flag;
//        flag = Judge(A,E);
//        System.out.println("flag:" + flag);
        /**Judge函数测试**/
    }
}
