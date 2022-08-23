package edu.isi.karma.research.modeling;

import com.alibaba.fastjson.JSON;
import com.alibaba.fastjson.JSONObject;
import com.google.gson.stream.JsonReader;
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
import jnr.ffi.annotations.In;
import org.apache.commons.io.FileUtils;
import org.apache.commons.lang.ArrayUtils;
import org.apache.commons.lang.StringUtils;
import org.apache.hadoop.util.hash.Hash;
import org.apache.poi.util.SystemOutLogger;
import org.ejml.simple.SimpleMatrix;
import org.jgrapht.EdgeFactory;
import org.jgrapht.graph.AsUndirectedGraph;
import org.jgrapht.graph.DirectedWeightedMultigraph;
import org.jgrapht.graph.WeightedMultigraph;
import org.mortbay.xml.XmlParser;
import org.python.core.PyFunction;
import org.python.core.PyInteger;
import org.python.core.PyList;
import org.python.google.common.collect.Lists;
import org.python.util.PythonInterpreter;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.*;
import java.math.BigDecimal;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.text.DecimalFormat;
import java.util.*;

import static edu.isi.karma.research.modeling.EliminateNodes.*;
import static edu.isi.karma.research.modeling.ModelLearner_KnownModels4.getIntegrationGraph;
import static edu.isi.karma.research.modeling.ModelLearner_KnownModels4.getIntegrationGraphPrediction;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;


public class SearchForSemanticModels {

    private static Logger logger = LoggerFactory.getLogger(SearchForSemanticModels.class);
    private static List<SemanticModel> SemanticModels = null;
    private static DirectedWeightedMultigraph<Node, DefaultLink> StartStateGraph = null;
    private static DirectedWeightedMultigraph<Node, LabeledLink> NewStartStateGraph = null;

    private static SemanticModel StartStateSemanticModel = null;
    private static List<LabeledLink> labeledLinks = new LinkedList<LabeledLink>();
    private static List<DefaultLink> labeledLinks1 = new LinkedList<DefaultLink>();
    private static List<List<String>> connectedPaths;
    private static List<List<Node>> connectedPathsNode;
    private static Set<List<Node>> connectedPathsNode_ANs_tree;//改成Set
    private static Set<List<DefaultLink>> connectedPathsLink_ANs_tree;
    private static Set<List<Node>> connectedPathsNode_ANs_mntPt;//改成Set
    private static Set<List<DefaultLink>> connectedPathsLink_ANs_mntPt;//改成Set
    private static List<List<DefaultLink>> connectedPathsLink;

    //定义当前路径
    private static List<String> nowPath = new ArrayList<String>();
    private static List<Node> nowPathNode = new ArrayList<Node>();
    private static List<DefaultLink> nowPathLink = new ArrayList<DefaultLink>();
    private static int Beam_Search = 0;
    private static int Beam_Search_Index = 0;
    private static int TransitionFunctionIndex = 0;
    private static int NegExmplesIndex = 0;

    /**MergeIntoTree1*/
    private static int MergeIntoTreenumber = 0;//文件名序号

    private static String sm_embedding_joint_filePath = "F:\\Cross-Modal Retrieval Model IN Linux\\Cross-Modal Retrieval Model Triple Loss\\sm_embedding_joint.txt";

    private static List<SemanticType> getCandidateSteinerSets(ColumnNode steinerNode, boolean useCorrectTypes, int numberOfCandidates) {

        if (steinerNode == null)
            return null;

        List<SemanticType> candidateSemanticTypes = null;

        if (!useCorrectTypes) {
            System.out.println("!useCorrectTypes");
            candidateSemanticTypes = steinerNode.getTopKLearnedSemanticTypes(numberOfCandidates);//获得斯坦纳树节点的前numberOfCandidates个候选语义模型
            if(candidateSemanticTypes.size() == 0){
                candidateSemanticTypes = steinerNode.getUserSemanticTypes();
            }
        } else if (steinerNode.getSemanticTypeStatus() == ColumnSemanticTypeStatus.UserAssigned) {
            System.out.println("ColumnSemanticTypeStatus.UserAssigned");
            candidateSemanticTypes = steinerNode.getUserSemanticTypes();
        }

        if (candidateSemanticTypes == null) {
            logger.error("No candidate semantic type found for the column " + steinerNode.getColumnName());
            System.out.println("No candidate semantic type found for the column " + steinerNode.getColumnName());
            return null;
        }

        return candidateSemanticTypes;
    }


    private static EdgeFactory<Node,LabeledLink> edgeFactory = new EdgeFactory<Node, LabeledLink>() {
        @Override
        public LabeledLink createEdge(Node sourceVertex, Node targetVertex) {
            return null;
        }
    };

    /**5.16  删除指定文件夹内容**/
    public static void RemoveDir(File dir){
        File[] files = dir.listFiles();
        if (files != null) {
            for (File file : files) {
                if (file.isDirectory()) {
                    RemoveDir(file);
                } else {
                    if (!file.delete()) {
                        logger.info("删除条形码文件{}失败", file.getName());
                    }
                }
            }
        }
    }


    /**5.14  根据得分升序排序 返回beam_size个SemanticModels**/
    public static Map SortMap(Map<SemanticModel, Double> map,Integer beam_size){
        //获取entrySet
        Set<Map.Entry<SemanticModel,Double>> mapEntries = map.entrySet();
        //使用链表来对集合进行排序 使用LinkedList 利于传入元素
        List<Map.Entry<SemanticModel,Double>> result = new LinkedList<>(mapEntries);
        //自定义比较器来比较链表中的元素
        Collections.sort(result, new Comparator<Map.Entry<SemanticModel,Double>>() {
            //基于entry的值（Entry.getValue()），来排序链表
            public int compare(Map.Entry<SemanticModel, Double> o1, Map.Entry<SemanticModel, Double> o2) {
                return o1.getValue().compareTo(o2.getValue());
            }
        });
        //将排好序的存入到LinkedHashMap(可保持顺序)中，需要存储键和值信息对到新的映射中。
        Integer sort = 1;
        Map<SemanticModel, Double> LinkMap = new LinkedHashMap<>();
        for (Map.Entry<SemanticModel, Double> newEntry : result) {
            // 取出排名前beam_size的值
            if ((sort <= beam_size)&&(newEntry.getValue()<0.95)) {
                LinkMap.put(newEntry.getKey(), newEntry.getValue());
                ++sort;
            }
        }
        return LinkMap;
    }

    /**5.20 根据得分降序排序  返回beam_size个SemanticModels**/
    public static Map DescendSortMap(Map<SemanticModel, Float> map,Integer beam_size){
        //获取entrySet
        Set<Map.Entry<SemanticModel,Float>> mapEntries = map.entrySet();
        //使用链表来对集合进行排序 使用LinkedList 利于传入元素
        List<Map.Entry<SemanticModel,Float>> result = new LinkedList<>(mapEntries);
        //自定义比较器来比较链表中的元素
        Collections.sort(result, new Comparator<Map.Entry<SemanticModel,Float>>() {
            //基于entry的值（Entry.getValue()），来排序链表
            public int compare(Map.Entry<SemanticModel, Float> o1, Map.Entry<SemanticModel, Float> o2) {
                return o1.getValue().compareTo(o2.getValue());
            }
        });
        //将排好序的存入到LinkedHashMap(可保持顺序)中，需要存储键和值信息对到新的映射中。
        Integer sort = 1;
        Map<SemanticModel, Float> LinkMap = new LinkedHashMap<>();
        for (Map.Entry<SemanticModel, Float> newEntry : result) {
            // 取出排名前beam_size的值
            if (sort <= beam_size) {
                LinkMap.put(newEntry.getKey(), newEntry.getValue());
                ++sort;
            }
        }
        return LinkMap;
    }

    /**5.20 针对某一data source预测生成Semantic Models**/
    public static List<SemanticModel> PredictSemanticModels(int SourceSemanticModelIndex) throws Exception{
        List<ColumnNode> Columnnodes = new LinkedList<ColumnNode>();//原始正确语义模型的Source Attributions集
        DirectedWeightedMultigraph<Node, DefaultLink> IntegrationGraph = null;//集成图
        List<SemanticModel> StartSearchStates = new LinkedList<SemanticModel>();//原始正确语义模型在执行Elimination操作后获得的初始Search States集
        SemanticModel StartSearchState = null;
        List<SemanticModel> PredictSemanticModels = new ArrayList<SemanticModel>();//生成negative examples
        JSONObject jsonObject = ReadEmbeddingJson(Params.ROOT_DIR +"final_embedding_correct.json");//获取entire_embedding.json

//        //删除指定文件夹内容
//        File dir3=new File(Params.ROOT_DIR+"prediction-semanticmodels");
//        RemoveDir(dir3);
//        File dir4=new File(Params.ROOT_DIR+"prediction-semanticmodels-json");
//        RemoveDir(dir4);

        /**获取Source Semantic Model**/
        if(SemanticModels == null) {
            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
        }
        SemanticModel SourceSemanticModel = SemanticModels.get(SourceSemanticModelIndex);

        /**获取integration graph**/
        Integer[] AllSMIndex = new Integer[]{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28};
        AllSMIndex = (Integer[]) ArrayUtils.remove(AllSMIndex, SourceSemanticModelIndex);
        System.out.println("开始计时");
        long start = System.currentTimeMillis();
        IntegrationGraph = getIntegrationGraphPrediction(SourceSemanticModelIndex, AllSMIndex);
        System.out.println("IntegrationGraph.links.size:" + IntegrationGraph.edgeSet().size());
        System.out.println("IntegrationGraph.nodes.size:" + IntegrationGraph.vertexSet().size());
        /**测试是否存在某一条边 source2**/
//        int isexit = 0;
//        for(DefaultLink link: IntegrationGraph.edgeSet()){
//            if(link.getSource().getId().equals("http://erlangen-crm.org/current/E22_Man-Made_Object")&&(link.getTarget().getId().equals("http://erlangen-crm.org/current/E31_Document1"))){
//                isexit = 1;
//                System.out.println("能找到link");
//                System.out.println("输出link.getUri:" + link.getUri());
////                break;
//            }
////            if((link.getUri().equals("http://erlangen-crm.org/current/P70i_is_documented_in"))){
////                isexit = 1;
////                System.out.println("能找到link");
////                break;
////            }
//        }
//        if(isexit == 1){
//            System.out.println("能找到link");
//        }
//        else{
//            System.out.println("找不到link");
//        }
        /**测试是否存在某一条边 source2**/

        /**查找Begin Date在integration graph中的祖先节点**/
//        Set<Node> Begin_Date_AncestorRoots = new HashSet<Node>();
//        for(ColumnNode node: SourceSemanticModel.getColumnNodes()) {
//            if(node.getColumnName().equals("Begin Date")) {
//                Begin_Date_AncestorRoots = findAncestorNodesInIntegrationGraph(IntegrationGraph,node);
//                break;
//            }
//        }
//        for(Node node:Begin_Date_AncestorRoots){
//            System.out.println("输出Begin_Date的祖先节点" + node.getId());
//        }
        /**查找Begin Date在integration graph中的祖先节点**/

        /**查找http://erlangen-crm.org/current/E67_Birth1到http://erlangen-crm.org/current/E52_Time-Span4**/
//        Set<Node> E52_Time_Span_AncestorRoots = new HashSet<Node>();
//        for(Node node: IntegrationGraph.vertexSet()) {
//            if(node.getId().equals("http://erlangen-crm.org/current/E52_Time-Span4")) {
//                E52_Time_Span_AncestorRoots = findAncestorNodesInIntegrationGraph(IntegrationGraph,node);
//                break;
//            }
//        }
//        //查看Begin_Date_AncestorRoots中是否有http://erlangen-crm.org/current/E21_Person1
//        for(Node node: E52_Time_Span_AncestorRoots){
//            if(node.getId().equals("http://erlangen-crm.org/current/E67_Birth1")){
//                System.out.println("E52_Time-Span4的祖先节点中包含E67_Birth1");
//            }
//        }
//        System.out.println("Begin_Date_AncestorRoots.size:" + E52_Time_Span_AncestorRoots.size());
        /**查找http://erlangen-crm.org/current/E21_Person1到Begin Date**/


        /**获取数据源属性名称列表**/
//        List<String> AttrName = new LinkedList<String>(){{
////            add("name");
////            add("biography");
////            add("birthDate");
////            add("Birth_URI");
////            add("deathDate");
////            add("Death_URI");
//            /**替换前**/
////            add("Attribution");
////            add("Actor_URI");
////            add("Birth_URI");
////            add("Death_URI");
////            add("Begin Date");
////            add("End Date");
////            add("Title");
////            add("Dated");
////            add("Medium");
////            add("Dimensions");
////            add("production_id");
////            add("Object_URI");
//            /**替换后**/
//            add("Attribution");
//            add("Actor_URI");
//            add("Begin Date");
//            add("Birth_URI");
//            add("End Date");
//            add("Death_URI");
//            add("Title");
//            add("Dated");
//            add("Medium");
//            add("Dimensions");
//            add("production_id");
//            add("Object_URI");
//            /**7.11 读入attribution order**/
//
//        }};
        /**7.12 读取attribution order.txt**/
        List<String> AttrName = ReadAttributionOrder(Params.ROOT_DIR +"AttributionOrder.txt").get(SourceSemanticModelIndex);
//        System.out.println("AttrName:" + AttrName);

        /**获取source attributions**/
        for(int i=0;i<AttrName.size();i++){
            for(ColumnNode columnnode: SourceSemanticModel.getColumnNodes()){
                if(AttrName.get(i).equals(columnnode.getColumnName())){
                    Columnnodes.add(columnnode);
                    break;
                }
            }
        }

        System.out.println("Columnnodes.size:" + Columnnodes.size());
//        for(ColumnNode node:Columnnodes){
//            System.out.println("Columnnodes.name:" + node.getColumnName());
//        }

        /**获取初始Semantic Model以启动Beam Search**/
        //首先创建一个空图
        DirectedWeightedMultigraph<Node, LabeledLink> EmptyGraph = new DirectedWeightedMultigraph<Node, LabeledLink>(LabeledLink.class);
        System.out.println("未添加前EmptyGraph.vertexSet.size:"+EmptyGraph.vertexSet().size());
        System.out.println("未添加前EmptyGraph.edgeSet.size:"+EmptyGraph.edgeSet().size());
        //在空图中添加第一个columnnode及其class node和link
        List<ColumnNode> emptygraph_addedcolumnNodes = new LinkedList<ColumnNode>();
        emptygraph_addedcolumnNodes.add(Columnnodes.get(0));
        Map<ColumnNode, ColumnNode> mappingToSourceColumns = new HashMap<ColumnNode, ColumnNode>();
        for(ColumnNode node: Columnnodes){
            mappingToSourceColumns.put(node,node);
        }

        //获取待添加columnnnode的correct semantic type
        List<SemanticType> CorrectSemanticTypes_ACN = getCandidateSteinerSets(emptygraph_addedcolumnNodes.get(0), true, 4);
//        System.out.println("输出CorrectSemanticTypes_ACN:" + CorrectSemanticTypes_ACN);
//        DefaultLink correctlink = new DefaultLink();
        List<DefaultLink> correctlink_list = new ArrayList<DefaultLink>();
        for (DefaultLink link : IntegrationGraph.edgeSet()) {
            if ((link.getSource().getUri().equals(CorrectSemanticTypes_ACN.get(0).getDomain().getUri())) && (link.getUri().equals(CorrectSemanticTypes_ACN.get(0).getType().getUri()))&&(link.getTarget().getId().equals(emptygraph_addedcolumnNodes.get(0).getId()))) {
//                correctlink = link;
                correctlink_list.add(link);
                System.out.println("输出correctlink:" + link.getSource().getId());
//                break;
            }
        }
        System.out.println("输出correctlink_list.size:" + correctlink_list.size());
        List<SemanticModel> StartSearchStateList = new ArrayList<SemanticModel>();
        //生成所有候选的startsearchstate
        for(DefaultLink correctlink: correctlink_list) {
            EmptyGraph = new DirectedWeightedMultigraph<Node, LabeledLink>(LabeledLink.class);
            System.out.println("输出未添加任何节点前EmptyGraph.vertexSet.size:" + EmptyGraph.vertexSet().size());
            System.out.println("输出未添加任何节点前EmptyGraph.edgeSet.size:" + EmptyGraph.edgeSet().size());
            String addedlinkId = LinkIdFactory.getLinkId(correctlink.getId(), correctlink.getSource().getId(), correctlink.getId());
            LabeledLink addedlink = new DataPropertyLink(addedlinkId, new Label(correctlink.getUri()));
            //添加columnnode及其class node和link
            EmptyGraph.addVertex(emptygraph_addedcolumnNodes.get(0));//添加columnnode
            EmptyGraph.addVertex(correctlink.getSource());//添加class node
            EmptyGraph.addEdge(correctlink.getSource(), emptygraph_addedcolumnNodes.get(0), addedlink);//添加link
            System.out.println("初始状态EmptyGraph.vertexSet.size:" + EmptyGraph.vertexSet().size());
            System.out.println("初始状态EmptyGraph.edgeSet.size:" + EmptyGraph.edgeSet().size());

            //创建初始StartSearchState(即EmptyGraph->Start Semantic Model)
            StartSearchState = new SemanticModel(new RandomGUID().toString(), EmptyGraph, emptygraph_addedcolumnNodes, mappingToSourceColumns);
            System.out.println("StartSearchState.vertexSet.size:" + StartSearchState.getGraph().vertexSet().size());
            System.out.println("StartSearchState.edgeSet.size:" + StartSearchState.getGraph().edgeSet().size());
//        System.out.println("StartSearchState.columnname.size:"+StartSearchState.getGraph().edgeSet().size());
//        System.out.println("StartSearchState.columnname:"+StartSearchState.getColumnNodes().get(0).getColumnName());
            StartSearchStateList.add(StartSearchState);
        }
        System.out.println("输出StartSearchStateList.size:" + StartSearchStateList.size());


        //以StartSearchState为初始状态 调用BeamSearchPrediction 为其生成后续正确的Semantic Models
        NegExmplesIndex = 0;
//        /**保存dot文件**/
//        GraphVizUtil.exportSemanticModelToGraphviz(StartSearchState, GraphVizLabelType.LocalId,
//                GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\next-state-graph\\" + "next_state_IntoMount" + Beam_Search + "_" + MergeIntoTreenumber + ".graph.json" + ".dot");
        List<ColumnNode> AddedColNodes = new LinkedList<ColumnNode>();
        AddedColNodes = Columnnodes;
        AddedColNodes.remove(Columnnodes.get(0));
        for(ColumnNode node: AddedColNodes){
            System.out.println("AddedColNodes.name:"+node.getColumnName());
        }

        /**获取correct sub source embedding index**/
        List<List<String>> combine_results = CombineOrder(AttrName);
        Integer[] sub_source_embedding_index = new Integer[AttrName.size()-1];
        int index = 0;
        for(int i=0;i<combine_results.size();i++){
            if(combine_results.get(i).contains(AttrName.get(0))){
                sub_source_embedding_index[index] = i+1;
                ++index;
            }
        }
        //读取correct sub source embedding 并将其存入列表中
        String sub_source_embedding_pathname = null;
        List<String> sub_source_embedding_list = new ArrayList<String>();
        for(int i=0;i<sub_source_embedding_index.length;i++) {
            if((SourceSemanticModelIndex+1)<10) {
                sub_source_embedding_pathname = "F:\\EmbdiForSourcesEmbeddings\\source20220314-embedding\\s0"+(SourceSemanticModelIndex+1)+"\\embeddings\\s0"+(SourceSemanticModelIndex+1)+"_Sub"+sub_source_embedding_index[i]+"-embedding.txt";
            }
            else{
                sub_source_embedding_pathname = "F:\\EmbdiForSourcesEmbeddings\\source20220314-embedding\\s"+(SourceSemanticModelIndex+1)+"\\embeddings\\s"+(SourceSemanticModelIndex+1)+"_Sub"+sub_source_embedding_index[i]+"-embedding.txt";
            }
            sub_source_embedding_list.addAll(ReadTxt(sub_source_embedding_pathname));
            System.out.println("输出sub_source_embedding_index:" + sub_source_embedding_index[i]);
//            System.out.println("输出sub_source_embedding_pathname:" + sub_source_embedding_pathname);
        }
//        System.out.println("输出sub_source_embedding_list:" + sub_source_embedding_list.get(0).getClass());


        PredictSemanticModels = BeamSearchPrediction(SourceSemanticModel,StartSearchStateList,IntegrationGraph,AddedColNodes,sub_source_embedding_list,jsonObject);


        long elapsedTimeMillis = System.currentTimeMillis() - start;
        float elapsedTimeSec = elapsedTimeMillis/1000F;

        System.out.println("Predict time: " + elapsedTimeSec);

        System.out.println("PredictSemanticModels.size:"+PredictSemanticModels.size());
        System.out.println("AllSMIndex:" + Arrays.toString(AllSMIndex));
        return null;
    }

    public static List<SemanticModel> BeamSearchPrediction(SemanticModel SourceSemanticModel, List<SemanticModel> StartSearchStates, DirectedWeightedMultigraph<Node, DefaultLink> IntegrationGraph, List<ColumnNode> AddedColNodes, List<String> sub_source_embedding_list,JSONObject jsonObject) throws Exception{
//        List<SemanticModel> StartSearchStates = new LinkedList<SemanticModel>();//原始正确语义模型在执行Elimination操作后获得的初始Search States集
        List<SemanticModel> SearchStates = new ArrayList<SemanticModel>();
        List<SemanticModel> NextStates_Sum = new ArrayList<SemanticModel>();
        List<SemanticModel> NextStates_Total = new ArrayList<SemanticModel>();
        List<SemanticModel> FinalSemanticModels = new ArrayList<SemanticModel>();
        Map<SemanticModel,Float> State_Value = new HashMap<SemanticModel,Float>();
        ModelEvaluation Sim_Value = null;
        SortableSemanticModel sortable_sm = null;
        Map<SemanticModel,Double> Sorted_State_Value = new HashMap<SemanticModel,Double>();
        int AddedAttributionsNum = 0;

        //删除指定文件夹内容
        File dir1=new File(Params.ROOT_DIR+"next-state-graph");
        RemoveDir(dir1);
        File dir2=new File(Params.ROOT_DIR+"next-search-states");
        RemoveDir(dir2);
//        File dir3=new File("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples");
//        RemoveDir(dir3);

        /**当初始搜索状态为空时**/
        SearchStates.addAll(StartSearchStates);
        System.out.println("SearchStates的大小:" + SearchStates.size());
        /**获取初始Search State要添加的Attributions的个数**/
        AddedAttributionsNum = AddedColNodes.size();
//        for(ColumnNode node: AddedColNodes){
//            System.out.println("输出BeamSearchPredict中的columnnode.name:" + node.getColumnName());
//        }
        System.out.println("AddedAttributionsNum:"+AddedAttributionsNum);
        //当SearchStates中没有元素时 则停止BeamSearch  否则继续BeamSearch  生成下一步更好的结果
        ColumnNode addednode = null;
        int addedindex = 0;
        String sub_source_embedding = null;
        BigDecimal[] sm_embedding_array;//保存最终sm embedding
        String sm_embedding = null;
        float score = 0;
        int best_sm_index = 0;
        List<SemanticModel> SearchStates_temp = new ArrayList<SemanticModel>();

        /**7.22 设置调用python model的参数**/
//        String pyPath = "F:\\Cross-Modal Retrieval Model IN Linux\\Cross-Modal Retrieval Model Triple Loss\\my_predict_triple.py"; //python文件路径
//        String pyEnvironment = "C:\\ProgramData\\Anaconda3\\python.exe";
//        PythonRun pythonRun = new PythonRun();
//        pythonRun.setEnvironment(pyEnvironment);
////        pythonRun.setRoot("F:\\Cross-Modal Retrieval Model IN Linux\\Cross-Modal Retrieval Model Triple Loss");
//        pythonRun.setCache("F:\\Cross-Modal Retrieval Model IN Linux\\Cross-Modal Retrieval Model Triple Loss\\");
//        PythonRun.AResult aResult = pythonRun.asyncRun(pyPath);
        /**7.22 设置调用python model的参数**/

        float score_time  = 0;
        while(AddedColNodes.size()>0){
            /**7.12 传入correct sub source embeddings  每次读入一个correct sub source embedding**/
            sub_source_embedding = sub_source_embedding_list.get(addedindex);//source_embedding
            System.out.println("输出sub_source_embedding:" + sub_source_embedding);
//            //每次按顺序只添加一个attribution
            addednode = AddedColNodes.get(0);
            Beam_Search++;
            System.out.println("添加一个attribution时开启的一次循环");
            System.out.println("循环开始时SearchStates大小:" + SearchStates.size());
            FinalSemanticModels = new ArrayList<SemanticModel>();
            NextStates_Total = new ArrayList<SemanticModel>();
            System.out.println("循环开始时NextStates_Total大小:" + NextStates_Total.size());
            //遍历SearchStates中的search state 调用TransitionFunctionPrediction1 为其生成添加一个节点之后的next search states集合
            System.out.println("输出当前循环要添加的columnnode.name:" + AddedColNodes.get(0).getColumnName());
            for(int i=0;i<SearchStates.size();i++) {
                TransitionFunctionIndex++;
                NextStates_Sum = TransitionFunctionPrediction1(SearchStates.get(i), IntegrationGraph, addednode);
                if(NextStates_Sum.size()>0) {
                    System.out.println("每执行一次TransitionFunctionPrediction1后的nextsearchstates个数:" + NextStates_Sum.size());
                    NextStates_Total.addAll(NextStates_Sum);
                }
            }
            //如果添加第一个node时没有生成候选语义模型 则删除初始状态中
            AddedColNodes.remove(addednode);//从添加集合中删除已添加的node
            //此时NextStates_Total是添加一个attribution后的所有候选semantic models的列表集
            /**7.23  更换打分方式**/
            StringBuffer sm_string_joint = new StringBuffer();
            /**7.11 替换打分函数**/
            SearchStates_temp = new ArrayList<SemanticModel>();
            if(NextStates_Total.size()>0){
                State_Value = new HashMap<SemanticModel,Float>();
                //遍历添加一个node之后的所有NextStates 计算其与CorrectSemanticModel的值
                int index = 0;
                for(SemanticModel sm: NextStates_Total){
                    /**7.12 计算sm的embedding  BigDecimal[]数组**/
//                    sortable_sm = new SortableSemanticModel(sm,true);
//                    Sim_Value = sortable_sm.evaluate(SourceSemanticModel);
                    System.out.println("计算开始-----------");
                    sm_embedding_array = SemanticModelEmbedding(jsonObject,sm);
                    sm_embedding = BigDecimalArray2String(sm_embedding_array);//sm_embedding
                    sm_string_joint.append(sm_embedding);
                    if(index < NextStates_Total.size()-1){
                        sm_string_joint.append(";");
                    }
                    ++index;
//                    long predict_start = System.currentTimeMillis();
//                    score = Float.parseFloat(GetScoreWithCrossModalModel(sub_source_embedding, sm_embedding));
//                    long predict_elapsedTimeMillis = System.currentTimeMillis() - predict_start;
//                    float predict_elapsedTimeSec = predict_elapsedTimeMillis/1000F;
//                    score_time = score_time + predict_elapsedTimeSec;
//                    System.out.println("Predict beam search time: " + predict_elapsedTimeSec);
//                    System.out.println("计算完成-----------");
//                    State_Value.put(sm,score);
                }
                saveASFileWrite(sm_string_joint.toString());
//                System.out.println("每添加一个node后State_Value的大小:"+State_Value.size());
//                Sorted_State_Value = DescendSortMap(State_Value,1);
//                System.out.println("每添加一个node后Sorted_State_Value的大小:"+Sorted_State_Value.size());
                /**7.23  NewGetScoreWithCrossModalModel**/
//                best_sm_index = Integer.parseInt(NewGetScoreWithCrossModalModel(sub_source_embedding,sm_string_joint.toString()));

                long predict_start = System.currentTimeMillis();
                best_sm_index = Integer.parseInt(NewGetScoreWithCrossModalModel(sub_source_embedding,"F:\\Cross-Modal Retrieval Model IN Linux\\Cross-Modal Retrieval Model Triple Loss\\sm_embedding_joint.txt"));
                long predict_elapsedTimeMillis = System.currentTimeMillis() - predict_start;
                float predict_elapsedTimeSec = predict_elapsedTimeMillis/1000F;
                score_time = score_time + predict_elapsedTimeSec;
                System.out.println("Predict beam search time: " + predict_elapsedTimeSec);

                SearchStates = new ArrayList<SemanticModel>();//清空SearchStates列表
//                SearchStates.addAll(Sorted_State_Value.keySet());//添加beam_size个最好的下一状态集合
                SearchStates.add(NextStates_Total.get(best_sm_index));
//                System.out.println("循环添加一个node后SearchStates大小:"+SearchStates.size());
                if(SearchStates.size()>0){
                    FinalSemanticModels.addAll(SearchStates);
                }
                System.out.println("当前状态下FinalSemanticModels大小:"+FinalSemanticModels.size());
            }
            else if((NextStates_Total.size() == 0)&&(AddedColNodes.size()>0)){
                SearchStates_temp.addAll(SearchStates);
                SearchStates = new ArrayList<SemanticModel>();
                SearchStates.addAll(SearchStates_temp);
            }
            else{
//                SearchStates = new ArrayList<SemanticModel>();//清空SearchStates列表
                FinalSemanticModels.addAll(SearchStates);
            }

            int index=0;
            if(FinalSemanticModels.size()>0){
                for(SemanticModel sm: FinalSemanticModels){
                    index++;
                    GraphUtil.exportJson1(sm.getGraph(), Params.ROOT_DIR+"prediction-semanticmodels-json\\" + NegExmplesIndex + "_" + Beam_Search + "_" + index + ".graph" + ".json",true,true);
                    GraphVizUtil.exportSemanticModelToGraphviz(sm, GraphVizLabelType.LocalId,
                            GraphVizLabelType.LocalUri, false, false, Params.ROOT_DIR+"prediction-semanticmodels\\" + NegExmplesIndex + "_" + Beam_Search + "_" + index + ".graph.json" + ".dot");
                }
            }
            ++addedindex;
        }
        System.out.println("score time: " + score_time);

//        //当SearchStates中的元素为0时 则停止BeamSearch  否则继续BeamSearch  生成下一步更好的结果
////        int AddedAttributionsNum1 = 1;
//
////        while(AddedAttributionsNum > 0){
////            //每次只添加一个attribution
////            Beam_Search++;
////            System.out.println("一次循环");
////            System.out.println("循环的SearchStates大小:" + SearchStates.size());
////            FinalSemanticModels = new ArrayList<SemanticModel>();
//////            SearchStates_Tmp.addAll(SearchStates);
//////            System.out.println("SearchStates_Tmp中元素个数:"+SearchStates_Tmp.size());
////            NextStates_Total = new ArrayList<SemanticModel>();
////            System.out.println("循环的NextStates_Total大小:" + NextStates_Total.size());
////            //遍历SearchStates中的search state 调用TransitionFunction2 为其生成添加一个节点之后的next search states集合
////            for(int i=0;i<SearchStates.size();i++) {
////                TransitionFunctionIndex++;
////                NextStates_Sum = TransitionFunctionPrediction(SearchStates.get(i), IntegrationGraph, Columnnodes);
////                if(NextStates_Sum.size()>0) {
////                    System.out.println("每执行一次TransitionFunction2后的nextsearchstates个数:" + NextStates_Sum.size());
////                    NextStates_Total.addAll(NextStates_Sum);
////                }
////            }
////            if(NextStates_Total.size()>0){
////                State_Value = new HashMap<SemanticModel,Double>();
////                //遍历添加一个node之后的所有NextStates 计算其与CorrectSemanticModel的值
////                for(SemanticModel sm: NextStates_Total){
////                    sortable_sm = new SortableSemanticModel(sm,true);
////                    Sim_Value = sortable_sm.evaluate(SourceSemanticModel);
////                    State_Value.put(sm,Sim_Value.getPrecision());
////                }
////                System.out.println("每添加一个node后State_Value的大小:"+State_Value.size());
////                Sorted_State_Value = DescendSortMap(State_Value,2);
////                System.out.println("每添加一个node后Sorted_State_Value的大小:"+Sorted_State_Value.size());
////                SearchStates = new ArrayList<SemanticModel>();//清空SearchStates列表
////                SearchStates.addAll(Sorted_State_Value.keySet());//添加beam_size个最好的下一状态集合
////                System.out.println("循环一次后的SearchStates大小:"+SearchStates.size());
////                if(SearchStates.size()>0){
////                    FinalSemanticModels.addAll(SearchStates);
////                }
////                System.out.println("循环一次后的FinalSemanticModels大小:"+FinalSemanticModels.size());
//////                if(AddedAttributionsNum==2){
//////                    int index = 0;
//////                    for(SemanticModel fsm: FinalSemanticModels){
//////                        index++;
//////                        GraphVizUtil.exportSemanticModelToGraphviz(fsm, GraphVizLabelType.LocalId,
//////                                GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples-tmp\\" + index + ".graph.json" + ".dot");
//////
//////                    }
//////                }
////            }
////            else{
////                SearchStates = new ArrayList<SemanticModel>();//清空SearchStates列表
////            }
////            /**5.16**/
////////            int index = 0;
////////            for(SemanticModel fsm: SearchStates){
////////                index++;
////////                GraphVizUtil.exportSemanticModelToGraphviz(fsm, GraphVizLabelType.LocalId,
////////                        GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples-tmp\\" + index + ".graph.json" + ".dot");
////////            }
//////            FinalSemanticModels = new ArrayList<SemanticModel>();
//////            NextStates_Total = new ArrayList<SemanticModel>();
//////            System.out.println("第二次循环的NextStates_Total大小:" + NextStates_Total.size());
//////            //遍历SearchStates中的search state 调用TransitionFunction2 为其生成添加一个节点之后的next search states集合
//////            for(int i=0;i<SearchStates.size();i++) {
//////                TransitionFunctionIndex++;
//////                NextStates_Sum = TransitionFunction2(SearchStates.get(9), IntegrationGraph, Columnnodes);
//////                if(NextStates_Sum.size()>0) {
//////                    System.out.println("第二次每执行一次TransitionFunction2后的nextsearchstates个数:" + NextStates_Sum.size());
//////                    NextStates_Total.addAll(NextStates_Sum);
//////                }
//////            }
//////            if(NextStates_Total.size()>0){
//////                State_Value = new HashMap<SemanticModel,Double>();
//////                //遍历添加一个node之后的所有NextStates 计算其与CorrectSemanticModel的值
//////                for(SemanticModel sm: NextStates_Total){
//////                    sortable_sm = new SortableSemanticModel(sm,true);
//////                    Sim_Value = sortable_sm.evaluate(SourceSemanticModel);
//////                    State_Value.put(sm,Sim_Value.getPrecision());
//////                }
//////                System.out.println("第二次每添加一个node后State_Value的大小:"+State_Value.size());
//////                Sorted_State_Value = SortMap(State_Value,10);
//////                System.out.println("第二次每添加一个node后Sorted_State_Value的大小:"+Sorted_State_Value.size());
//////                SearchStates = new ArrayList<SemanticModel>();//清空SearchStates列表
//////                SearchStates.addAll(Sorted_State_Value.keySet());//添加beam_size个最好的下一状态集合
//////                System.out.println("第二次循环一次后的SearchStates大小:"+SearchStates.size());
//////                if(SearchStates.size()>0){
//////                    FinalSemanticModels.addAll(SearchStates);
//////                }
//////                System.out.println("第二次循环一次后的FinalSemanticModels大小:"+FinalSemanticModels.size());
////////                if(AddedAttributionsNum==1){
////////                    int index = 0;
////////                    for(SemanticModel fsm: FinalSemanticModels){
////////                        index++;
////////                        GraphVizUtil.exportSemanticModelToGraphviz(fsm, GraphVizLabelType.LocalId,
////////                                GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples-tmp\\" + index + ".graph.json" + ".dot");
////////
////////                    }
////////                }
//////            }
//////            else{
//////                SearchStates = new ArrayList<SemanticModel>();//清空SearchStates列表
//////            }
//////            int index = 0;
//////            for(SemanticModel fsm: FinalSemanticModels){
//////                index++;
//////                GraphVizUtil.exportSemanticModelToGraphviz(fsm, GraphVizLabelType.LocalId,
//////                        GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples-tmp\\" + index + ".graph.json" + ".dot");
//////            }
////            /**5.16**/
////
////            AddedAttributionsNum--;
//////            AddedAttributionsNum1--;
////        }
        System.out.println("最终的FinalSemanticModels大小:"+FinalSemanticModels.size());//添加最后一个attribution后得到最终的semantic models
        Beam_Search_Index = 0;
        for(SemanticModel SM: FinalSemanticModels){
            //计算最后SemanticModel的precision和recall
            sortable_sm = new SortableSemanticModel(SM,true);
            Sim_Value = sortable_sm.new_evaluate(SourceSemanticModel);
            System.out.println("输出最终SemanticModel的Precision:" + Sim_Value.getPrecision());
            System.out.println("输出最终SemanticModel的Recall:" + Sim_Value.getRecall());
            Beam_Search_Index++;
            GraphUtil.exportJson1(SM.getGraph(), Params.ROOT_DIR+"prediction-semanticmodels-json\\" + NegExmplesIndex + "_" + Beam_Search_Index + ".graph" + ".json",true,true);
            GraphVizUtil.exportSemanticModelToGraphviz(SM, GraphVizLabelType.LocalId,
                    GraphVizLabelType.LocalUri, false, false, Params.ROOT_DIR+"prediction-semanticmodels\\" + "final_" + NegExmplesIndex + "_" + Beam_Search_Index + ".graph.json" + ".dot");

        }
        /**当初始搜索状态为空时**/

        return FinalSemanticModels;
    }

    public static  List<SemanticModel> TransitionFunctionPrediction1(SemanticModel SearchState, DirectedWeightedMultigraph<Node, DefaultLink> Gint, ColumnNode Attribution) throws Exception{
        //        List<ColumnNode> Columnnodes = new ArrayList<ColumnNode>();
        List<ColumnNode> SearchStateColumnnodes = new ArrayList<ColumnNode>();
        List<ColumnNode> SearchStateColumnnodesEmptySM = new ArrayList<ColumnNode>();
//        List<SemanticModel> StartSearchStates = new LinkedList<SemanticModel>();
//        SemanticModel StartSearchState = null;
//        DirectedWeightedMultigraph<Node, DefaultLink> IntegrationGraph = null;
        List<SemanticModel> Trees = new ArrayList<SemanticModel>();
        List<SemanticModel> NextStates = new ArrayList<SemanticModel>();

//        /**获取Source Semantic Model**/
//        if(SemanticModels == null) {
//            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
//        }
//        SemanticModel SourceSemanticModel = SemanticModels.get(SourceSemanticModelIndex);

//        /**获取source attributions**/
//        Columnnodes = SourceSemanticModel.getColumnNodes();

//        /**获取integration graph**/
//        IntegrationGraph = getIntegrationGraph(0, new Integer[]{1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28});


//        /**当初始搜索状态不为空时**/
//        /**获取Start Search States**/
//        StartSearchStates = getNewStartStatesSemanticModel(SourceSemanticModelIndex);
//        StartSearchState = StartSearchStates.get(StartSearchStateIndex);//根据索引，获取某一个start search state

        /**获取search state的attributions**/
//        SearchStateColumnnodes = SearchState.getColumnNodes();


////        List<SemanticModel> NextSearchStates = new ArrayList<SemanticModel>();
//        Set<ColumnNode> NeededAddColumnNodes= new HashSet<ColumnNode>();//保存StartSearchState中的A'
//
//        for(ColumnNode node: Attributions){
//            if(!SearchStateColumnnodes.contains(node)){
//                NeededAddColumnNodes.add(node);
//            }
//        }
        //如果有待添加的attibution 则继续调用MergeIntoTree1来添加nodes 如果没有待添加的attribution 则直接返回空列表
//        if(NeededAddColumnNodes.size()>0) {
//            for (ColumnNode node_ai : NeededAddColumnNodes) {
                //tree <- MergeIntoTree(St,Gint,ai)
//                Trees = MergeIntoTreePrediction(SearchState, Gint, Attribution);
                Trees = newMergeIntoTreePrediction(SearchState, Gint, Attribution);
                System.out.println("Trees的大小：" + Trees.size());
                //for st+1 <- trees do
//                for (SemanticModel st : Trees) {
//                    NextStates.add(st);
//                }
                NextStates.addAll(Trees);
//            }
            /**当初始搜索状态为空时**/

            int index = 0;
            for(SemanticModel sm: NextStates) {
                index++;
                GraphVizUtil.exportSemanticModelToGraphviz(sm, GraphVizLabelType.LocalId,
                        GraphVizLabelType.LocalUri, false, false, Params.ROOT_DIR+"next-search-states\\" + Beam_Search + "_" + TransitionFunctionIndex + "_" + index + ".graph.json" + ".dot");
            }

//        }
////        else {
////            NextStates = new ArrayList<SemanticModel>();
////        }
        return NextStates;
    }


    public static  List<SemanticModel> TransitionFunctionPrediction(SemanticModel SearchState, DirectedWeightedMultigraph<Node, DefaultLink> Gint, List<ColumnNode> Attributions) throws Exception{
        //        List<ColumnNode> Columnnodes = new ArrayList<ColumnNode>();
        List<ColumnNode> SearchStateColumnnodes = new ArrayList<ColumnNode>();
        List<ColumnNode> SearchStateColumnnodesEmptySM = new ArrayList<ColumnNode>();
//        List<SemanticModel> StartSearchStates = new LinkedList<SemanticModel>();
//        SemanticModel StartSearchState = null;
//        DirectedWeightedMultigraph<Node, DefaultLink> IntegrationGraph = null;
        List<SemanticModel> Trees = new ArrayList<SemanticModel>();
        List<SemanticModel> NextStates = new ArrayList<SemanticModel>();

//        /**获取Source Semantic Model**/
//        if(SemanticModels == null) {
//            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
//        }
//        SemanticModel SourceSemanticModel = SemanticModels.get(SourceSemanticModelIndex);

//        /**获取source attributions**/
//        Columnnodes = SourceSemanticModel.getColumnNodes();

//        /**获取integration graph**/
//        IntegrationGraph = getIntegrationGraph(0, new Integer[]{1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28});


//        /**当初始搜索状态不为空时**/
//        /**获取Start Search States**/
//        StartSearchStates = getNewStartStatesSemanticModel(SourceSemanticModelIndex);
//        StartSearchState = StartSearchStates.get(StartSearchStateIndex);//根据索引，获取某一个start search state

        /**获取search state的attributions**/
        SearchStateColumnnodes = SearchState.getColumnNodes();


//        List<SemanticModel> NextSearchStates = new ArrayList<SemanticModel>();
        Set<ColumnNode> NeededAddColumnNodes= new HashSet<ColumnNode>();//保存StartSearchState中的A'

        for(ColumnNode node: Attributions){
            if(!SearchStateColumnnodes.contains(node)){
                NeededAddColumnNodes.add(node);
            }
        }
        //如果有待添加的attibution 则继续调用MergeIntoTree1来添加nodes 如果没有待添加的attribution 则直接返回空列表
        if(NeededAddColumnNodes.size()>0) {
            for (ColumnNode node_ai : NeededAddColumnNodes) {
                //tree <- MergeIntoTree(St,Gint,ai)
                Trees = MergeIntoTreePrediction(SearchState, Gint, node_ai);
                System.out.println("Trees的大小：" + Trees.size());
                //for st+1 <- trees do
                for (SemanticModel st : Trees) {
                    NextStates.add(st);
                }
            }
            /**当初始搜索状态为空时**/

            int index = 0;
            for(SemanticModel sm: NextStates) {
                index++;
                GraphVizUtil.exportSemanticModelToGraphviz(sm, GraphVizLabelType.LocalId,
                        GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\next-search-states\\" + Beam_Search + "_" + TransitionFunctionIndex + "_" + index + ".graph.json" + ".dot");
            }

        }
//        else {
//            NextStates = new ArrayList<SemanticModel>();
//        }
        return NextStates;
    }

    /**7.19 newMergeIntoPrediction**/
    public static List<SemanticModel> newMergeIntoTreePrediction(SemanticModel ST,DirectedWeightedMultigraph<Node, DefaultLink> Gint,ColumnNode Attribution) throws Exception {
        System.out.println("进入newMergeIntoTreePrediction");
        System.out.println("输出search state的信息：" + "nodes个数：" + ST.getGraph().vertexSet().size() + "||links个数：" + ST.getGraph().edgeSet().size());
        System.out.println("输出Integration Graph的信息：" + "nodes个数：" + Gint.vertexSet().size() + "||links个数：" + Gint.edgeSet().size());
        System.out.println("输出此时Attribution的信息：" + Attribution.getId());

        Set<InternalNode> SearchStateInternalnodes = new HashSet<InternalNode>();
        List<DefaultLink> IntegrationGraphLinks = new ArrayList<DefaultLink>();
        List<DefaultLink> SearchStateLinks = new ArrayList<DefaultLink>();
        Map<Node, Set<Node>> SearchStateInternalnodesMappingIntegrationGraph = new HashMap<Node, Set<Node>>();
        SemanticModel InitialStartSearchStateSM = null;
        SemanticModel MergeInitialStartSearchStateSM = null;
        SemanticModel NextSearchStateSM = null;

        List<SemanticModel> newTrees = new LinkedList<SemanticModel>();

        /**存储StartSearchState中的internal nodes到SearchStateInternalnodes中**/
        SearchStateInternalnodes = ST.getInternalNodes();

        /**存储integration graph中所有的link**/
        IntegrationGraphLinks = new ArrayList<DefaultLink>(Gint.edgeSet());

        /**存储ST(tree)中的所有link**/
        SearchStateLinks = new ArrayList<DefaultLink>(ST.getGraph().edgeSet());

        /**遍历语义模型中的Internal node,找到其在integration graph中对应的nodes**/
        for (InternalNode node : SearchStateInternalnodes) {
            Set<Node> SearchStateInternalnodesMapping = new HashSet<Node>();
            System.out.println("SearchStateInternalnodes的node信息：" + node.getId());
            //获得每个internal node在integration graph中的映射nodes
            for (Node integrationnode : Gint.vertexSet()) {
                if (integrationnode.getId().equals(node.getId())) {
                    SearchStateInternalnodesMapping.add(integrationnode);
                }
            }
            System.out.println("SearchStateInternalnodesMapping的size:" + SearchStateInternalnodesMapping.size());
            //获得所有internal nodes在integration graph中的映射信息
            SearchStateInternalnodesMappingIntegrationGraph.put(node, SearchStateInternalnodesMapping);
        }

        /**获取StartSearchState的root node  改**/
        Node Root = null;
        Root = getSemanticModelRoot(ST);
        System.out.println("MergeIntoTreePrediction中Root.name:" + Root.getId());
        /**5.19**/
        List<Node> RootList = new ArrayList<Node>();
        RootList = getSemanticModelRootList(ST);

        /**取出root在integration graph中的mapping nodes set  改**/
        Set<Node> RootMappingNodes = new HashSet<Node>();
        Set<Node> InternalnodeintreeMappingNodes = new HashSet<Node>();
        /**5.19**/


        List<List<String>> AllconnectedPaths;//存储所有可能的paths(path中的元素是nodeId)
        List<List<DefaultLink>> NeededAddCandidatePath = new ArrayList<List<DefaultLink>>();
        List<List<DefaultLink>> AllconnectedPathsLink_intomount;//存储merge into mount这种情况的所有可能paths(path中的元素是link)
        List<List<Node>> AllconnectedPathsNode_intomount;//存储merge into mount这种情况的所有可能paths(path中的元素是link)
        List<List<DefaultLink>> AllconnectedPathsLink_intotree;//存储merge into tree这种情况的所有可能paths(path中的元素是link)
        List<List<Node>> AllconnectedPathsNode_intotree;//存储merge into tree这种情况的所有可能paths(path中的元素是link)
        List<List<Node>> AllconnectedPathsNode_triangle;//存储merge tree and mount这种情况的所有可能paths(path中的元素是node)


        /**找mntPt及其所有可能的paths 并进行添加**/

//        //初始化path要添加的nodes集合
//        List<Node> eachPathAddedNodes = new ArrayList<Node>();
//        //初始化path要添加的links集合
//        List<DefaultLink> eachPathAddedLinks = new ArrayList<DefaultLink>();
//        List<DefaultLink> eachPathAddedLinks_intomount = new ArrayList<DefaultLink>();
//        List<DefaultLink> eachPathAddedLinks_intotree = new ArrayList<DefaultLink>();
//        List<DefaultLink> eachPathAddedLinks_treeroot = new ArrayList<DefaultLink>();
//        List<DefaultLink> eachPathAddedLinks_mntPtsource = new ArrayList<DefaultLink>();
        //已完成找路径的mntPt semantic type集合,Map<String,Srting>中存放的为link的source node id和link上的信息(uri)
        Set<String> mntPtcomplete = new HashSet<String>();
        //获取每个待添加columnnode的所有可能semantictypes
        /**这个地方是不是还要考虑其正确的user semantic type？(2022.5.8)**/
        List<SemanticType> candidatesemantictypes = getCandidateSteinerSets(Attribution, true, 4);
        System.out.println(Attribution.getColumnName() + "的candidatesemantictypes大小：" + candidatesemantictypes.size() + "||candidatesemantictypes:" + candidatesemantictypes);
        /**对于每个待添加的column node,mntPts中存储的应该是integration graph中和此column node的semantic types相同的nodes**/
        Set<DefaultLink> mntPts = new HashSet<DefaultLink>();
        //遍历每个node的semantic type,找到在integration graph中与该semantic type相同的nodes
        for (SemanticType semantictype : candidatesemantictypes) {
            for (DefaultLink link : Gint.edgeSet()) {
                if ((link.getSource().getUri().equals(semantictype.getDomain().getUri())) && (link.getUri().equals(semantictype.getType().getUri()))) {
                    mntPts.add(link);//优化  存储link.getSource_Id及link.getUri
                }
            }
        }
        System.out.println("mntPts.size():" + mntPts.size());

        Boolean isdelpath = false;
        Set<List<DefaultLink>> AllPaths = new HashSet<List<DefaultLink>>();
        Set<List<DefaultLink>> AllPaths_1 = null;
        Set<List<DefaultLink>> AllPaths_2 = null;
        Set<List<DefaultLink>> AllPaths_3 = null;
        /**找所有可能的paths并进行添加(分两大种情况)  1.直接映射  2.tree和mntPt的merge**/
        //遍历所有可能的mntPt
        for (DefaultLink mntPt : mntPts) {
            //存储当前mntPt的所有可能paths(path中的元素为要添加的links) 最后要依据此列表来添加nodes和links
            AllPaths_1 = new HashSet<List<DefaultLink>>();//intomount
            AllPaths_2 = new HashSet<List<DefaultLink>>();//intotree
            AllPaths_3 = new HashSet<List<DefaultLink>>();//triangle

            /**已完成找路径的mntPt集合  判断要添加的columnnode在integration graph中的映射的具有相同semantic type的link是否重复
             * 如果重复就进入下一次循环
             * 否则就找其connctedPaths**/
            if (mntPtcomplete.contains(mntPt.getSource().getId() + "||" + mntPt.getUri())) {
                continue;
            }
            mntPtcomplete.add(mntPt.getSource().getId() + "||" + mntPt.getUri());

            boolean ExistInIntegrationGraph = false;//判断此mntPt的source node是否在semantic model tree中
            boolean IsRoot = false;//判断此mntPt的source node是否为semantic model tree中的root
            System.out.println("mntPt:" + mntPt.getSource().getId());

            /**2022.5.8 21：47**/
            /**一.直接映射**/
            //判断此mntPt的source node是否在StartSearchState(ST)中
            //如果此mntPt的source node在StartSearchState(ST)中,则只需要直接映射到StartSearchState(ST)中,添加此mntPt的target node
            //检查StartSearchState(ST)的所有Internal nodes或nodes中是否包含mntPt的source node
            if (ST.getGraph().vertexSet().contains(mntPt.getSource())) {
                String mntPtlinkId = LinkIdFactory.getLinkId(mntPt.getId(), mntPt.getSource().getId(), Attribution.getId());
//                System.out.println("mntPtlinkId:" + mntPt.getId());
                LabeledLink mntPtlink = new DataPropertyLink(mntPtlinkId, new Label(mntPt.getUri()));

                InitialStartSearchStateSM = ST.clone();
                System.out.println("Direct方式添加attr时,初始StartSearchState的nodes.size:" + ST.getGraph().vertexSet().size());
                System.out.println("Direct方式添加attr时,初始StartSearchState的links.size:" + ST.getGraph().edgeSet().size());
                /**添加target node**/
                InitialStartSearchStateSM.getGraph().addVertex(Attribution);
                /**添加link**/
                InitialStartSearchStateSM.getGraph().addEdge(mntPt.getSource(), Attribution, mntPtlink);
                MergeIntoTreenumber++;

                GraphVizUtil.exportSemanticModelToGraphviz(InitialStartSearchStateSM, GraphVizLabelType.LocalId,
                        GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\next-state-graph\\" + "next_state_Direct" + MergeIntoTreenumber + ".graph.json" + ".dot");

                newTrees.add(InitialStartSearchStateSM);
//                IsSemanticModeHasOnlyRoot(InitialStartSearchStateSM);//判断是否为tree
                System.out.println("Direct方式添加attr后,NextSearchState的nodes.size:" + InitialStartSearchStateSM.getGraph().vertexSet().size());
                System.out.println("Direct方式添加attr后,NextSearchState的links.size:" + InitialStartSearchStateSM.getGraph().edgeSet().size());
                continue;
            }
            /**一.直接映射**/

            /**二.merge tree和mount**/
            //如果此mntPt的source node不在StartSearchState(ST)中,则需要找三种类型的所有paths,并按照paths添加到StartSearchState(ST)中
            else {
                AllconnectedPathsLink_intomount = new ArrayList<List<DefaultLink>>();//intomount
                AllconnectedPathsNode_intomount = new ArrayList<List<Node>>();//intomount
                AllconnectedPathsLink_intotree = new ArrayList<List<DefaultLink>>();//intotree
                AllconnectedPathsNode_intotree = new ArrayList<List<Node>>();//intotree
                AllconnectedPathsNode_triangle = new ArrayList<List<Node>>();//triangle

                //初始化要添加的mntPt link
                String mntPtlinkId = LinkIdFactory.getLinkId(mntPt.getId(), mntPt.getSource().getId(), Attribution.getId());
//                System.out.println("mntPtlinkId:" + mntPt.getId());
                LabeledLink mntPtlink = new DataPropertyLink(mntPtlinkId, new Label(mntPt.getUri()));
                //添加mntPt的node(source node和target node)及其link
                MergeInitialStartSearchStateSM = ST.clone();
                System.out.println("Merge方式添加atrr时,初始StartSearchState的nodes.size:" + ST.getGraph().vertexSet().size());
                System.out.println("Merge方式添加atrr时,初始StartSearchState的links.size:" + ST.getGraph().edgeSet().size());

                /**添加mntPt**/
                MergeInitialStartSearchStateSM.getGraph().addVertex(Attribution);//添加mntPt的target node
                MergeInitialStartSearchStateSM.getGraph().addVertex(mntPt.getSource());//添加mntPt的source node
                MergeInitialStartSearchStateSM.getGraph().addEdge(mntPt.getSource(), Attribution, mntPtlink);//添加表示mntPt的link
                /**添加mntPt**/

//                System.out.println("Merge方式添加atrr时,添加mntPt-link后MergeInitialStartSearchStateSM的nodes.size:" + MergeInitialStartSearchStateSM.getGraph().vertexSet().size());
//                System.out.println("Merge方式添加atrr时,添加mntPt-link后MergeInitialStartSearchStateSM的links.size:" + MergeInitialStartSearchStateSM.getGraph().edgeSet().size());


                /**1.tree添加到mntPt的paths  intomount**/
                //以mntPt的source node为source,以tree的root为target 找到所有可能的paths(此时path中的元素为node)  path长度最大为3:表示mntPt和tree-root之间最多间隔一个node
                //取出root在integration graph中的mapping nodes set  改Root->RootList

                RootMappingNodes = SearchStateInternalnodesMappingIntegrationGraph.get(Root);
                System.out.println("RootMappingNodesPerRoot:" + RootMappingNodes.size());
                //遍历每个root映射到integration中的nodes
                for (Node rootmappingnode : RootMappingNodes) {
                    connectedPathsNode = new ArrayList<List<Node>>();
                    connectedPathsLink = new ArrayList<List<DefaultLink>>();
                    newfindAllPathLinkForClearPath(IntegrationGraphLinks, mntPt.getSource().getId(), rootmappingnode.getId(), 3);
                    AllconnectedPathsLink_intomount.addAll(connectedPathsLink);
                    /**考虑defaultlink**/
//                    if(AllconnectedPathsLink_intomount.size()==0) {
//                        connectedPathsLink = new ArrayList<List<DefaultLink>>();
//                        newfindAllPathLink(IntegrationGraphLinks, mntPt.getSource().getId(), rootmappingnode.getId(), 3);
//                        NeededAddCandidatePath = connectedPathsLink.subList(0, 1);
//                        AllconnectedPathsLink_intomount.addAll(NeededAddCandidatePath);
//                    }
                    /**考虑defaultlink**/
                }

                System.out.println("AllconnectedPathsLink_intomount.size1:" + mntPt.getId() + "||" + AllconnectedPathsLink_intomount.size());
//                System.out.println("AllconnectedPathsNode_intomount.size1:" + mntPt.getId() + "||" + AllconnectedPathsNode_intomount.size());

                //以set的形式暂存当前node pair的links
//                Set<DefaultLink> temp_nodepair_links_intomount = null;
//                for (List<Node> path : AllconnectedPathsNode_intomount) {
//                    eachPathAddedLinks = new ArrayList<DefaultLink>();
//                    //存储每个path要添加的links信息
//                    for (int i = 0; i < path.size() - 1; i++) {
//                        temp_nodepair_links_intomount = new HashSet<DefaultLink>();
//                        /**检查当前pathnode的nodes(除tree-root外)是否存在于StartSearchState的InternalNodes中  避免出现环**/
//                        if (ST.getGraph().vertexSet().contains(path.get(i))) {
//                            eachPathAddedLinks = new ArrayList<DefaultLink>();
//                            break;
//                        }
//                        else {
//                            for (DefaultLink integrationlink : Gint.edgeSet()) {
//                                if((integrationlink.getSource().getId().equals(path.get(i).getId())) && (integrationlink.getTarget().getId().equals(path.get(i + 1).getId()))){
//                                    temp_nodepair_links_intomount.add(integrationlink);//存储了当前node pair所有links
//                                }
//                            }
//                            //计算temp_nodepair_links中defaultlink的数量
//                            int defaultlinknum = 0;
//                            for(DefaultLink link: temp_nodepair_links_intomount){
//                                if(link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink")){
//                                    defaultlinknum++;
//                                }
//                            }
//                            if(defaultlinknum == temp_nodepair_links_intomount.size()){
////                                System.out.println("AllPath1_添加了defaultlink");
////                                eachPathAddedLinks = new ArrayList<DefaultLink>();
////                                break;
//                                eachPathAddedLinks.add(new ArrayList<DefaultLink>(temp_nodepair_links_intomount).get(0));
//                            }
//                            else{
////                                System.out.println("AllPath1_添加了nondefaultlink");
//                                for(DefaultLink link: temp_nodepair_links_intomount){
//                                    if(!(link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink"))){
//                                        System.out.println(link.getId());
//                                        eachPathAddedLinks.add(link);
//                                        break;
//                                    }
//                                }
//                            }
//                        }
//                    }
//                    if (eachPathAddedLinks.size() == (path.size()-1)) {
//                        AllPaths_1.add(eachPathAddedLinks);
//                    }
//                }
                for (List<DefaultLink> path : new HashSet<List<DefaultLink>>(AllconnectedPathsLink_intomount)) {
                    isdelpath = false;
                    /**检查当前path中的nodes(除tree-root外)是否存在于StartSearchState的InternalNodes中  避免出现环**/
                    for (int i = 0; i < path.size(); i++) {
                        /**去除包含defaultlink的path**/
//                        if (path.get(i).getUri().equals("http://isi.edu/integration/karma/dev#defaultLink")) {
//                            isdelpath = true;
//                            break;
//                        }
                        /**去除包含defaultlink的path**/
                        if (i < path.size() - 1) {
                            if ((ST.getGraph().vertexSet().contains(path.get(i).getSource())) || (ST.getGraph().vertexSet().contains(path.get(i).getTarget()))) {
                                isdelpath = true;
                                break;
                            }
                        } else {
                            if (ST.getGraph().vertexSet().contains(path.get(i).getSource())) {
                                isdelpath = true;
                                break;
                            }
                        }
                    }
                    if (!isdelpath) {
                        AllPaths_1.add(path);
                    }
                }
                AllPaths.addAll(AllPaths_1);
                System.out.println("AllPaths_1.size:" + mntPt.getId() + "||" + AllPaths_1.size());
                System.out.println("AllPaths.size:" + mntPt.getId() + "||" + AllPaths.size());


                /**2.mntPt添加到tree的paths  intotree  注意此时mntPt的class node(source node)不在tree中**/
                //以tree中的任一class node为source,以mntPt的source node为target  找到所有可能的paths(此时path中的元素为node)
                //判断mntPt的class node是否在tree中  如果在tree中 则跳过 不为其查找添加到tree中的paths 然后检查下一个mntPt  否则,为其查找添加到tree中的paths
//                System.out.println("判断mntPt的class node是否在tree中");
                if (ST.getGraph().vertexSet().contains(mntPt.getSource())) {
                    continue;
                } else {
                    //遍历tree(ST)中每个Internal node(共11个internal node)
                    NeededAddCandidatePath = new ArrayList<List<DefaultLink>>();
                    for (Node internalnodeIntree : ST.getInternalNodes()) {
                        //取出每个internalnodeIntree在Integration Graph中对应的nodes列表
                        InternalnodeintreeMappingNodes = SearchStateInternalnodesMappingIntegrationGraph.get(internalnodeIntree);
                        //遍历InternalnodeintreeMappingNodes集合,以每个node为source,以mntPt的source node为target,找到所有可能的paths(此时path中的元素为link)
                        System.out.println("InternalnodeintreeMappingNodes.size:" + InternalnodeintreeMappingNodes.size());
                        for (Node internalnodeintreemappingnode : InternalnodeintreeMappingNodes) {
                            connectedPathsNode = new ArrayList<List<Node>>();
                            connectedPathsLink = new ArrayList<List<DefaultLink>>();
                            newfindAllPathLinkForClearPath(IntegrationGraphLinks, internalnodeintreemappingnode.getId(), mntPt.getSource().getId(), 3);
                            AllconnectedPathsLink_intotree.addAll(connectedPathsLink);
                            /**考虑defaultlink**/
//                            connectedPathsNode = new ArrayList<List<Node>>();
//                            connectedPathsLink = new ArrayList<List<DefaultLink>>();
//                            newfindAllPathLink(IntegrationGraphLinks, internalnodeintreemappingnode.getId(), mntPt.getSource().getId(), 3);
//                            NeededAddCandidatePath.addAll(connectedPathsLink.subList(0,1));
                            /**考虑defaultlink**/
                        }
                    }
                    /**考虑defaultlink**/
//                    if(AllconnectedPathsLink_intotree.size()==0) {
//                        Collections.shuffle(NeededAddCandidatePath);
//                        AllconnectedPathsLink_intotree.addAll(NeededAddCandidatePath.subList(0, 1));
//                    }
                    /**考虑defaultlink**/
                }
                System.out.println("AllconnectedPathsLink_intotree.size2:" + mntPt.getId() + "||" + AllconnectedPathsLink_intotree.size());
//                System.out.println("AllconnectedPathsNode_intotree.size2:" + mntPt.getId() + "||" + AllconnectedPathsNode_intotree.size());

                //以set的形式暂存当前node pair的links
                List<DefaultLink> deldefaultlink = new ArrayList<DefaultLink>();
                for (List<DefaultLink> path : new HashSet<List<DefaultLink>>(AllconnectedPathsLink_intotree)) {
                    isdelpath = false;
                    //存储每个path要添加的links信息
                    deldefaultlink = new ArrayList<DefaultLink>();
                    for (int i = 0; i < path.size(); i++) {
//                        if (path.get(i).getUri().equals("http://isi.edu/integration/karma/dev#defaultLink")) {
//                            isdelpath = true;
//                            break;
//                        }
                        /**依次遍历path中的node pair(1-2,2-3,3-4...)
                         * 检查当前node pair是否在tree中有路径 如果有则不添加node pair之间对应到integration graph上的link信息
                         * 如果没有则添加对应到integration graph上的link信息**/
                        nowPathNode = new ArrayList<Node>();
                        nowPathLink = new ArrayList<DefaultLink>();
                        connectedPathsNode = new ArrayList<List<Node>>();
                        connectedPathsLink = new ArrayList<List<DefaultLink>>();
                        newfindAllPathLink(SearchStateLinks, path.get(i).getSource().getId(), path.get(i).getTarget().getId(), 50);//长度变更
                        if (connectedPathsLink.size() > 0) {
                            deldefaultlink.add(path.get(i));
//                            path.remove(path.get(i));
                        }
                        /**如果path.size()>2 检查当前pathlink的nodes(除第一个node外)是否存在于StartSearchState的InternalNodes中  避免出现环**/
                        if ((i == 0) && (ST.getGraph().vertexSet().contains(path.get(i).getTarget()))) {
                            isdelpath = true;
                            break;
                        } else if ((i > 0) && ((ST.getGraph().vertexSet().contains(path.get(i).getSource())) || (ST.getGraph().vertexSet().contains(path.get(i).getTarget())))) {
                            isdelpath = true;
                            break;
                        }
                    }
                    if (!isdelpath) {
                        path.removeAll(deldefaultlink);
                        AllPaths_2.add(path);
                    }
                }
                AllPaths.addAll(AllPaths_2);
                System.out.println("AllPaths_2.size:" + mntPt.getId() + "||" + AllPaths_2.size());
                System.out.println("AllPaths.size:" + mntPt.getId() + "||" + AllPaths.size());

                /**3.mntPt和tree到common nodes的paths**/
                //分别查找mntPt和tree在integration graph中的ancestor nodes
                Set<Node> mntPt_AncestorNodes = new HashSet<Node>();
                mntPt_AncestorNodes = findAncestorNodesInIntegrationGraph(Gint, mntPt.getSource());//获得mntPt的ancestornodes列表
                //遍历每个Root 找到其tree_AncestorNodes
                Set<Node> tree_AncestorNodes = new HashSet<Node>();//存储ST(tree)的root在integration graph中的ancestor nodes
                for (Node root : RootList) {
                    Set<Node> tree_ANsCommonWithmntPt_AN = new HashSet<Node>();
//                System.out.println(mntPt.getId()+"的mntPt和tree到common nodes的paths");
                    tree_AncestorNodes = new HashSet<Node>();
                    tree_AncestorNodes = findAncestorNodesInIntegrationGraph(Gint, root);
                    System.out.println("mntPt_AncestorNodes的初始大小：" + mntPt_AncestorNodes.size());
                    System.out.println("tree_AncestorNodes的初始大小：" + tree_AncestorNodes.size());
                    tree_ANsCommonWithmntPt_AN.addAll(tree_AncestorNodes);
                    tree_ANsCommonWithmntPt_AN.retainAll(mntPt_AncestorNodes);
                    System.out.println("tree_AncestorNodes和mntPt_AncestorNodes的交集大小" + tree_ANsCommonWithmntPt_AN.size());
                    //遍历tree_ANsCommonWithmntPt_AN  找到其中每一个节点到tree root的commonnode_tree_paths和到mntPt source node的commonnode_mntPt_paths
                    for (Node commonnode : tree_ANsCommonWithmntPt_AN) {
                        if (!ST.getGraph().vertexSet().contains(commonnode)) {//避免出现环
                            connectedPathsNode = new ArrayList<List<Node>>();
                            connectedPathsLink = new ArrayList<List<DefaultLink>>();
                            connectedPathsNode_ANs_tree = new HashSet<List<Node>>();
                            connectedPathsLink_ANs_tree = new HashSet<List<DefaultLink>>();
                            connectedPathsNode_ANs_mntPt = new HashSet<List<Node>>();
                            connectedPathsLink_ANs_mntPt = new HashSet<List<DefaultLink>>();
                            List<List<DefaultLink>> pathTreeMntPtPerCommon = new ArrayList<List<DefaultLink>>();
                            //以common node为source,以tree root为target
                            newfindAllPathLinkForClearPath(IntegrationGraphLinks, commonnode.getId(), Root.getId(), 3);
                            connectedPathsNode_ANs_tree.addAll(connectedPathsNode);
                            connectedPathsLink_ANs_tree.addAll(connectedPathsLink);
//                          System.out.println("connectedPathsNode_ANs_tree-connectedPathsNode的大小：" + connectedPathsNode.size());
//                          System.out.println("connectedPathsNode_ANs_tree的大小：" + connectedPathsNode_ANs_tree.size());
//                          System.out.println("connectedPathsLink_ANs_tree的大小：" + connectedPathsLink_ANs_tree.size());
//                          System.out.println("connectedPathsNode_ANs_tree的get(0)的大小：" + new ArrayList<>(connectedPathsNode_ANs_tree).get(0).size());
                            //以common node为source,以mntPt source node为target
                            connectedPathsNode = new ArrayList<List<Node>>();
                            connectedPathsLink = new ArrayList<List<DefaultLink>>();
                            newfindAllPathLinkForClearPath(IntegrationGraphLinks, commonnode.getId(), mntPt.getSource().getId(), 3);
                            connectedPathsNode_ANs_mntPt.addAll(connectedPathsNode);
                            connectedPathsLink_ANs_mntPt.addAll(connectedPathsLink);
//                          System.out.println("connectedPathsNode_ANs_mntPt-connectedPathsNode的大小：" + connectedPathsNode.size());
//                          System.out.println("connectedPathsNode_ANs_mntPt的大小：" + connectedPathsNode_ANs_mntPt.size());
//                          System.out.println("connectedPathsLink_ANs_mntPt的大小：" + connectedPathsLink_ANs_mntPt.size());
//                          System.out.println("connectedPathsNode_ANs_mntPt的get(0)的大小：" + new ArrayList<>(connectedPathsNode_ANs_mntPt).get(0).size());

                            /**整合tree_path和mnt_path**/
                            for (List<DefaultLink> path_ans_tree : connectedPathsLink_ANs_tree) {
                                isdelpath = false;
                                //存储每个path要添加的links信息
                                for (int i = 0; i < path_ans_tree.size(); i++) {
                                    if (path_ans_tree.get(i).getUri().equals("http://isi.edu/integration/karma/dev#defaultLink")) {
                                        isdelpath = true;
                                        break;
                                    }
                                    /**依次遍历path中的node pair(1-2,2-3,3-4...)
                                     * 添加对应到integration graph上的link信息**/
                                    /**检查当前pathnode的nodes(除tree-root外)是否存在于StartSearchState的InternalNodes中  避免出现环**/
                                    if ((i == (path_ans_tree.size() - 1)) && (ST.getGraph().vertexSet().contains(path_ans_tree.get(i).getSource()))) {
                                        isdelpath = true;
                                        break;
                                    } else if ((i < (path_ans_tree.size() - 1)) && ((ST.getGraph().vertexSet().contains(path_ans_tree.get(i).getSource())) || (ST.getGraph().vertexSet().contains(path_ans_tree.get(i).getTarget())))) {
                                        isdelpath = true;
                                        break;
                                    }
                                }
                                if ((isdelpath) || (path_ans_tree.size() == 0)) {
                                    continue;
                                }
//                              System.out.println("eachPathAddedLinks_treeroot的get(0)的大小：" + eachPathAddedLinks_treeroot.size());
//                              System.out.println("结束了一次path_ans_tree");


                                /**处理mntpath**/
                                for (List<DefaultLink> path_ans_mntPt : connectedPathsLink_ANs_mntPt) {
                                    isdelpath = false;
                                    //这里判断如果两个childpath大小之和大于5 则continue 否则继续以下操作
                                    if ((path_ans_tree.size() + path_ans_mntPt.size()) > 3) {
                                        continue;
                                    }
                                    //存储每个path要添加的links信息
                                    for (int i = 0; i < path_ans_mntPt.size(); i++) {
                                        if (path_ans_mntPt.get(i).getUri().equals("http://isi.edu/integration/karma/dev#defaultLink")) {
                                            isdelpath = true;
                                            break;
                                        }
                                        /**依次遍历path中的node pair(1-2,2-3,3-4...)
                                         * 添加对应到integration graph上的link信息**/
                                        //以set的形式暂存当前node pair的links
                                        /**检查当前pathnode的nodes(除mntPt source node外)是否存在于StartSearchState的InternalNodes中  避免出现环**/
                                        if ((ST.getGraph().vertexSet().contains(path_ans_mntPt.get(i).getSource())) || (ST.getGraph().vertexSet().contains(path_ans_mntPt.get(i).getTarget()))) {
                                            isdelpath = true;
                                            break;
                                        }
                                    }
                                    if (isdelpath) {
                                        continue;
                                    }
                                    List<DefaultLink> path_tree_with_mntPt = new ArrayList<DefaultLink>();
                                    if (path_ans_mntPt.size() > 0) {
                                        if (!(path_ans_tree.get(0).getUri().equals(path_ans_mntPt.get(0).getUri()))) {
                                            path_tree_with_mntPt.addAll(path_ans_tree);
                                            path_tree_with_mntPt.addAll(path_ans_mntPt);
                                        } else {
                                            continue;
                                        }
                                    } else {
                                        continue;
                                    }
                                    int commonnodenum = 0;
                                    for (DefaultLink link : path_tree_with_mntPt) {
                                        if (link.getSource().getId().equals(commonnode.getId())) {
                                            commonnodenum++;
                                        }
                                    }
                                    if (commonnodenum == 2) {
                                        pathTreeMntPtPerCommon.add(path_tree_with_mntPt);
                                    }
                                }
                            }
//                          if(pathTreeMntPtPerCommon.size()>0) {
//                              System.out.println("pathTreeMntPtPerCommon的大小：" + pathTreeMntPtPerCommon.get(0).size());
//                          }

//                          if(pathTreeMntPtPerCommon.size()>0) {
//                              System.out.println("pathTreeMntPtPerCommon的大小：" + pathTreeMntPtPerCommon.size());
//                          }
                            if (pathTreeMntPtPerCommon.size() > 0) {
                                AllPaths_3.addAll(pathTreeMntPtPerCommon);
                            }
                        }
                    }
                }

                System.out.println(mntPt.getId() + "的AllPaths_3大小" + AllPaths_3.size());
                /**3.mntPt和tree到common nodes的paths**/

                //遍历tree的ancestor nodes
                //查看mntPt的ancestor nodes中是否包含当前的tree ancestor node
                //如果包含则取该node为common node,查找common node到tree root node的path以及common node到mntPt source node的path
                //依据这一对path添加信息 生成triangle类型的nextsearchstate


                /**二.merge tree和mount**/

                /**添加其中任意一种类型(如AllPaths_1)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/
                for (List<DefaultLink> addpath : AllPaths_1) {
                    if (addpath.size() > 0) {
                        NextSearchStateSM = MergeInitialStartSearchStateSM.clone();
//            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().vertexSet().size());
//            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().edgeSet().size());
                        for (int i = 0; i < addpath.size(); i++) {
                            LabeledLink addedlink = new DataPropertyLink(addpath.get(i).getId(), new Label(addpath.get(i).getUri()));
                            NextSearchStateSM.getGraph().addVertex(addpath.get(i).getSource());
                            NextSearchStateSM.getGraph().addVertex(addpath.get(i).getTarget());
                            NextSearchStateSM.getGraph().addEdge(addpath.get(i).getSource(), addpath.get(i).getTarget(), addedlink);
                        }
                        MergeIntoTreenumber++;

                        /**保存Json文件**/

                        /**保存dot文件**/
                        GraphVizUtil.exportSemanticModelToGraphviz(NextSearchStateSM, GraphVizLabelType.LocalId,
                                GraphVizLabelType.LocalUri, false, false, Params.ROOT_DIR + "next-state-graph\\" + "next_state_IntoMount" + Beam_Search + "_" + MergeIntoTreenumber + ".graph.json" + ".dot");

                        newTrees.add(NextSearchStateSM);
//                IsSemanticModeHasOnlyRoot(NextSearchStateSM);//判断是否为tree
                        System.out.println("NextSearchStateSM的nodes:" + NextSearchStateSM.getGraph().vertexSet().size());
                        System.out.println("NextSearchStateSM的links:" + NextSearchStateSM.getGraph().edgeSet().size());
                    }
                }
                /**添加其中任意一种类型(如AllPaths_1)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/

                /**添加其中任意一种类型(如AllPaths_2)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/
                for (List<DefaultLink> addpath : AllPaths_2) {
                    if (addpath.size() > 0) {
                        NextSearchStateSM = MergeInitialStartSearchStateSM.clone();
//            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().vertexSet().size());
//            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().edgeSet().size());
                        for (int i = 0; i < addpath.size(); i++) {
                            LabeledLink addedlink = new DataPropertyLink(addpath.get(i).getId(), new Label(addpath.get(i).getUri()));
                            NextSearchStateSM.getGraph().addVertex(addpath.get(i).getSource());
                            NextSearchStateSM.getGraph().addVertex(addpath.get(i).getTarget());
                            NextSearchStateSM.getGraph().addEdge(addpath.get(i).getSource(), addpath.get(i).getTarget(), addedlink);
                        }
                        MergeIntoTreenumber++;

                        GraphVizUtil.exportSemanticModelToGraphviz(NextSearchStateSM, GraphVizLabelType.LocalId,
                                GraphVizLabelType.LocalUri, false, false, Params.ROOT_DIR + "next-state-graph\\" + "next_state_IntoTree" + Beam_Search + "_" + MergeIntoTreenumber + ".graph.json" + ".dot");

                        newTrees.add(NextSearchStateSM);
//                IsSemanticModeHasOnlyRoot(NextSearchStateSM);//判断是否为tree
                        System.out.println("NextSearchStateSM的nodes:" + NextSearchStateSM.getGraph().vertexSet().size());
                        System.out.println("NextSearchStateSM的links:" + NextSearchStateSM.getGraph().edgeSet().size());
                    }
                }
                /**添加其中任意一种类型(如AllPaths_2)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/

                /**添加其中任意一种类型(如AllPaths_3)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/
                for (List<DefaultLink> addpath : AllPaths_3) {
//                System.out.println("AllPaths_3:" + addpath.size());
                    if (addpath.size() > 0) {
                        NextSearchStateSM = MergeInitialStartSearchStateSM.clone();
//            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().vertexSet().size());
//            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().edgeSet().size());
                        for (int i = 0; i < addpath.size(); i++) {
                            LabeledLink addedlink = new DataPropertyLink(addpath.get(i).getId(), new Label(addpath.get(i).getUri()));
                            NextSearchStateSM.getGraph().addVertex(addpath.get(i).getSource());
                            NextSearchStateSM.getGraph().addVertex(addpath.get(i).getTarget());
                            NextSearchStateSM.getGraph().addEdge(addpath.get(i).getSource(), addpath.get(i).getTarget(), addedlink);
                        }
                        MergeIntoTreenumber++;

                        GraphVizUtil.exportSemanticModelToGraphviz(NextSearchStateSM, GraphVizLabelType.LocalId,
                                GraphVizLabelType.LocalUri, false, false, Params.ROOT_DIR + "next-state-graph\\" + "next_state_triangle" + Beam_Search + "_" + MergeIntoTreenumber + ".graph.json" + ".dot");

                        newTrees.add(NextSearchStateSM);
//                IsSemanticModeHasOnlyRoot(NextSearchStateSM);//判断是否为tree
                        System.out.println("NextSearchStateSM的nodes:" + NextSearchStateSM.getGraph().vertexSet().size());
                        System.out.println("NextSearchStateSM的links:" + NextSearchStateSM.getGraph().edgeSet().size());
                    }
                }

//            /**添加其中任意一种类型(如AllPaths_3)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/
//
//            /**2022.5.8 22：10 注释**/
////            /**判断mntPt类型(三种)**/
////            for (Node i : SearchStateInternalnodesMappingIntegrationGraph.keySet()) {
////                /**判断mntPt的source是不是已经存在于semantic model tree中
////                 * 1.如果存在于semantic model tree中，并且不是映射到semantic model tree的root上，则只需要找semantic model tree的root到mntPt的source node之间的路径
////                 * 2.如果此mntPt的source node映射到semantic model tree中的root上，则需要找common node将semantic model tree与mntPt连接起来
////                 * 3.如果mntPt的source node不存在于semantic model tree中,则找semantic model tree中的任意internal node到mntPt的source node之间的路径**/
////                if (SearchStateInternalnodesMappingIntegrationGraph.get(i).contains(mntPt.getSource())) {
////                    ExistInIntegrationGraph = true;//mntPt的source node存在于semantic model tree中
////                    if (mntPt.getSource().getId().equals(Root.getId())) {
////                        IsRoot = true;
////                    }
////                    break;
////                }
////            }
////            System.out.println("ExistInIntegrationGraph:" + ExistInIntegrationGraph);
////            System.out.println("IsRoot:" + IsRoot);
////
////
////            //1.如果mntPt的source node存在于semantic model tree中，并且为semantic model tree中的root，则需找common node将两者联系起来
////            if (ExistInIntegrationGraph && IsRoot) {
////                //保存每个mntPt的所有的待添加路径信息
////                AllconnectedPaths = new ArrayList<List<String>>();
////                AllconnectedPathsNode = new ArrayList<List<Node>>();
////                System.out.println("找common node----------");
////            }
////            //2.如果mntPt的source node存在于semantic model tree中，且不为root，则需找root到mntPt之间的路径
////            else if (ExistInIntegrationGraph) {
////                //保存每个mntPt的所有的待添加路径信息
////                AllconnectedPaths = new ArrayList<List<String>>();
////                AllconnectedPathsNode = new ArrayList<List<Node>>();
////
////                System.out.println("找root到mntPt之间的路径----------");
////                //取出root在integration graph中的mapping nodes set
////                RootMappingNodes = SearchStateInternalnodesMappingIntegrationGraph.get(Root);
////                System.out.println("RootMappingNodes:" + RootMappingNodes.size());
////
////                //遍历每个root到integration中的nodes
////                for (Node rootmappingnode : RootMappingNodes) {
////                    System.out.println("rootmappingnode:" + rootmappingnode.getId() + "||" + mntPt.getSource().getId());
////                    connectedPathsNode = new ArrayList<List<Node>>();
////                    findAllPathNode(IntegrationGraphLinks, rootmappingnode.getId(), mntPt.getSource().getId(), 3);
////                    System.out.println("connectedPathsNode.size:" + connectedPathsNode.size());
////                    //connectedPaths ← all paths that connect leaves or root of st with mntPt
////                    int index = 0;//用于测试,对于每个要添加的node,现只连接其第一条路径
////
////                    //获得每个mntPt的所有待添加路径信息
////                    for (List<Node> path : connectedPathsNode) {
////                        AllconnectedPathsNode.add(path);
////                    }
////
////                    System.out.println("AllconnectedPathsNode.size:" + AllconnectedPathsNode.size());
////                    for (List<Node> path : AllconnectedPathsNode) {
////                        InitialStartSearchStateSM = ST.clone();
////                        System.out.println("初始化时StartSearchState的nodes:" + ST.getGraph().vertexSet().size());
////                        System.out.println("初始化时StartSearchState的links:" + ST.getGraph().edgeSet().size());
////
////                        eachPathAddedNodes.add(Attribution);//添加需要add的mntPt target(column) node
////                        /**添加target node**/
////                        InitialStartSearchStateSM.getGraph().addVertex(Attribution);
////                        /**添加mntPt**/
////                        String mntPtlinkId = LinkIdFactory.getLinkId(mntPt.getId(), mntPt.getSource().getId(), Attribution.getId());
////                        System.out.println("mntPtlinkId:" + mntPt.getId());
////                        LabeledLink mntPtlink = new DataPropertyLink(mntPtlinkId, new Label(mntPt.getUri()));
////                        InitialStartSearchStateSM.getGraph().addEdge(mntPt.getSource(), Attribution, mntPtlink);
////                        /**完成target(column) node和mntPt的添加**/
////                        System.out.println(mntPt.getSource().getId() + "的connectedPaths:" + path);
////                        //存储每个path要添加的nodes
////                        for (Node nodeInfo : path) {
////                            for (Node integrationnode : Gint.vertexSet()) {
////                                if (integrationnode.getId().equals(nodeInfo.getId())) {
//////                                    InitialStartSearchState.addVertex(integrationnode);//添加每个path要add的nodes\
////                                    InitialStartSearchStateSM.getGraph().addVertex(integrationnode);
////                                    eachPathAddedNodes.add(integrationnode);
////                                }
////                            }
////                        }
//////                            //输出每条(第一条)path要添加的nodes信息
//////                            for(Node pathnode: eachPathAddedNodes) {
//////                                //向semantic model tree中添加这些nodes
//////                                System.out.println("输出每条(第一条)path要添加的nodes信息" + pathnode.getId());
//////                            }////////////////////////////////////////////
////                        //存储每个path要添加的links信息
////                        for (int i = 0; i < path.size() - 1; i++) {
////                            for (DefaultLink integrationlink : Gint.edgeSet()) {
////                                if ((integrationlink.getSource().getId().equals(path.get(i).getId())) && (integrationlink.getTarget().getId().equals(path.get(i + 1).getId()))) {//待添加的links
////                                    boolean isaddedlink = true;
////                                    LabeledLink addedlink = new DataPropertyLink(integrationlink.getId(), new Label(integrationlink.getUri()));
////                                    for (LabeledLink semanticmodeltreelink : ST.getGraph().edgeSet()) {//遍历semantic model tree中的links
////                                        if (integrationlink.getId().equals(semanticmodeltreelink.getId())) {
////                                            isaddedlink = false;
////                                            break;
////                                        }
////                                    }
////                                    if (isaddedlink) {
////                                        InitialStartSearchStateSM.getGraph().addEdge(integrationlink.getSource(), integrationlink.getTarget(), addedlink);
////                                    }
////                                    eachPathAddedLinks.add(integrationlink);//测试
////                                }
////                            }
////                        }
//////                            //输出每条(第一条)path要添加的links信息
//////                            for(DefaultLink pathlink: eachPathAddedLinks) {
//////                                //向semantic model tree中添加这些nodes
//////                                System.out.println("输出每条(第一条)path要添加的links信息" + pathlink.getId());
//////                            }//////////////////////////////
////
////                        /**保存添加一个target(column) node的nextsearchstate**/
////
////                        MergeIntoTreenumber++;
////
////                        GraphVizUtil.exportSemanticModelToGraphviz(InitialStartSearchStateSM, GraphVizLabelType.LocalId,
////                                GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\next-state-graph\\" + "next_state_" + MergeIntoTreenumber + ".graph.json" + ".dot");
////
////                        newTrees.add(InitialStartSearchStateSM);
////                        System.out.println("InitialStartSearchState的nodes:" + InitialStartSearchStateSM.getGraph().vertexSet().size());
////                        System.out.println("InitialStartSearchState的links:" + InitialStartSearchStateSM.getGraph().edgeSet().size());
////                    }
////                }
////            }
////            //3.如果mntPt的source node不存在于semantic model tree中,则找semantic model tree中的任意internal node到mntPt的source node之间的路径
////            else{
////                //保存每个mntPt的所有的待添加路径信息
////                AllconnectedPaths = new ArrayList<List<String>>();
////                AllconnectedPathsNode = new ArrayList<List<Node>>();
////                System.out.println("找semantic model tree中任一internal node到mntPt的source node之间的路径");
////            }
//            /**2022.5.8 22：10 注释**/
//        }
            }
        }
        return newTrees;
    }

    public static List<SemanticModel> MergeIntoTreePrediction(SemanticModel ST,DirectedWeightedMultigraph<Node, DefaultLink> Gint,ColumnNode Attribution) throws Exception {
        System.out.println("进入MergeIntoTreePrediction");
        System.out.println("输出search state的信息：" + "nodes个数：" + ST.getGraph().vertexSet().size() + "||links个数：" + ST.getGraph().edgeSet().size());
        System.out.println("输出Integration Graph的信息：" + "nodes个数：" + Gint.vertexSet().size() + "||links个数：" + Gint.edgeSet().size());
        System.out.println("输出此时Attribution的信息：" + Attribution.getId());

        Set<InternalNode> SearchStateInternalnodes = new HashSet<InternalNode>();
        List<DefaultLink> IntegrationGraphLinks = new ArrayList<DefaultLink>();
        List<DefaultLink> SearchStateLinks = new ArrayList<DefaultLink>();
        Map<Node, Set<Node>> SearchStateInternalnodesMappingIntegrationGraph = new HashMap<Node, Set<Node>>();
        SemanticModel InitialStartSearchStateSM = null;
        SemanticModel MergeInitialStartSearchStateSM = null;
        SemanticModel NextSearchStateSM = null;

        List<SemanticModel> newTrees = new LinkedList<SemanticModel>();

        /**存储StartSearchState中的internal nodes到SearchStateInternalnodes中**/
        SearchStateInternalnodes = ST.getInternalNodes();

        /**存储integration graph中所有的link**/
        IntegrationGraphLinks = new ArrayList<DefaultLink>(Gint.edgeSet());

        /**存储ST(tree)中的所有link**/
        SearchStateLinks = new ArrayList<DefaultLink>(ST.getGraph().edgeSet());

        /**遍历语义模型中的Internal node,找到其在integration graph中对应的nodes**/
        for (InternalNode node : SearchStateInternalnodes) {
            Set<Node> SearchStateInternalnodesMapping = new HashSet<Node>();
            System.out.println("SearchStateInternalnodes的node信息：" + node.getId());
            //获得每个internal node在integration graph中的映射nodes
            for (Node integrationnode : Gint.vertexSet()) {
                if (integrationnode.getId().equals(node.getId())) {
                    SearchStateInternalnodesMapping.add(integrationnode);
                }
            }
            System.out.println("SearchStateInternalnodesMapping的size:" + SearchStateInternalnodesMapping.size());
            //获得所有internal nodes在integration graph中的映射信息
            SearchStateInternalnodesMappingIntegrationGraph.put(node, SearchStateInternalnodesMapping);
        }

        /**获取StartSearchState的root node  改**/
        Node Root = null;
        Root = getSemanticModelRoot(ST);
        System.out.println("MergeIntoTreePrediction中Root.name:" + Root.getId());
        /**5.19**/
        List<Node> RootList = new ArrayList<Node>();
        RootList = getSemanticModelRootList(ST);

        /**取出root在integration graph中的mapping nodes set  改**/
        Set<Node> RootMappingNodes = new HashSet<Node>();
        Set<Node> InternalnodeintreeMappingNodes = new HashSet<Node>();
        /**5.19**/


        List<List<String>> AllconnectedPaths;//存储所有可能的paths(path中的元素是nodeId)
        List<List<Node>> AllconnectedPathsNode_intomount;//存储merge into mount这种情况的所有可能paths(path中的元素是node)
        List<List<Node>> AllconnectedPathsNode_intotree;//存储merge into tree这种情况的所有可能paths(path中的元素是node)
        List<List<Node>> AllconnectedPathsNode_triangle;//存储merge tree and mount这种情况的所有可能paths(path中的元素是node)


        /**找mntPt及其所有可能的paths 并进行添加**/

        //初始化path要添加的nodes集合
        List<Node> eachPathAddedNodes = new ArrayList<Node>();
        //初始化path要添加的links集合
        List<DefaultLink> eachPathAddedLinks = new ArrayList<DefaultLink>();
        List<DefaultLink> eachPathAddedLinks_intomount = new ArrayList<DefaultLink>();
        List<DefaultLink> eachPathAddedLinks_intotree = new ArrayList<DefaultLink>();
        List<DefaultLink> eachPathAddedLinks_treeroot = new ArrayList<DefaultLink>();
        List<DefaultLink> eachPathAddedLinks_mntPtsource = new ArrayList<DefaultLink>();
        //已完成找路径的mntPt semantic type集合,Map<String,Srting>中存放的为link的source node id和link上的信息(uri)
        Set<String> mntPtcomplete = new HashSet<String>();
        //获取每个待添加columnnode的所有可能semantictypes
        /**这个地方是不是还要考虑其正确的user semantic type？(2022.5.8)**/
        List<SemanticType> candidatesemantictypes = getCandidateSteinerSets(Attribution, true, 4);
        System.out.println(Attribution.getColumnName() + "的candidatesemantictypes大小：" + candidatesemantictypes.size() + "||candidatesemantictypes:" + candidatesemantictypes);
        /**对于每个待添加的column node,mntPts中存储的应该是integration graph中和此column node的semantic types相同的nodes**/
        Set<DefaultLink> mntPts = new HashSet<DefaultLink>();
        //遍历每个node的semantic type,找到在integration graph中与该semantic type相同的nodes
        for (SemanticType semantictype : candidatesemantictypes) {
            for (DefaultLink link : Gint.edgeSet()) {
                if ((link.getSource().getUri().equals(semantictype.getDomain().getUri())) && (link.getUri().equals(semantictype.getType().getUri()))) {
                    mntPts.add(link);//优化  存储link.getSource_Id及link.getUri
                }
            }
        }
        System.out.println("mntPts.size():" + mntPts.size());

        Set<List<DefaultLink>> AllPaths = new HashSet<List<DefaultLink>>();
        Set<List<DefaultLink>> AllPaths_1 = null;
        Set<List<DefaultLink>> AllPaths_2 = null;
        Set<List<DefaultLink>> AllPaths_3 = null;
//        Set<Node> tree_AncestorNodes = new HashSet<Node>();//存储ST(tree)的root在integration graph中的ancestor nodes
//        tree_AncestorNodes = findAncestorNodesInIntegrationGraph(Gint,Root);//获得tree的ancestornodes列表
        /**找所有可能的paths并进行添加(分两大种情况)  1.直接映射  2.tree和mntPt的merge**/
        //遍历所有可能的mntPt
        for (DefaultLink mntPt : mntPts) {
            //存储当前mntPt的所有可能paths(path中的元素为要添加的links) 最后要依据此列表来添加nodes和links
            AllPaths_1 = new HashSet<List<DefaultLink>>();//intomount
            AllPaths_2 = new HashSet<List<DefaultLink>>();//intotree
            AllPaths_3 = new HashSet<List<DefaultLink>>();//triangle

            /**已完成找路径的mntPt集合  判断要添加的columnnode在integration graph中的映射的具有相同semantic type的link是否重复
             * 如果重复就进入下一次循环
             * 否则就找其connctedPaths**/
            if (mntPtcomplete.contains(mntPt.getSource().getId() + "||" + mntPt.getUri())) {
                continue;
            }
            mntPtcomplete.add(mntPt.getSource().getId() + "||" + mntPt.getUri());

            boolean ExistInIntegrationGraph = false;//判断此mntPt的source node是否在semantic model tree中
            boolean IsRoot = false;//判断此mntPt的source node是否为semantic model tree中的root
            System.out.println("mntPt:" + mntPt.getSource().getId());

            /**2022.5.8 21：47**/
            /**一.直接映射**/
            //判断此mntPt的source node是否在StartSearchState(ST)中
            //如果此mntPt的source node在StartSearchState(ST)中,则只需要直接映射到StartSearchState(ST)中,添加此mntPt的target node
            //检查StartSearchState(ST)的所有Internal nodes或nodes中是否包含mntPt的source node
            if (ST.getGraph().vertexSet().contains(mntPt.getSource())) {
                String mntPtlinkId = LinkIdFactory.getLinkId(mntPt.getId(), mntPt.getSource().getId(), Attribution.getId());
//                System.out.println("mntPtlinkId:" + mntPt.getId());
                LabeledLink mntPtlink = new DataPropertyLink(mntPtlinkId, new Label(mntPt.getUri()));

                InitialStartSearchStateSM = ST.clone();
                System.out.println("Direct方式添加attr时,初始StartSearchState的nodes.size:" + ST.getGraph().vertexSet().size());
                System.out.println("Direct方式添加attr时,初始StartSearchState的links.size:" + ST.getGraph().edgeSet().size());
                /**添加target node**/
                InitialStartSearchStateSM.getGraph().addVertex(Attribution);
                /**添加link**/
                InitialStartSearchStateSM.getGraph().addEdge(mntPt.getSource(), Attribution, mntPtlink);
                MergeIntoTreenumber++;

                GraphVizUtil.exportSemanticModelToGraphviz(InitialStartSearchStateSM, GraphVizLabelType.LocalId,
                        GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\next-state-graph\\" + "next_state_Direct" + MergeIntoTreenumber + ".graph.json" + ".dot");

                newTrees.add(InitialStartSearchStateSM);
//                IsSemanticModeHasOnlyRoot(InitialStartSearchStateSM);//判断是否为tree
                System.out.println("Direct方式添加attr后,NextSearchState的nodes.size:" + InitialStartSearchStateSM.getGraph().vertexSet().size());
                System.out.println("Direct方式添加attr后,NextSearchState的links.size:" + InitialStartSearchStateSM.getGraph().edgeSet().size());
                continue;
            }
            /**一.直接映射**/

            /**二.merge tree和mount**/
            //如果此mntPt的source node不在StartSearchState(ST)中,则需要找三种类型的所有paths,并按照paths添加到StartSearchState(ST)中
            else {
                AllconnectedPathsNode_intomount = new ArrayList<List<Node>>();//intomount
                AllconnectedPathsNode_intotree = new ArrayList<List<Node>>();//intotree
                AllconnectedPathsNode_triangle = new ArrayList<List<Node>>();//triangle

                //初始化要添加的mntPt link
                String mntPtlinkId = LinkIdFactory.getLinkId(mntPt.getId(), mntPt.getSource().getId(), Attribution.getId());
//                System.out.println("mntPtlinkId:" + mntPt.getId());
                LabeledLink mntPtlink = new DataPropertyLink(mntPtlinkId, new Label(mntPt.getUri()));
                //添加mntPt的node(source node和target node)及其link
                MergeInitialStartSearchStateSM = ST.clone();
                System.out.println("Merge方式添加atrr时,初始StartSearchState的nodes.size:" + ST.getGraph().vertexSet().size());
                System.out.println("Merge方式添加atrr时,初始StartSearchState的links.size:" + ST.getGraph().edgeSet().size());

                /**添加mntPt**/
                MergeInitialStartSearchStateSM.getGraph().addVertex(Attribution);//添加mntPt的target node
                MergeInitialStartSearchStateSM.getGraph().addVertex(mntPt.getSource());//添加mntPt的source node
                MergeInitialStartSearchStateSM.getGraph().addEdge(mntPt.getSource(), Attribution, mntPtlink);//添加表示mntPt的link
                /**添加mntPt**/

//                System.out.println("Merge方式添加atrr时,添加mntPt-link后MergeInitialStartSearchStateSM的nodes.size:" + MergeInitialStartSearchStateSM.getGraph().vertexSet().size());
//                System.out.println("Merge方式添加atrr时,添加mntPt-link后MergeInitialStartSearchStateSM的links.size:" + MergeInitialStartSearchStateSM.getGraph().edgeSet().size());


                /**1.tree添加到mntPt的paths  intomount**/
                //以mntPt的source node为source,以tree的root为target 找到所有可能的paths(此时path中的元素为node)  path长度最大为3:表示mntPt和tree-root之间最多间隔一个node
                //取出root在integration graph中的mapping nodes set  改Root->RootList

//                for(Node root: RootList){
//                    //遍历每个root 查找其在integration graph中的映射nodes
//                    RootMappingNodes = SearchStateInternalnodesMappingIntegrationGraph.get(root);
//                    System.out.println("RootMappingNodesPerRoot:" + RootMappingNodes.size());
//                    //遍历每个root映射到integration中的nodes
//                    for (Node rootmappingnode : RootMappingNodes) {
//                        connectedPathsNode = new ArrayList<List<Node>>();
//                        findAllPathNode(IntegrationGraphLinks, mntPt.getSource().getId(), rootmappingnode.getId(), 2);
//
//                        AllconnectedPathsNode_intomount.addAll(connectedPathsNode);
//                    }
//                }

                //以mntPt的source node为source,以tree的internal node为target 找到所有可能的paths(此时path中的元素为node)  path长度最大为3:表示mntPt和tree-root之间最多间隔一个node
                //取出internal node在integration graph中的mapping nodes set  改Root->RootList
//                for(Node node: ST.getInternalNodes()){
//                    //遍历每个root 查找其在integration graph中的映射nodes
//                    InternalnodeintreeMappingNodes = SearchStateInternalnodesMappingIntegrationGraph.get(node);
//                    System.out.println("RootMappingNodesPerRoot:" + InternalnodeintreeMappingNodes.size());
//                    //遍历每个root映射到integration中的nodes
//                    for (Node internalmappingnode : InternalnodeintreeMappingNodes) {
//                        connectedPathsNode = new ArrayList<List<Node>>();
//                        findAllPathNode(IntegrationGraphLinks, mntPt.getSource().getId(), internalmappingnode.getId(), 3);
//
//                        AllconnectedPathsNode_intomount.addAll(connectedPathsNode);
//                    }
//                }
                RootMappingNodes = SearchStateInternalnodesMappingIntegrationGraph.get(Root);
                System.out.println("RootMappingNodesPerRoot:" + RootMappingNodes.size());
                //遍历每个root映射到integration中的nodes
                for (Node rootmappingnode : RootMappingNodes) {
                    connectedPathsNode = new ArrayList<List<Node>>();
                    findAllPathNode(IntegrationGraphLinks, mntPt.getSource().getId(), rootmappingnode.getId(), 3);
                    AllconnectedPathsNode_intomount.addAll(connectedPathsNode);
                }

                System.out.println("AllconnectedPathsNode_intomount.size1:" + mntPt.getId() + "||" + AllconnectedPathsNode_intomount.size());

                //以set的形式暂存当前node pair的links
                Set<DefaultLink> temp_nodepair_links_intomount = null;
                for (List<Node> path : AllconnectedPathsNode_intomount) {
                    eachPathAddedLinks = new ArrayList<DefaultLink>();
                    //存储每个path要添加的links信息
                    for (int i = 0; i < path.size() - 1; i++) {
                        temp_nodepair_links_intomount = new HashSet<DefaultLink>();
                        /**检查当前pathnode的nodes(除tree-root外)是否存在于StartSearchState的InternalNodes中  避免出现环**/
                        if (ST.getGraph().vertexSet().contains(path.get(i))) {
                            eachPathAddedLinks = new ArrayList<DefaultLink>();
                            break;
                        } else {
                            for (DefaultLink integrationlink : Gint.edgeSet()) {
                                if ((integrationlink.getSource().getId().equals(path.get(i).getId())) && (integrationlink.getTarget().getId().equals(path.get(i + 1).getId()))) {
                                    temp_nodepair_links_intomount.add(integrationlink);//存储了当前node pair所有links
                                }
                            }
                            //计算temp_nodepair_links中defaultlink的数量
                            int defaultlinknum = 0;
                            for (DefaultLink link : temp_nodepair_links_intomount) {
                                if (link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink")) {
                                    defaultlinknum++;
                                }
                            }
                            if (defaultlinknum == temp_nodepair_links_intomount.size()) {
//                                System.out.println("AllPath1_添加了defaultlink");
//                                eachPathAddedLinks = new ArrayList<DefaultLink>();
//                                break;
                                eachPathAddedLinks.add(new ArrayList<DefaultLink>(temp_nodepair_links_intomount).get(0));
                            } else {
//                                System.out.println("AllPath1_添加了nondefaultlink");
                                for (DefaultLink link : temp_nodepair_links_intomount) {
                                    if (!(link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink"))) {
                                        System.out.println(link.getId());
                                        eachPathAddedLinks.add(link);
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    if (eachPathAddedLinks.size() == (path.size() - 1)) {
                        AllPaths_1.add(eachPathAddedLinks);
                    }
                }
                AllPaths.addAll(AllPaths_1);
                System.out.println("AllPaths_1.size:" + mntPt.getId() + "||" + AllPaths_1.size());
                System.out.println("AllPaths.size:" + mntPt.getId() + "||" + AllPaths.size());


                /**2.mntPt添加到tree的paths  intotree  注意此时mntPt的class node(source node)不在tree中**/
                //以tree中的任一class node为source,以mntPt的source node为target  找到所有可能的paths(此时path中的元素为node)
                //判断mntPt的class node是否在tree中  如果在tree中 则跳过 不为其查找添加到tree中的paths 然后检查下一个mntPt  否则,为其查找添加到tree中的paths
//                System.out.println("判断mntPt的class node是否在tree中");
                if (ST.getGraph().vertexSet().contains(mntPt.getSource())) {
//                    System.out.println("mntPt的class node在ST tree中");
                    continue;
                } else {
//                    System.out.println("mntPt的class node不在ST tree中");
                    //遍历tree(ST)中每个Internal node(共11个internal node)
                    for (Node internalnodeIntree : ST.getInternalNodes()) {
                        //取出每个internalnodeIntree在Integration Graph中对应的nodes列表
                        InternalnodeintreeMappingNodes = SearchStateInternalnodesMappingIntegrationGraph.get(internalnodeIntree);
                        //遍历InternalnodeintreeMappingNodes集合,以每个node为source,以mntPt的source node为target,找到所有可能的paths(此时path中的元素为node)
                        System.out.println("InternalnodeintreeMappingNodes.size:" + InternalnodeintreeMappingNodes.size());
                        for (Node internalnodeintreemappingnode : InternalnodeintreeMappingNodes) {
//                            System.out.println("找paths");
                            connectedPathsNode = new ArrayList<List<Node>>();
                            findAllPathNode(IntegrationGraphLinks, internalnodeintreemappingnode.getId(), mntPt.getSource().getId(), 3);
                            for (List<Node> pathnode : connectedPathsNode) {
                                AllconnectedPathsNode_intotree.add(pathnode);
                            }
//                            System.out.println("以每个internalnodeintreemappingnode为source的connectedPathsNode.size:" + connectedPathsNode.size());
                        }
                    }
                }
                System.out.println("AllconnectedPathsNode_intotree.size2:" + mntPt.getId() + "||" + AllconnectedPathsNode_intotree.size());
                //以set的形式暂存当前node pair的links
                Set<DefaultLink> temp_nodepair_links_intotree = null;
                for (List<Node> path : AllconnectedPathsNode_intotree) {
                    eachPathAddedLinks = new ArrayList<DefaultLink>();
                    //存储每个path要添加的links信息
                    for (int i = 0; i < path.size() - 1; i++) {
                        temp_nodepair_links_intotree = new HashSet<DefaultLink>();
                        /**依次遍历path中的node pair(1-2,2-3,3-4...)
                         * 检查当前node pair是否在tree中有路径 如果有则不添加node pair之间对应到integration graph上的link信息
                         * 如果没有则添加对应到integration graph上的link信息**/
                        connectedPathsNode = new ArrayList<List<Node>>();
                        findAllPathNode(SearchStateLinks, path.get(i).getId(), path.get(i + 1).getId(), 50);//长度变更
                        if (connectedPathsNode.size() > 0) {
                            continue;
                        }
                        /**如果path.size()>2 检查当前pathnode的nodes(除第一个node外)是否存在于StartSearchState的InternalNodes中  避免出现环**/
//                        if(path.size()>2) {
                        if ((i!=path.size()-2)&&(ST.getGraph().vertexSet().contains(path.get(i + 1)))) {
                            eachPathAddedLinks = new ArrayList<DefaultLink>();
                            break;
                        }
                        else {
                            for (DefaultLink integrationlink : Gint.edgeSet()) {
//                            if ((integrationlink.getSource().getId().equals(path.get(i).getId())) && (integrationlink.getTarget().getId().equals(path.get(i + 1).getId()))) {//待添加的links
//                                eachPathAddedLinks.add(integrationlink);
//                                break;
//                            }
                                if ((integrationlink.getSource().getId().equals(path.get(i).getId())) && (integrationlink.getTarget().getId().equals(path.get(i + 1).getId()))) {
                                    temp_nodepair_links_intotree.add(integrationlink);//存储了当前node pair所有links
                                }
                            }
                            //计算temp_nodepair_links中defaultlink的数量
                            int defaultlinknum = 0;
                            for (DefaultLink link : temp_nodepair_links_intotree) {
                                if (link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink")) {
                                    defaultlinknum++;
                                }
                            }
                            if (defaultlinknum == temp_nodepair_links_intotree.size()) {
//                            System.out.println("AllPath2_添加了defaultlink");
//                                eachPathAddedLinks = new ArrayList<DefaultLink>();
//                                break;
                                eachPathAddedLinks.add(new ArrayList<DefaultLink>(temp_nodepair_links_intotree).get(0));
                            } else {
//                            System.out.println("AllPath2_添加了nondefaultlink");
                                for (DefaultLink link : temp_nodepair_links_intotree) {
                                    if (!(link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink"))) {
                                        System.out.println("path2中的link.getId:"+link.getId());
                                        eachPathAddedLinks.add(link);
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    if (eachPathAddedLinks.size() == (path.size()-1)) {
                        AllPaths_2.add(eachPathAddedLinks);
                    }
                }
                AllPaths.addAll(AllPaths_2);
                System.out.println("AllPaths_2.size:" + mntPt.getId() + "||" + AllPaths_2.size());
                System.out.println("AllPaths.size:" + mntPt.getId() + "||" + AllPaths.size());

                /**3.mntPt和tree到common nodes的paths**/
                //分别查找mntPt和tree在integration graph中的ancestor nodes
                Set<Node> mntPt_AncestorNodes = new HashSet<Node>();
                mntPt_AncestorNodes = findAncestorNodesInIntegrationGraph(Gint,mntPt.getSource());//获得mntPt的ancestornodes列表
                //遍历每个Root 找到其tree_AncestorNodes
                Set<Node> tree_AncestorNodes = new HashSet<Node>();//存储ST(tree)的root在integration graph中的ancestor nodes
                for(Node root: RootList){
                    Set<Node> tree_ANsCommonWithmntPt_AN = new HashSet<Node>();
//                System.out.println(mntPt.getId()+"的mntPt和tree到common nodes的paths");
                    tree_AncestorNodes = new HashSet<Node>();
                    tree_AncestorNodes = findAncestorNodesInIntegrationGraph(Gint,root);
                    System.out.println("mntPt_AncestorNodes的初始大小："+mntPt_AncestorNodes.size());
                    System.out.println("tree_AncestorNodes的初始大小："+tree_AncestorNodes.size());
                    tree_ANsCommonWithmntPt_AN.addAll(tree_AncestorNodes);
                    tree_ANsCommonWithmntPt_AN.retainAll(mntPt_AncestorNodes);
                    System.out.println("tree_AncestorNodes和mntPt_AncestorNodes的交集大小" + tree_ANsCommonWithmntPt_AN.size());
                    //遍历tree_ANsCommonWithmntPt_AN  找到其中每一个节点到tree root的commonnode_tree_paths和到mntPt source node的commonnode_mntPt_paths
                    for(Node commonnode: tree_ANsCommonWithmntPt_AN) {
                        if (!ST.getGraph().vertexSet().contains(commonnode)){//避免出现环
                            connectedPathsNode = new ArrayList<List<Node>>();
                            connectedPathsNode_ANs_tree = new HashSet<List<Node>>();
                            connectedPathsNode_ANs_mntPt = new HashSet<List<Node>>();
                            List<List<DefaultLink>> pathTreeMntPtPerCommon = new ArrayList<List<DefaultLink>>();
                            //以common node为source,以tree root为target
                            findAllPathNode(IntegrationGraphLinks, commonnode.getId(), Root.getId(), 3);
                            connectedPathsNode_ANs_tree.addAll(connectedPathsNode);
//                          System.out.println("connectedPathsNode_ANs_tree-connectedPathsNode的大小：" + connectedPathsNode.size());
//                          System.out.println("connectedPathsNode_ANs_tree的大小：" + connectedPathsNode_ANs_tree.size());
//                          System.out.println("connectedPathsNode_ANs_tree的get(0)的大小：" + new ArrayList<>(connectedPathsNode_ANs_tree).get(0).size());
                            //以common node为source,以mntPt source node为target
                            connectedPathsNode = new ArrayList<List<Node>>();
                            findAllPathNode(IntegrationGraphLinks, commonnode.getId(), mntPt.getSource().getId(), 3);
                            connectedPathsNode_ANs_mntPt.addAll(connectedPathsNode);
//                          System.out.println("connectedPathsNode_ANs_mntPt-connectedPathsNode的大小：" + connectedPathsNode.size());
//                          System.out.println("connectedPathsNode_ANs_mntPt的大小：" + connectedPathsNode_ANs_mntPt.size());
//                          System.out.println("connectedPathsNode_ANs_mntPt的get(0)的大小：" + new ArrayList<>(connectedPathsNode_ANs_mntPt).get(0).size());

                            //以set的形式暂存当前node pair的links
                            Set<DefaultLink> temp_nodepair_links = null;
                            for (List<Node> path_ans_tree : connectedPathsNode_ANs_tree) {
                                eachPathAddedLinks_treeroot = new ArrayList<DefaultLink>();
                                //存储每个path要添加的links信息
                                for (int i = 0; i < path_ans_tree.size() - 1; i++) {
                                    /**依次遍历path中的node pair(1-2,2-3,3-4...)
                                     * 添加对应到integration graph上的link信息**/
                                    //以set的形式暂存当前node pair的links
                                    temp_nodepair_links = new HashSet<DefaultLink>();
                                    /**检查当前pathnode的nodes(除tree-root外)是否存在于StartSearchState的InternalNodes中  避免出现环**/
                                    if ((i!=path_ans_tree.size()-2)&&(ST.getGraph().vertexSet().contains(path_ans_tree.get(i + 1)))) {
                                        eachPathAddedLinks_treeroot = new ArrayList<DefaultLink>();
                                        break;
                                    }
                                    else{
                                        for (DefaultLink integrationlink : Gint.edgeSet()) {
                                            if ((integrationlink.getSource().getId().equals(path_ans_tree.get(i).getId())) && (integrationlink.getTarget().getId().equals(path_ans_tree.get(i + 1).getId()))) {
                                                temp_nodepair_links.add(integrationlink);//存储了当前node pair所有links
                                            }
                                        }
                                        //计算temp_nodepair_links中defaultlink的数量
                                        int defaultlinknum = 0;
                                        for (DefaultLink link : temp_nodepair_links) {
                                            if (link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink")) {
                                                defaultlinknum++;
                                            }
                                        }
                                        if (defaultlinknum == temp_nodepair_links.size()) {
//                                            System.out.println("添加了defaultlink");
//                                            eachPathAddedLinks_treeroot = new ArrayList<DefaultLink>();
//                                            break;
                                            eachPathAddedLinks_treeroot.add(new ArrayList<DefaultLink>(temp_nodepair_links).get(0));
                                        } else {
//                                            System.out.println("添加了nondefaultlink");
                                            for (DefaultLink link : temp_nodepair_links) {
                                                if (!(link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink"))) {
//                                              System.out.println(link.getId());
                                                    eachPathAddedLinks_treeroot.add(link);
                                                    break;
                                                }
                                            }
                                        }
                                    }
                                }
                                if(eachPathAddedLinks_treeroot.size()==0){
                                    continue;
                                }
//                              System.out.println("eachPathAddedLinks_treeroot的get(0)的大小：" + eachPathAddedLinks_treeroot.size());
//                              System.out.println("结束了一次path_ans_tree");

                                for (List<Node> path_ans_mntPt : connectedPathsNode_ANs_mntPt) {
                                    //这里判断如果两个childpath大小之和大于5 则continue 否则继续以下操作
                                    if((path_ans_tree.size()+path_ans_mntPt.size())>5){
                                        continue;
                                    }
                                    eachPathAddedLinks_mntPtsource = new ArrayList<DefaultLink>();
                                    //存储每个path要添加的links信息
                                    for (int i = 0; i < path_ans_mntPt.size() - 1; i++) {
                                        /**依次遍历path中的node pair(1-2,2-3,3-4...)
                                         * 添加对应到integration graph上的link信息**/
                                        //以set的形式暂存当前node pair的links
                                        temp_nodepair_links = new HashSet<DefaultLink>();
                                        /**检查当前pathnode的nodes(除mntPt source node外)是否存在于StartSearchState的InternalNodes中  避免出现环**/
                                        if ((ST.getGraph().vertexSet().contains(path_ans_mntPt.get(i + 1)))) {
                                            eachPathAddedLinks_mntPtsource = new ArrayList<DefaultLink>();
                                            break;
                                        }
                                        for (DefaultLink integrationlink : Gint.edgeSet()) {
                                            if ((integrationlink.getSource().getId().equals(path_ans_mntPt.get(i).getId())) && (integrationlink.getTarget().getId().equals(path_ans_mntPt.get(i + 1).getId()))) {
                                                temp_nodepair_links.add(integrationlink);//存储了当前node pair所有links
                                            }
                                        }
                                        //计算temp_nodepair_links中defaultlink的数量
                                        int defaultlinknum = 0;
                                        for (DefaultLink link : temp_nodepair_links) {
                                            if (link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink")) {
                                                defaultlinknum++;
                                            }
                                        }
                                        if (defaultlinknum == temp_nodepair_links.size()) {
//                                          System.out.println("在mntPt时添加了defaultlink");
//                                          eachPathAddedLinks_mntPtsource = new ArrayList<DefaultLink>();
//                                          break;
                                            eachPathAddedLinks_mntPtsource.add(new ArrayList<DefaultLink>(temp_nodepair_links).get(0));
                                        } else {
//                                          System.out.println("在mntPt时添加了nondefaultlink");
                                            for (DefaultLink link : temp_nodepair_links) {
                                                if (!(link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink"))) {
//                                                  System.out.println(link.getId());
                                                    eachPathAddedLinks_mntPtsource.add(link);
                                                    break;
                                                }
                                            }
                                        }
                                    }
//                                  System.out.println("eachPathAddedLinks_mntPtsource的get(0)的大小：" + eachPathAddedLinks_mntPtsource.size());

                                    List<DefaultLink> path_tree_with_mntPt = new ArrayList<DefaultLink>();
                                    if(eachPathAddedLinks_mntPtsource.size()>0) {
//                                        path_tree_with_mntPt.addAll(eachPathAddedLinks_treeroot);
                                        if (!(eachPathAddedLinks_treeroot.get(0).getUri().toString().equals(eachPathAddedLinks_mntPtsource.get(0).getUri().toString()))) {
                                            path_tree_with_mntPt.addAll(eachPathAddedLinks_treeroot);
                                            path_tree_with_mntPt.addAll(eachPathAddedLinks_mntPtsource);
                                        } else {
                                            continue;
                                        }
                                    }
                                    else{
                                        continue;
                                    }
                                    int commonnodenum = 0;
                                    for(DefaultLink link: path_tree_with_mntPt){
                                        if(link.getSource().getId().equals(commonnode.getId())){
                                            commonnodenum++;
                                        }
                                    }
                                    if(commonnodenum==2) {
                                        pathTreeMntPtPerCommon.add(path_tree_with_mntPt);
                                    }
                                }
                            }
//                          if(pathTreeMntPtPerCommon.size()>0) {
//                              System.out.println("pathTreeMntPtPerCommon的大小：" + pathTreeMntPtPerCommon.get(0).size());
//                          }

//                          if(pathTreeMntPtPerCommon.size()>0) {
//                              System.out.println("pathTreeMntPtPerCommon的大小：" + pathTreeMntPtPerCommon.size());
//                          }
                            if(pathTreeMntPtPerCommon.size()>0) {
                                AllPaths_3.addAll(pathTreeMntPtPerCommon);
                            }
                        }
                    }
                }

                System.out.println(mntPt.getId() + "的AllPaths_3大小" + AllPaths_3.size());
                /**3.mntPt和tree到common nodes的paths**/

                //遍历tree的ancestor nodes
                //查看mntPt的ancestor nodes中是否包含当前的tree ancestor node
                //如果包含则取该node为common node,查找common node到tree root node的path以及common node到mntPt source node的path
                //依据这一对path添加信息 生成triangle类型的nextsearchstate

            }
            /**二.merge tree和mount**/

            /**添加其中任意一种类型(如AllPaths_1)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/
            for(List<DefaultLink> addpath: AllPaths_1){
                if(addpath.size()>0) {
                    NextSearchStateSM = MergeInitialStartSearchStateSM.clone();
//            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().vertexSet().size());
//            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().edgeSet().size());
                    for (int i = 0; i < addpath.size(); i++) {
                        LabeledLink addedlink = new DataPropertyLink(addpath.get(i).getId(), new Label(addpath.get(i).getUri()));
                        NextSearchStateSM.getGraph().addVertex(addpath.get(i).getSource());
                        NextSearchStateSM.getGraph().addVertex(addpath.get(i).getTarget());
                        NextSearchStateSM.getGraph().addEdge(addpath.get(i).getSource(), addpath.get(i).getTarget(), addedlink);
                    }
                    MergeIntoTreenumber++;

                    /**保存Json文件**/

                    /**保存dot文件**/
                    GraphVizUtil.exportSemanticModelToGraphviz(NextSearchStateSM, GraphVizLabelType.LocalId,
                            GraphVizLabelType.LocalUri, false, false, Params.ROOT_DIR+"next-state-graph\\" + "next_state_IntoMount" + Beam_Search + "_" + MergeIntoTreenumber + ".graph.json" + ".dot");

                    newTrees.add(NextSearchStateSM);
//                IsSemanticModeHasOnlyRoot(NextSearchStateSM);//判断是否为tree
                    System.out.println("NextSearchStateSM的nodes:" + NextSearchStateSM.getGraph().vertexSet().size());
                    System.out.println("NextSearchStateSM的links:" + NextSearchStateSM.getGraph().edgeSet().size());
                }
            }
            /**添加其中任意一种类型(如AllPaths_1)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/

            /**添加其中任意一种类型(如AllPaths_2)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/
            for(List<DefaultLink> addpath: AllPaths_2){
                if(addpath.size()>0) {
                    NextSearchStateSM = MergeInitialStartSearchStateSM.clone();
//            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().vertexSet().size());
//            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().edgeSet().size());
                    for (int i = 0; i < addpath.size(); i++) {
                        LabeledLink addedlink = new DataPropertyLink(addpath.get(i).getId(), new Label(addpath.get(i).getUri()));
                        NextSearchStateSM.getGraph().addVertex(addpath.get(i).getSource());
                        NextSearchStateSM.getGraph().addVertex(addpath.get(i).getTarget());
                        NextSearchStateSM.getGraph().addEdge(addpath.get(i).getSource(), addpath.get(i).getTarget(), addedlink);
                    }
                    MergeIntoTreenumber++;

                    GraphVizUtil.exportSemanticModelToGraphviz(NextSearchStateSM, GraphVizLabelType.LocalId,
                            GraphVizLabelType.LocalUri, false, false, Params.ROOT_DIR+"next-state-graph\\" + "next_state_IntoTree" + Beam_Search + "_" + MergeIntoTreenumber + ".graph.json" + ".dot");

                    newTrees.add(NextSearchStateSM);
//                IsSemanticModeHasOnlyRoot(NextSearchStateSM);//判断是否为tree
                    System.out.println("NextSearchStateSM的nodes:" + NextSearchStateSM.getGraph().vertexSet().size());
                    System.out.println("NextSearchStateSM的links:" + NextSearchStateSM.getGraph().edgeSet().size());
                }
            }
            /**添加其中任意一种类型(如AllPaths_2)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/

            /**添加其中任意一种类型(如AllPaths_3)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/
            for(List<DefaultLink> addpath: AllPaths_3){
//                System.out.println("AllPaths_3:" + addpath.size());
                if(addpath.size()>0) {
                    NextSearchStateSM = MergeInitialStartSearchStateSM.clone();
//            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().vertexSet().size());
//            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().edgeSet().size());
                    for (int i = 0; i < addpath.size(); i++) {
                        LabeledLink addedlink = new DataPropertyLink(addpath.get(i).getId(), new Label(addpath.get(i).getUri()));
                        NextSearchStateSM.getGraph().addVertex(addpath.get(i).getSource());
                        NextSearchStateSM.getGraph().addVertex(addpath.get(i).getTarget());
                        NextSearchStateSM.getGraph().addEdge(addpath.get(i).getSource(), addpath.get(i).getTarget(), addedlink);
                    }
                    MergeIntoTreenumber++;

                    GraphVizUtil.exportSemanticModelToGraphviz(NextSearchStateSM, GraphVizLabelType.LocalId,
                            GraphVizLabelType.LocalUri, false, false, Params.ROOT_DIR+"next-state-graph\\" + "next_state_triangle" + Beam_Search + "_" + MergeIntoTreenumber + ".graph.json" + ".dot");

                    newTrees.add(NextSearchStateSM);
//                IsSemanticModeHasOnlyRoot(NextSearchStateSM);//判断是否为tree
                    System.out.println("NextSearchStateSM的nodes:" + NextSearchStateSM.getGraph().vertexSet().size());
                    System.out.println("NextSearchStateSM的links:" + NextSearchStateSM.getGraph().edgeSet().size());
                }
            }
            /**添加其中任意一种类型(如AllPaths_3)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/

            /**2022.5.8 22：10 注释**/
//            /**判断mntPt类型(三种)**/
//            for (Node i : SearchStateInternalnodesMappingIntegrationGraph.keySet()) {
//                /**判断mntPt的source是不是已经存在于semantic model tree中
//                 * 1.如果存在于semantic model tree中，并且不是映射到semantic model tree的root上，则只需要找semantic model tree的root到mntPt的source node之间的路径
//                 * 2.如果此mntPt的source node映射到semantic model tree中的root上，则需要找common node将semantic model tree与mntPt连接起来
//                 * 3.如果mntPt的source node不存在于semantic model tree中,则找semantic model tree中的任意internal node到mntPt的source node之间的路径**/
//                if (SearchStateInternalnodesMappingIntegrationGraph.get(i).contains(mntPt.getSource())) {
//                    ExistInIntegrationGraph = true;//mntPt的source node存在于semantic model tree中
//                    if (mntPt.getSource().getId().equals(Root.getId())) {
//                        IsRoot = true;
//                    }
//                    break;
//                }
//            }
//            System.out.println("ExistInIntegrationGraph:" + ExistInIntegrationGraph);
//            System.out.println("IsRoot:" + IsRoot);
//
//
//            //1.如果mntPt的source node存在于semantic model tree中，并且为semantic model tree中的root，则需找common node将两者联系起来
//            if (ExistInIntegrationGraph && IsRoot) {
//                //保存每个mntPt的所有的待添加路径信息
//                AllconnectedPaths = new ArrayList<List<String>>();
//                AllconnectedPathsNode = new ArrayList<List<Node>>();
//                System.out.println("找common node----------");
//            }
//            //2.如果mntPt的source node存在于semantic model tree中，且不为root，则需找root到mntPt之间的路径
//            else if (ExistInIntegrationGraph) {
//                //保存每个mntPt的所有的待添加路径信息
//                AllconnectedPaths = new ArrayList<List<String>>();
//                AllconnectedPathsNode = new ArrayList<List<Node>>();
//
//                System.out.println("找root到mntPt之间的路径----------");
//                //取出root在integration graph中的mapping nodes set
//                RootMappingNodes = SearchStateInternalnodesMappingIntegrationGraph.get(Root);
//                System.out.println("RootMappingNodes:" + RootMappingNodes.size());
//
//                //遍历每个root到integration中的nodes
//                for (Node rootmappingnode : RootMappingNodes) {
//                    System.out.println("rootmappingnode:" + rootmappingnode.getId() + "||" + mntPt.getSource().getId());
//                    connectedPathsNode = new ArrayList<List<Node>>();
//                    findAllPathNode(IntegrationGraphLinks, rootmappingnode.getId(), mntPt.getSource().getId(), 3);
//                    System.out.println("connectedPathsNode.size:" + connectedPathsNode.size());
//                    //connectedPaths ← all paths that connect leaves or root of st with mntPt
//                    int index = 0;//用于测试,对于每个要添加的node,现只连接其第一条路径
//
//                    //获得每个mntPt的所有待添加路径信息
//                    for (List<Node> path : connectedPathsNode) {
//                        AllconnectedPathsNode.add(path);
//                    }
//
//                    System.out.println("AllconnectedPathsNode.size:" + AllconnectedPathsNode.size());
//                    for (List<Node> path : AllconnectedPathsNode) {
//                        InitialStartSearchStateSM = ST.clone();
//                        System.out.println("初始化时StartSearchState的nodes:" + ST.getGraph().vertexSet().size());
//                        System.out.println("初始化时StartSearchState的links:" + ST.getGraph().edgeSet().size());
//
//                        eachPathAddedNodes.add(Attribution);//添加需要add的mntPt target(column) node
//                        /**添加target node**/
//                        InitialStartSearchStateSM.getGraph().addVertex(Attribution);
//                        /**添加mntPt**/
//                        String mntPtlinkId = LinkIdFactory.getLinkId(mntPt.getId(), mntPt.getSource().getId(), Attribution.getId());
//                        System.out.println("mntPtlinkId:" + mntPt.getId());
//                        LabeledLink mntPtlink = new DataPropertyLink(mntPtlinkId, new Label(mntPt.getUri()));
//                        InitialStartSearchStateSM.getGraph().addEdge(mntPt.getSource(), Attribution, mntPtlink);
//                        /**完成target(column) node和mntPt的添加**/
//                        System.out.println(mntPt.getSource().getId() + "的connectedPaths:" + path);
//                        //存储每个path要添加的nodes
//                        for (Node nodeInfo : path) {
//                            for (Node integrationnode : Gint.vertexSet()) {
//                                if (integrationnode.getId().equals(nodeInfo.getId())) {
////                                    InitialStartSearchState.addVertex(integrationnode);//添加每个path要add的nodes\
//                                    InitialStartSearchStateSM.getGraph().addVertex(integrationnode);
//                                    eachPathAddedNodes.add(integrationnode);
//                                }
//                            }
//                        }
////                            //输出每条(第一条)path要添加的nodes信息
////                            for(Node pathnode: eachPathAddedNodes) {
////                                //向semantic model tree中添加这些nodes
////                                System.out.println("输出每条(第一条)path要添加的nodes信息" + pathnode.getId());
////                            }////////////////////////////////////////////
//                        //存储每个path要添加的links信息
//                        for (int i = 0; i < path.size() - 1; i++) {
//                            for (DefaultLink integrationlink : Gint.edgeSet()) {
//                                if ((integrationlink.getSource().getId().equals(path.get(i).getId())) && (integrationlink.getTarget().getId().equals(path.get(i + 1).getId()))) {//待添加的links
//                                    boolean isaddedlink = true;
//                                    LabeledLink addedlink = new DataPropertyLink(integrationlink.getId(), new Label(integrationlink.getUri()));
//                                    for (LabeledLink semanticmodeltreelink : ST.getGraph().edgeSet()) {//遍历semantic model tree中的links
//                                        if (integrationlink.getId().equals(semanticmodeltreelink.getId())) {
//                                            isaddedlink = false;
//                                            break;
//                                        }
//                                    }
//                                    if (isaddedlink) {
//                                        InitialStartSearchStateSM.getGraph().addEdge(integrationlink.getSource(), integrationlink.getTarget(), addedlink);
//                                    }
//                                    eachPathAddedLinks.add(integrationlink);//测试
//                                }
//                            }
//                        }
////                            //输出每条(第一条)path要添加的links信息
////                            for(DefaultLink pathlink: eachPathAddedLinks) {
////                                //向semantic model tree中添加这些nodes
////                                System.out.println("输出每条(第一条)path要添加的links信息" + pathlink.getId());
////                            }//////////////////////////////
//
//                        /**保存添加一个target(column) node的nextsearchstate**/
//
//                        MergeIntoTreenumber++;
//
//                        GraphVizUtil.exportSemanticModelToGraphviz(InitialStartSearchStateSM, GraphVizLabelType.LocalId,
//                                GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\next-state-graph\\" + "next_state_" + MergeIntoTreenumber + ".graph.json" + ".dot");
//
//                        newTrees.add(InitialStartSearchStateSM);
//                        System.out.println("InitialStartSearchState的nodes:" + InitialStartSearchStateSM.getGraph().vertexSet().size());
//                        System.out.println("InitialStartSearchState的links:" + InitialStartSearchStateSM.getGraph().edgeSet().size());
//                    }
//                }
//            }
//            //3.如果mntPt的source node不存在于semantic model tree中,则找semantic model tree中的任意internal node到mntPt的source node之间的路径
//            else{
//                //保存每个mntPt的所有的待添加路径信息
//                AllconnectedPaths = new ArrayList<List<String>>();
//                AllconnectedPathsNode = new ArrayList<List<Node>>();
//                System.out.println("找semantic model tree中任一internal node到mntPt的source node之间的路径");
//            }
            /**2022.5.8 22：10 注释**/
        }

        return newTrees;
    }
    /**5.20 针对某一data source预测生成Semantic Models**/

    /**6.24 针对某一Positive Models所在文件夹 为其生成所有models的negative examples 以便生成其嵌入表示**/
    public static List<SemanticModel> GenNegativeExamplesPerFolderForEmbedding(int SourceSMIndex,JSONObject jsonObject) throws Exception{
//        //获取某一路径下的所有文件
//        File file = new File("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\positive-models\\positive-models-json\\");
//        File[] files = file.listFiles();
//        List<String> FilesName = new LinkedList<String>();
//        for (File subfile : files) {
//            FilesName.add(subfile.getName());
//        }
//        System.out.println("输出指定文件名:" + FilesName.get(FileIndex));
        //读入所有正确的语义模型
        if(SemanticModels == null) {
            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR +"models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
        }
//        //遍历语义模型
//        for(SemanticModel CorrectSMIn29: SemanticModels) {
            List<SemanticModel> CorrectSubSMList = new LinkedList<SemanticModel>();
        CorrectSubSMList = CorrectSubSemanticModels(SemanticModels.get(SourceSMIndex),SourceSMIndex, Params.ROOT_DIR +"positive-models/",jsonObject);
//        }
        System.out.println("输出sourcename:" + SemanticModels.get(SourceSMIndex).getName());
        /**获取integration graph**/
        DirectedWeightedMultigraph<Node, DefaultLink> IntegrationGraph = null;//集成图
        Integer[] AllSMIndex = new Integer[]{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28};
        AllSMIndex = (Integer[]) ArrayUtils.remove(AllSMIndex, SourceSMIndex);
        System.out.println("AllSMIndex:" + Arrays.toString(AllSMIndex));

        IntegrationGraph = getIntegrationGraph(SourceSMIndex, AllSMIndex);//获取除SourceSemanticModelIndex之外所有语义模型的正确语义标注组成的integration graph
        System.out.println("GenNegativeExamplesPerFolderForEmbedding中IntegrationGraph.links.size:" + IntegrationGraph.edgeSet().size());
        System.out.println("GenNegativeExamplesPerFolderForEmbedding中IntegrationGraph.nodes.size:" + IntegrationGraph.vertexSet().size());


        /**对于每个正确子语义模型 生成其negative examples及对应的embeddings 单独为correct sub semantic models生成embeddings的时候需要注释**/
//        for(int i=0;i<CorrectSubSMList.size();i++) {
//            GenNegativeExamplesForEmbedding(i,CorrectSubSMList.get(i),IntegrationGraph,jsonObject);
//        }
        /**对于每个正确子语义模型 生成其negative examples及对应的embeddings**/
        return null;
    }

    /**6.23 针对某一SemanticModel为其生成negative examples 以便生成其嵌入表示**/
    public static List<SemanticModel> GenNegativeExamplesForEmbedding(int SourceSMIndex,SemanticModel SourceSemanticModel,DirectedWeightedMultigraph<Node, DefaultLink> IntegrationGraph,JSONObject jsonObject) throws Exception{
        List<ColumnNode> Columnnodes = new ArrayList<ColumnNode>();//原始正确语义模型的Source Attributions集
//        DirectedWeightedMultigraph<Node, DefaultLink> IntegrationGraph = null;//集成图
        List<SemanticModel> StartSearchStates = new LinkedList<SemanticModel>();//原始正确语义模型在执行Elimination操作后获得的初始Search States集
        List<SemanticModel> NegativeExamples = new ArrayList<SemanticModel>();//对于每个正确语义模型的某一衍生状态 保存其生成的每种子状态的negative examples
        List<SemanticModel> NegativeExamplesPerFolder = new ArrayList<SemanticModel>();//保存正确的语义模型某一衍生状态 生成的所有negative examples

        //删除指定文件夹内容
//        File dir3=new File("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples-dot-for-embedding\\"+StartSearchStates.get(i).getName()+".Sub"+(SourceSMIndex+1)+".State"+NegExmplesIndex);
//        RemoveDir(dir3);
        File dir4=new File(Params.ROOT_DIR +"negative-examples-json-for-embedding");
        RemoveDir(dir4);

        /**获取Source Semantic Model**/
//        if(SemanticModels == null) {
//            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "positive-models\\positive-models-json\\s01.csv", Params.MODEL_MAIN_FILE_EXT);
//        }
//        System.out.println("输出GenNegativeExamplesForEmbedding中SemanticModels.size:" + SemanticModels.size());
//        SemanticModel SourceSemanticModel = SemanticModels.get(4082);//获得要生成negative examples的semantic model
        /**获取初始Start Search State列表**/
        StartSearchStates = getNewStartStatesSemanticModelForEmbedding(SourceSemanticModel);
        for(SemanticModel sm: StartSearchStates){
            System.out.println("输出每个StartSearchState.getColumnNodes.size:" + sm.getColumnNodes().size());
        }
        System.out.println("StartSearchStates.size:"+StartSearchStates.size());
        /**获取source attributions**/
        Columnnodes = SourceSemanticModel.getColumnNodes();
        System.out.println("Columnnodes.size:" + Columnnodes.size());
//        /**获取integration graph**/
//        Integer[] AllSMIndex = new Integer[]{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28};
//        AllSMIndex = (Integer[]) ArrayUtils.remove(AllSMIndex, SourceSemanticModelIndex);
//
//        IntegrationGraph = getIntegrationGraph(SourceSemanticModelIndex, AllSMIndex);//获取除SourceSemanticModelIndex之外所有语义模型的正确语义标注组成的integration graph
        System.out.println("GenNegativeExamplesForEmbedding中IntegrationGraph.links.size:" + IntegrationGraph.edgeSet().size());
        System.out.println("GenNegativeExamplesForEmbedding中IntegrationGraph.nodes.size:" + IntegrationGraph.vertexSet().size());

        /**解开**/
        //遍历所有的StartSearchStates 调用BeamSearch1 为当前SourceSemanticModel生成50个negative examples
        NegExmplesIndex = 0;
        for(int i=0;i<StartSearchStates.size();i++){
            System.out.println("对于一个sub,生成其negative examples");
            NegativeExamples = new ArrayList<SemanticModel>();
            /**创建文件夹**/
            NegExmplesIndex++;
            //根据StartSearchState 在E:\D_Drive\ASM\DataSets\museum-29-crm\negative-examples-dot-for-embedding下创建文件夹StartSearchState.name
            String DirectoryPath = Params.ROOT_DIR +"negative-examples-dot-for-embedding/"+StartSearchStates.get(i).getName()+".Sub"+(SourceSMIndex+1)+".State"+NegExmplesIndex;
            File dir3=new File(Params.ROOT_DIR +"negative-examples-dot-for-embedding/"+StartSearchStates.get(i).getName()+".Sub"+(SourceSMIndex+1)+".State"+NegExmplesIndex);
            RemoveDir(dir3);
            File file = new File(DirectoryPath);
            if(!file.exists()){
                if(file.mkdirs()){
                    System.out.println("创建" + DirectoryPath + "成功");
                }
                else{
                    System.out.println("创建" + DirectoryPath + "失败");
                }
            }
            /**创建文件夹**/
            NegativeExamples = BeamSearchForEmbedding(SourceSemanticModel,StartSearchStates.get(i),IntegrationGraph,Columnnodes,DirectoryPath,jsonObject);
            NegativeExamplesPerFolder.addAll(NegativeExamples);
        }
        System.out.println("NegativeExamples.size:"+NegativeExamples.size());
        System.out.println("NegativeExamplesPerFolder.size:"+NegativeExamplesPerFolder.size());

        /**解开**/

        return null;
    }

    /**5.16 针对某一SemanticModel生成negative examples**/
    public static List<SemanticModel> GenNegativeExamples(int SourceSemanticModelIndex) throws Exception{
        List<ColumnNode> Columnnodes = new ArrayList<ColumnNode>();//原始正确语义模型的Source Attributions集
        DirectedWeightedMultigraph<Node, DefaultLink> IntegrationGraph = null;//集成图
        List<SemanticModel> StartSearchStates = new LinkedList<SemanticModel>();//原始正确语义模型在执行Elimination操作后获得的初始Search States集
        List<SemanticModel> NegativeExamples = new ArrayList<SemanticModel>();//生成negative examples

        //删除指定文件夹内容
        File dir3=new File("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples");
        RemoveDir(dir3);
        File dir4=new File("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples-json");
        RemoveDir(dir4);

        /**获取Source Semantic Model**/
        if(SemanticModels == null) {
            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
        }
        SemanticModel SourceSemanticModel = SemanticModels.get(SourceSemanticModelIndex);//获得要生成negative examples的semnatic model
        /**获取初始Start Search State列表**/
        StartSearchStates = getNewStartStatesSemanticModel1(SourceSemanticModelIndex);
        System.out.println("StartSearchStates.size:"+StartSearchStates.size());
        /**获取source attributions**/
        Columnnodes = SourceSemanticModel.getColumnNodes();
        System.out.println("Columnnodes.size:" + Columnnodes.size());
        /**获取integration graph**/
        Integer[] AllSMIndex = new Integer[]{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28};
        AllSMIndex = (Integer[]) ArrayUtils.remove(AllSMIndex, SourceSemanticModelIndex);

        IntegrationGraph = getIntegrationGraph(SourceSemanticModelIndex, AllSMIndex);
        System.out.println("IntegrationGraph.links.size:" + IntegrationGraph.edgeSet().size());
        System.out.println("IntegrationGraph.nodes.size:" + IntegrationGraph.vertexSet().size());

        //遍历所有的StartSearchStates 调用BeamSearch1 为当前SourceSemanticModel生成300个negative examples
        NegExmplesIndex = 0;
        for(int i=0;i<StartSearchStates.size();i++){
            NegExmplesIndex++;
            NegativeExamples = BeamSearch1(SourceSemanticModel,StartSearchStates.get(i),IntegrationGraph,Columnnodes);
        }
        System.out.println("NegativeExamples.size:"+NegativeExamples.size());
        System.out.println("AllSMIndex:" + Arrays.toString(AllSMIndex));
        return null;
    }

    /**6.23 **/
    public static List<SemanticModel> BeamSearchForEmbedding(SemanticModel SourceSemanticModel, SemanticModel StartSearchState, DirectedWeightedMultigraph<Node, DefaultLink> IntegrationGraph, List<ColumnNode> Columnnodes, String Path,JSONObject jsonObject) throws Exception{
//        List<SemanticModel> StartSearchStates = new LinkedList<SemanticModel>();//原始正确语义模型在执行Elimination操作后获得的初始Search States集
        List<SemanticModel> SearchStates = new ArrayList<SemanticModel>();
        List<SemanticModel> NextStates_Sum = new ArrayList<SemanticModel>();
        List<SemanticModel> NextStates_Total = new ArrayList<SemanticModel>();
        List<SemanticModel> FinalSemanticModels = new ArrayList<SemanticModel>();
        Map<SemanticModel,Double> State_Value = new HashMap<SemanticModel,Double>();
        ModelEvaluation Sim_Value = null;
        SortableSemanticModel sortable_sm = null;
        Map<SemanticModel,Double> Sorted_State_Value = new HashMap<SemanticModel,Double>();
        int AddedAttributionsNum = 0;

        //删除指定文件夹内容  这两个文件夹存储startsearchstate在beamsearch过程总产生的states
        File dir1=new File(Params.ROOT_DIR +"next-state-graph");
        RemoveDir(dir1);
        File dir2=new File(Params.ROOT_DIR +"next-search-states");
        RemoveDir(dir2);
//        File dir3=new File("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples");
//        RemoveDir(dir3);

        System.out.println("BeamSearchForEmbedding中的integrationgraph.vertex.size:" + IntegrationGraph.vertexSet().size());
        System.out.println("BeamSearchForEmbedding中的integrationgraph.edgeset.size:" + IntegrationGraph.edgeSet().size());

        /**当初始搜索状态不为空时**/
        SearchStates.add(StartSearchState);
        System.out.println("SearchStates的大小:" + SearchStates.size());
        /**获取初始Search State要添加的Attributions的个数**/
        for(ColumnNode node: Columnnodes){
            if(!StartSearchState.getColumnNodes().contains(node)){
                AddedAttributionsNum++;
            }
        }
        System.out.println("AddedAttributionsNum:"+AddedAttributionsNum);
        //当SearchStates中的元素为0时 则停止BeamSearch  否则继续BeamSearch  生成下一步更好的结果

        while(AddedAttributionsNum > 0){
            Beam_Search++;
            System.out.println("一次循环");
            System.out.println("循环的SearchStates大小:" + SearchStates.size());
            FinalSemanticModels = new ArrayList<SemanticModel>();
            NextStates_Total = new ArrayList<SemanticModel>();
            System.out.println("循环的NextStates_Total大小:" + NextStates_Total.size());
            //遍历SearchStates中的search state 调用TransitionFunction2 为其生成添加一个节点之后的next search states集合
            for(int i=0;i<SearchStates.size();i++) {
                TransitionFunctionIndex++;
                NextStates_Sum = TransitionFunction2(SearchStates.get(i), IntegrationGraph, Columnnodes);
                if(NextStates_Sum.size()>0) {
                    System.out.println("每执行一次TransitionFunction2后的nextsearchstates个数:" + NextStates_Sum.size());
                    NextStates_Total.addAll(NextStates_Sum);
                }
            }
            List<SemanticModel> SelectSemanticModels = new ArrayList<SemanticModel>();
            Double[][] SimilaryScores = new Double[50][1];
            System.out.println("输出NextStates_Total.size:" + NextStates_Total.size());
            if(NextStates_Total.size()>0){
//                /**打乱NextStates_Total的顺序**/
//                Collections.shuffle(NextStates_Total);
////                State_Value = new HashMap<SemanticModel,Double>();
                int num = 0;
                //遍历添加一个node之后的所有NextStates 计算其与CorrectSemanticModel的值
                for(SemanticModel sm: NextStates_Total){
                    sortable_sm = new SortableSemanticModel(sm,true);
                    Sim_Value = sortable_sm.evaluate(SourceSemanticModel);
                    if(Sim_Value.getPrecision()<1){
                        ++num;
                        if(num>50){
                            break;
                        }
                        SelectSemanticModels.add(sm);
                        SimilaryScores[num-1][0] = Sim_Value.getPrecision();
                    }
                }
                save2dDoubleArray(SimilaryScores,Path+"/similarity_scores.txt");
                System.out.println("每添加一个node后NextStates_Total的大小:"+NextStates_Total.size());
                System.out.println("每添加一个node后SelectSemanticModels的大小:"+SelectSemanticModels.size());
                SearchStates = new ArrayList<SemanticModel>();//清空SearchStates列表
                SearchStates.addAll(SelectSemanticModels);//添加beam_size个最好的下一状态集合
                System.out.println("循环一次后的SearchStates大小:"+SearchStates.size());
                if(SearchStates.size()>0){
                    FinalSemanticModels.addAll(SearchStates);
                }
                System.out.println("循环一次后的FinalSemanticModels大小:"+FinalSemanticModels.size());
            }
            else{
                SearchStates = new ArrayList<SemanticModel>();//清空SearchStates列表
            }

            AddedAttributionsNum--;
        }
        System.out.println("最终的FinalSemanticModels大小:"+FinalSemanticModels.size());

        /**保存Embeddings**/
        BigDecimal[] sm_embedding_array;//保存最终sm embedding
        BigDecimal[][] all_sm_embedding_array = new BigDecimal[FinalSemanticModels.size()][200];
        //遍历所有的sm
        int sm_index = 0;
        /**保存Embeddings**/

        Beam_Search_Index = 0;
        for(SemanticModel SM: FinalSemanticModels){
            Beam_Search_Index++;
//            GraphUtil.exportJson1(SM.getGraph(), Path+"\\" + NegExmplesIndex + "_" + Beam_Search_Index + ".graph" + ".json",true,true);
            GraphVizUtil.exportSemanticModelToGraphviz(SM, GraphVizLabelType.LocalId,
                    GraphVizLabelType.LocalUri, false, false, Path+"/" + NegExmplesIndex + "_" + Beam_Search_Index + ".graph.json" + ".dot");

            /**保存Embeddings**/
            sm_embedding_array = SemanticModelEmbedding(jsonObject,SM);
            List<BigDecimal> sm_embedding_list = Arrays.asList(sm_embedding_array);
            System.out.println("输出sm_embedding_list:" + sm_embedding_list);
            System.out.println("输出sm_embedding_list.size:" + sm_embedding_list.size());
            all_sm_embedding_array[sm_index] = sm_embedding_array;//存储每个link对应的embedding
            ++sm_index;
            /**保存Embeddings**/
        }
        /**保存Embeddings**/
        System.out.println("输出all_sm_embedding_array.size:" + all_sm_embedding_array.length);
        //存储all_sm_embedding_array到txt中
        save2dArray(all_sm_embedding_array,Path+"/sm_embeddings.txt");

        /**保存Embeddings**/
//        //保存Embeddings
//        SaveSMListEmbedding(FinalSemanticModels,jsonObject,Path+"\\sm_embeddings.txt");
        /**当初始搜索状态不为空时**/

        return FinalSemanticModels;
    }

    public static List<SemanticModel> BeamSearch1(SemanticModel SourceSemanticModel, SemanticModel StartSearchState, DirectedWeightedMultigraph<Node, DefaultLink> IntegrationGraph, List<ColumnNode> Columnnodes) throws Exception{
//        List<SemanticModel> StartSearchStates = new LinkedList<SemanticModel>();//原始正确语义模型在执行Elimination操作后获得的初始Search States集
        List<SemanticModel> SearchStates = new ArrayList<SemanticModel>();
        List<SemanticModel> NextStates_Sum = new ArrayList<SemanticModel>();
        List<SemanticModel> NextStates_Total = new ArrayList<SemanticModel>();
        List<SemanticModel> FinalSemanticModels = new ArrayList<SemanticModel>();
        Map<SemanticModel,Double> State_Value = new HashMap<SemanticModel,Double>();
        ModelEvaluation Sim_Value = null;
        SortableSemanticModel sortable_sm = null;
        Map<SemanticModel,Double> Sorted_State_Value = new HashMap<SemanticModel,Double>();
        int AddedAttributionsNum = 0;

        //删除指定文件夹内容
        File dir1=new File("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\next-state-graph");
        RemoveDir(dir1);
        File dir2=new File("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\next-search-states");
        RemoveDir(dir2);
//        File dir3=new File("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples");
//        RemoveDir(dir3);


        /**当初始搜索状态不为空时**/
        SearchStates.add(StartSearchState);
        System.out.println("SearchStates的大小:" + SearchStates.size());
        /**获取初始Search State要添加的Attributions的个数**/
        for(ColumnNode node: Columnnodes){
            if(!StartSearchState.getColumnNodes().contains(node)){
                AddedAttributionsNum++;
            }
        }
        System.out.println("AddedAttributionsNum:"+AddedAttributionsNum);
        //当SearchStates中的元素为0时 则停止BeamSearch  否则继续BeamSearch  生成下一步更好的结果
//        int AddedAttributionsNum1 = 1;

        while(AddedAttributionsNum > 0){
            Beam_Search++;
            System.out.println("一次循环");
            System.out.println("循环的SearchStates大小:" + SearchStates.size());
            FinalSemanticModels = new ArrayList<SemanticModel>();
//            SearchStates_Tmp.addAll(SearchStates);
//            System.out.println("SearchStates_Tmp中元素个数:"+SearchStates_Tmp.size());
            NextStates_Total = new ArrayList<SemanticModel>();
            System.out.println("循环的NextStates_Total大小:" + NextStates_Total.size());
            //遍历SearchStates中的search state 调用TransitionFunction2 为其生成添加一个节点之后的next search states集合
            for(int i=0;i<SearchStates.size();i++) {
                TransitionFunctionIndex++;
                NextStates_Sum = TransitionFunction2(SearchStates.get(i), IntegrationGraph, Columnnodes);
                if(NextStates_Sum.size()>0) {
                    System.out.println("每执行一次TransitionFunction2后的nextsearchstates个数:" + NextStates_Sum.size());
                    NextStates_Total.addAll(NextStates_Sum);
                }
            }
            if(NextStates_Total.size()>0){
                State_Value = new HashMap<SemanticModel,Double>();
                //遍历添加一个node之后的所有NextStates 计算其与CorrectSemanticModel的值
                for(SemanticModel sm: NextStates_Total){
                    sortable_sm = new SortableSemanticModel(sm,true);
                    Sim_Value = sortable_sm.evaluate(SourceSemanticModel);
                    State_Value.put(sm,Sim_Value.getPrecision());
                }
                System.out.println("每添加一个node后State_Value的大小:"+State_Value.size());
                Sorted_State_Value = SortMap(State_Value,2);
                System.out.println("每添加一个node后Sorted_State_Value的大小:"+Sorted_State_Value.size());
                SearchStates = new ArrayList<SemanticModel>();//清空SearchStates列表
                SearchStates.addAll(Sorted_State_Value.keySet());//添加beam_size个最好的下一状态集合
                System.out.println("循环一次后的SearchStates大小:"+SearchStates.size());
                if(SearchStates.size()>0){
                    FinalSemanticModels.addAll(SearchStates);
                }
                System.out.println("循环一次后的FinalSemanticModels大小:"+FinalSemanticModels.size());
//                if(AddedAttributionsNum==2){
//                    int index = 0;
//                    for(SemanticModel fsm: FinalSemanticModels){
//                        index++;
//                        GraphVizUtil.exportSemanticModelToGraphviz(fsm, GraphVizLabelType.LocalId,
//                                GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples-tmp\\" + index + ".graph.json" + ".dot");
//
//                    }
//                }
            }
            else{
                SearchStates = new ArrayList<SemanticModel>();//清空SearchStates列表
            }
            /**5.16**/
////            int index = 0;
////            for(SemanticModel fsm: SearchStates){
////                index++;
////                GraphVizUtil.exportSemanticModelToGraphviz(fsm, GraphVizLabelType.LocalId,
////                        GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples-tmp\\" + index + ".graph.json" + ".dot");
////            }
//            FinalSemanticModels = new ArrayList<SemanticModel>();
//            NextStates_Total = new ArrayList<SemanticModel>();
//            System.out.println("第二次循环的NextStates_Total大小:" + NextStates_Total.size());
//            //遍历SearchStates中的search state 调用TransitionFunction2 为其生成添加一个节点之后的next search states集合
//            for(int i=0;i<SearchStates.size();i++) {
//                TransitionFunctionIndex++;
//                NextStates_Sum = TransitionFunction2(SearchStates.get(9), IntegrationGraph, Columnnodes);
//                if(NextStates_Sum.size()>0) {
//                    System.out.println("第二次每执行一次TransitionFunction2后的nextsearchstates个数:" + NextStates_Sum.size());
//                    NextStates_Total.addAll(NextStates_Sum);
//                }
//            }
//            if(NextStates_Total.size()>0){
//                State_Value = new HashMap<SemanticModel,Double>();
//                //遍历添加一个node之后的所有NextStates 计算其与CorrectSemanticModel的值
//                for(SemanticModel sm: NextStates_Total){
//                    sortable_sm = new SortableSemanticModel(sm,true);
//                    Sim_Value = sortable_sm.evaluate(SourceSemanticModel);
//                    State_Value.put(sm,Sim_Value.getPrecision());
//                }
//                System.out.println("第二次每添加一个node后State_Value的大小:"+State_Value.size());
//                Sorted_State_Value = SortMap(State_Value,10);
//                System.out.println("第二次每添加一个node后Sorted_State_Value的大小:"+Sorted_State_Value.size());
//                SearchStates = new ArrayList<SemanticModel>();//清空SearchStates列表
//                SearchStates.addAll(Sorted_State_Value.keySet());//添加beam_size个最好的下一状态集合
//                System.out.println("第二次循环一次后的SearchStates大小:"+SearchStates.size());
//                if(SearchStates.size()>0){
//                    FinalSemanticModels.addAll(SearchStates);
//                }
//                System.out.println("第二次循环一次后的FinalSemanticModels大小:"+FinalSemanticModels.size());
////                if(AddedAttributionsNum==1){
////                    int index = 0;
////                    for(SemanticModel fsm: FinalSemanticModels){
////                        index++;
////                        GraphVizUtil.exportSemanticModelToGraphviz(fsm, GraphVizLabelType.LocalId,
////                                GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples-tmp\\" + index + ".graph.json" + ".dot");
////
////                    }
////                }
//            }
//            else{
//                SearchStates = new ArrayList<SemanticModel>();//清空SearchStates列表
//            }
//            int index = 0;
//            for(SemanticModel fsm: FinalSemanticModels){
//                index++;
//                GraphVizUtil.exportSemanticModelToGraphviz(fsm, GraphVizLabelType.LocalId,
//                        GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples-tmp\\" + index + ".graph.json" + ".dot");
//            }
            /**5.16**/

            AddedAttributionsNum--;
//            AddedAttributionsNum1--;
        }
        System.out.println("最终的FinalSemanticModels大小:"+FinalSemanticModels.size());
        Beam_Search_Index = 0;
        for(SemanticModel SM: FinalSemanticModels){
            Beam_Search_Index++;
            GraphUtil.exportJson1(SM.getGraph(), "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples-json\\" + NegExmplesIndex + "_" + Beam_Search_Index + ".graph" + ".json",true,true);
            GraphVizUtil.exportSemanticModelToGraphviz(SM, GraphVizLabelType.LocalId,
                    GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples\\" + NegExmplesIndex + "_" + Beam_Search_Index + ".graph.json" + ".dot");

        }
        /**当初始搜索状态不为空时**/

        return FinalSemanticModels;
    }

    /**5.13**/
    public static List<SemanticModel> BeamSearch(int SourceSemanticModelIndex, int StartSearchStateIndex) throws Exception{
        List<ColumnNode> Columnnodes = new ArrayList<ColumnNode>();//原始正确语义模型的Source Attributions集
        DirectedWeightedMultigraph<Node, DefaultLink> IntegrationGraph = null;//集成图
        List<SemanticModel> StartSearchStates = new LinkedList<SemanticModel>();//原始正确语义模型在执行Elimination操作后获得的初始Search States集
        SemanticModel StartSearchState = null;//某一初始search state
        List<SemanticModel> SearchStates = new ArrayList<SemanticModel>();
//        List<SemanticModel> SearchStates_Tmp = new ArrayList<SemanticModel>();
        List<SemanticModel> NextStates_Sum = new ArrayList<SemanticModel>();
        List<SemanticModel> NextStates_Total = new ArrayList<SemanticModel>();
        List<SemanticModel> FinalSemanticModels = new ArrayList<SemanticModel>();
//        List<SemanticModel> NextStates_PerState_Sum = new ArrayList<SemanticModel>();
//        List<SemanticModel> NextStates_BeamSize = new ArrayList<SemanticModel>();
        Map<SemanticModel,Double> State_Value = new HashMap<SemanticModel,Double>();
        ModelEvaluation Sim_Value = null;
        SortableSemanticModel sortable_sm = null;
        Map<SemanticModel,Double> Sorted_State_Value = new HashMap<SemanticModel,Double>();
        int AddedAttributionsNum = 0;

        //删除指定文件夹内容
        File dir1=new File("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\next-state-graph");
        RemoveDir(dir1);
        File dir2=new File("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\next-search-states");
        RemoveDir(dir2);
        File dir3=new File("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples");
        RemoveDir(dir3);


        /**获取Source Semantic Model**/
        if(SemanticModels == null) {
            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
        }
        SemanticModel SourceSemanticModel = SemanticModels.get(SourceSemanticModelIndex);

        /**获取source attributions**/
        Columnnodes = SourceSemanticModel.getColumnNodes();

        /**获取integration graph**/
        IntegrationGraph = getIntegrationGraph(0, new Integer[]{1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28});

        /**当初始搜索状态不为空时**/
        /**获取Start Search States**/
        StartSearchStates = getNewStartStatesSemanticModel(SourceSemanticModelIndex);
        StartSearchState = StartSearchStates.get(StartSearchStateIndex);//根据索引，获取某一个start search state
        SearchStates.add(StartSearchState);
        System.out.println("SearchStates的大小:" + SearchStates.size());
        /**获取初始Search State要添加的Attributions的个数**/
        for(ColumnNode node: Columnnodes){
            if(!StartSearchState.getColumnNodes().contains(node)){
                AddedAttributionsNum++;
            }
        }
        System.out.println("AddedAttributionsNum:"+AddedAttributionsNum);
        //当SearchStates中的元素为0时 则停止BeamSearch  否则继续BeamSearch  生成下一步更好的结果
//        int AddedAttributionsNum1 = 1;
        while(AddedAttributionsNum > 0){
            Beam_Search++;
            System.out.println("一次循环");
            System.out.println("循环的SearchStates大小:" + SearchStates.size());
            FinalSemanticModels = new ArrayList<SemanticModel>();
//            SearchStates_Tmp.addAll(SearchStates);
//            System.out.println("SearchStates_Tmp中元素个数:"+SearchStates_Tmp.size());
            NextStates_Total = new ArrayList<SemanticModel>();
            System.out.println("循环的NextStates_Total大小:" + NextStates_Total.size());
            //遍历SearchStates中的search state 调用TransitionFunction2 为其生成添加一个节点之后的next search states集合
            for(int i=0;i<SearchStates.size();i++) {
                TransitionFunctionIndex++;
                NextStates_Sum = TransitionFunction2(SearchStates.get(i), IntegrationGraph, Columnnodes);
                if(NextStates_Sum.size()>0) {
                    System.out.println("每执行一次TransitionFunction2后的nextsearchstates个数:" + NextStates_Sum.size());
                    NextStates_Total.addAll(NextStates_Sum);
                }
            }
            if(NextStates_Total.size()>0){
                State_Value = new HashMap<SemanticModel,Double>();
                //遍历添加一个node之后的所有NextStates 计算其与CorrectSemanticModel的值
                for(SemanticModel sm: NextStates_Total){
                    sortable_sm = new SortableSemanticModel(sm,true);
                    Sim_Value = sortable_sm.evaluate(SourceSemanticModel);
                    State_Value.put(sm,Sim_Value.getPrecision());
                }
                System.out.println("每添加一个node后State_Value的大小:"+State_Value.size());
                Sorted_State_Value = SortMap(State_Value,10);
                System.out.println("每添加一个node后Sorted_State_Value的大小:"+Sorted_State_Value.size());
                SearchStates = new ArrayList<SemanticModel>();//清空SearchStates列表
                SearchStates.addAll(Sorted_State_Value.keySet());//添加beam_size个最好的下一状态集合
                System.out.println("循环一次后的SearchStates大小:"+SearchStates.size());
                if(SearchStates.size()>0){
                    FinalSemanticModels.addAll(SearchStates);
                }
                System.out.println("循环一次后的FinalSemanticModels大小:"+FinalSemanticModels.size());
//                if(AddedAttributionsNum==2){
//                    int index = 0;
//                    for(SemanticModel fsm: FinalSemanticModels){
//                        index++;
//                        GraphVizUtil.exportSemanticModelToGraphviz(fsm, GraphVizLabelType.LocalId,
//                                GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples-tmp\\" + index + ".graph.json" + ".dot");
//
//                    }
//                }
            }
            else{
                SearchStates = new ArrayList<SemanticModel>();//清空SearchStates列表
            }
            /**5.16**/
////            int index = 0;
////            for(SemanticModel fsm: SearchStates){
////                index++;
////                GraphVizUtil.exportSemanticModelToGraphviz(fsm, GraphVizLabelType.LocalId,
////                        GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples-tmp\\" + index + ".graph.json" + ".dot");
////            }
//            FinalSemanticModels = new ArrayList<SemanticModel>();
//            NextStates_Total = new ArrayList<SemanticModel>();
//            System.out.println("第二次循环的NextStates_Total大小:" + NextStates_Total.size());
//            //遍历SearchStates中的search state 调用TransitionFunction2 为其生成添加一个节点之后的next search states集合
//            for(int i=0;i<SearchStates.size();i++) {
//                TransitionFunctionIndex++;
//                NextStates_Sum = TransitionFunction2(SearchStates.get(9), IntegrationGraph, Columnnodes);
//                if(NextStates_Sum.size()>0) {
//                    System.out.println("第二次每执行一次TransitionFunction2后的nextsearchstates个数:" + NextStates_Sum.size());
//                    NextStates_Total.addAll(NextStates_Sum);
//                }
//            }
//            if(NextStates_Total.size()>0){
//                State_Value = new HashMap<SemanticModel,Double>();
//                //遍历添加一个node之后的所有NextStates 计算其与CorrectSemanticModel的值
//                for(SemanticModel sm: NextStates_Total){
//                    sortable_sm = new SortableSemanticModel(sm,true);
//                    Sim_Value = sortable_sm.evaluate(SourceSemanticModel);
//                    State_Value.put(sm,Sim_Value.getPrecision());
//                }
//                System.out.println("第二次每添加一个node后State_Value的大小:"+State_Value.size());
//                Sorted_State_Value = SortMap(State_Value,10);
//                System.out.println("第二次每添加一个node后Sorted_State_Value的大小:"+Sorted_State_Value.size());
//                SearchStates = new ArrayList<SemanticModel>();//清空SearchStates列表
//                SearchStates.addAll(Sorted_State_Value.keySet());//添加beam_size个最好的下一状态集合
//                System.out.println("第二次循环一次后的SearchStates大小:"+SearchStates.size());
//                if(SearchStates.size()>0){
//                    FinalSemanticModels.addAll(SearchStates);
//                }
//                System.out.println("第二次循环一次后的FinalSemanticModels大小:"+FinalSemanticModels.size());
////                if(AddedAttributionsNum==1){
////                    int index = 0;
////                    for(SemanticModel fsm: FinalSemanticModels){
////                        index++;
////                        GraphVizUtil.exportSemanticModelToGraphviz(fsm, GraphVizLabelType.LocalId,
////                                GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples-tmp\\" + index + ".graph.json" + ".dot");
////
////                    }
////                }
//            }
//            else{
//                SearchStates = new ArrayList<SemanticModel>();//清空SearchStates列表
//            }
//            int index = 0;
//            for(SemanticModel fsm: FinalSemanticModels){
//                index++;
//                GraphVizUtil.exportSemanticModelToGraphviz(fsm, GraphVizLabelType.LocalId,
//                        GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples-tmp\\" + index + ".graph.json" + ".dot");
//            }
            /**5.16**/

            AddedAttributionsNum--;
//            AddedAttributionsNum1--;
        }
        System.out.println("最终的FinalSemanticModels大小:"+FinalSemanticModels.size());
        for(SemanticModel SM: FinalSemanticModels){
            Beam_Search_Index++;
            GraphVizUtil.exportSemanticModelToGraphviz(SM, GraphVizLabelType.LocalId,
                    GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\negative-examples\\" + Beam_Search_Index + ".graph.json" + ".dot");

        }
        /**当初始搜索状态不为空时**/

        return null;
    }

    public static  List<SemanticModel> TransitionFunction2(SemanticModel SearchState, DirectedWeightedMultigraph<Node, DefaultLink> Gint, List<ColumnNode> Attributions) throws Exception {

        System.out.println("进入TransitionFunction2");
        //        List<ColumnNode> Columnnodes = new ArrayList<ColumnNode>();
        List<ColumnNode> SearchStateColumnnodes = new ArrayList<ColumnNode>();
        List<ColumnNode> SearchStateColumnnodesEmptySM = new ArrayList<ColumnNode>();
//        List<SemanticModel> StartSearchStates = new LinkedList<SemanticModel>();
//        SemanticModel StartSearchState = null;
//        DirectedWeightedMultigraph<Node, DefaultLink> IntegrationGraph = null;
        List<SemanticModel> Trees = new ArrayList<SemanticModel>();
        List<SemanticModel> NextStates = new ArrayList<SemanticModel>();

//        /**获取Source Semantic Model**/
//        if(SemanticModels == null) {
//            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
//        }
//        SemanticModel SourceSemanticModel = SemanticModels.get(SourceSemanticModelIndex);

//        /**获取source attributions**/
//        Columnnodes = SourceSemanticModel.getColumnNodes();

//        /**获取integration graph**/
//        IntegrationGraph = getIntegrationGraph(0, new Integer[]{1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28});


//        /**当初始搜索状态不为空时**/
//        /**获取Start Search States**/
//        StartSearchStates = getNewStartStatesSemanticModel(SourceSemanticModelIndex);
//        StartSearchState = StartSearchStates.get(StartSearchStateIndex);//根据索引，获取某一个start search state

        /**获取search state的attributions**/
        SearchStateColumnnodes = SearchState.getColumnNodes();


//        List<SemanticModel> NextSearchStates = new ArrayList<SemanticModel>();
        Set<ColumnNode> NeededAddColumnNodes= new HashSet<ColumnNode>();//保存StartSearchState中的A'

        for(ColumnNode node: Attributions){
            if(!SearchStateColumnnodes.contains(node)){
                NeededAddColumnNodes.add(node);
            }
        }
//        System.out.println("输出TransitionFunction2中的NeededAddColumnNodes.size:" + NeededAddColumnNodes.size());
        //如果有待添加的attibution 则继续调用MergeIntoTree1来添加nodes 如果没有待添加的attribution 则直接返回空列表
        if(NeededAddColumnNodes.size()>0) {
            for (ColumnNode node_ai : NeededAddColumnNodes) {
//                System.out.println("输出node_ai:" + node_ai.getColumnName());
                //tree <- MergeIntoTree(St,Gint,ai)
                System.out.println("进入MergeIntoTree1");
                Trees = MergeIntoTree1(SearchState, Gint, node_ai);//往现有语义模型中添加一个缺失node
                System.out.println("Trees的大小：" + Trees.size());
                //for st+1 <- trees do
                for (SemanticModel st : Trees) {
                    NextStates.add(st);
                }
            }
            /**当初始搜索状态不为空时**/

            /**当初始搜索状态为空时**/
//        /**创建一个empty semantic model**/
//        DirectedWeightedMultigraph<Node,LabeledLink> EmptyGraph = new DirectedWeightedMultigraph<Node,LabeledLink>(LabeledLink.class);
//        SemanticModel EmptySemanticModel = new SemanticModel("EmptySemanticModel",EmptyGraph);
//
//        /**获取empty semantic model的attributions**/
//        SearchStateColumnnodesEmptySM = EmptySemanticModel.getColumnNodes();
//
//        Set<ColumnNode> NeededAddColumnNodesEmptySM = new HashSet<ColumnNode>();//保存EmptySM中的A'
//
//        for(ColumnNode node: Columnnodes){
//            if(!SearchStateColumnnodesEmptySM.contains(node)){
//                NeededAddColumnNodesEmptySM.add(node);
//            }
//        }
//        for(ColumnNode node_ai: NeededAddColumnNodesEmptySM){
//            //tree <- MergeIntoTree(St,Gint,ai)
//            Trees = MergeIntoEmptyTree(EmptySemanticModel,IntegrationGraph,node_ai);
//            System.out.println("Trees的大小："+Trees.size());
//            //for st+1 <- trees do
//            for (SemanticModel st : Trees) {
//                NextStates.add(st);
//            }
//        }
            /**当初始搜索状态为空时**/
            int index = 0;
            for(SemanticModel sm: NextStates) {
                index++;
                GraphVizUtil.exportSemanticModelToGraphviz(sm, GraphVizLabelType.LocalId,
                        GraphVizLabelType.LocalUri, true, true, Params.ROOT_DIR +"next-search-states/" + Beam_Search + "_" + TransitionFunctionIndex + "_" + index + ".graph.json" + ".dot");
            }
            System.out.println("完成MergeIntoTree1");
        }
        System.out.println("完全完成MergeIntoTree1");
        return NextStates;
    }

    public static List<SemanticModel> TransitionFunction(int SemanticModelIndex) throws Exception{

//        SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.TRAIN_MODEL_DIR + "new-train-graph-json", ".json.json");

        File file = new File("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\train-graph\\new-train-graph-json\\s01-cb.csv.Train_1.train_1.graph.json.json");
        InputStream iStream = new FileInputStream(file);
        InputStreamReader in = new InputStreamReader(iStream);
        JsonReader reader = new JsonReader(in);

        if(StartStateGraph==null){
//            graph=GraphUtil.readGraph();
            StartStateGraph = GraphUtil.readGraph(reader);
        }

        System.out.println("StartStateGraph.getClass:"+StartStateGraph.edgeSet());

        /**存储StartStateGraph中的defaultlinks为labeledlinks**/
        for(DefaultLink link: StartStateGraph.edgeSet()){
            labeledLinks.add((LabeledLink) link);
        }
        System.out.println("labeledLinks.size:"+labeledLinks.size());

        /**存储StartStateGraph中的defaultlinks**/
        for(DefaultLink link: StartStateGraph.edgeSet()){
            labeledLinks1.add(link);
        }
        System.out.println("labeledLinks1.size:"+labeledLinks1.size());


//        System.out.println("语义模型的数目："+SemanticModels.size());
//        SemanticModel StartStateSemanticModel = SemanticModels.get(SemanticModelIndex);
//        System.out.println(StartStateSemanticModel);

        /**打印StartStateGraph相关信息**/
        System.out.println("StartStateGraph:"+StartStateGraph);
        System.out.println("图中的节点数:"+StartStateGraph.vertexSet().size());
        System.out.println("图中的边数:"+StartStateGraph.edgeSet().size());
        System.out.println("StartStateGraph.getEdgeFactory:"+StartStateGraph.getEdgeFactory());

        /**为生成一个DirectedWeightedMultigraph<Node, LabeledLink>图创建其EdgeFactory**/
        for(DefaultLink link: StartStateGraph.edgeSet()) {
//            System.out.println("getEdgeSource:"+StartStateGraph.getEdgeSource(link));
//            System.out.println("getEdgeTarget:"+StartStateGraph.getEdgeTarget(link));
            edgeFactory.createEdge(StartStateGraph.getEdgeSource(link),StartStateGraph.getEdgeTarget(link));
            System.out.println("edgeFactory:"+edgeFactory);
        }

        /**由生成的EdgeFactory创建一个DirectedWeightedMultigraph<Node, LabeledLink>空图**/
        NewStartStateGraph = new DirectedWeightedMultigraph<Node, LabeledLink>(edgeFactory);
        System.out.println("NewStartStateGraph.vertexSet().size():"+NewStartStateGraph.vertexSet().size());
        System.out.println("NewStartStateGraph.edgeSet().size():"+NewStartStateGraph.edgeSet().size());

        /**为空图添加节点**/
        for(Node node: StartStateGraph.vertexSet()) {
            NewStartStateGraph.addVertex(node);
        }

        /**为空图添加边做准备：存一个字典,Key是LabeledLink,Value是一个HashMap(Key是SourceNode,Value是TargetNode)**/
        HashMap<LabeledLink,HashMap<Node,Node>> LabeledLink_Source_Target_Nodes= new HashMap<LabeledLink,HashMap<Node,Node>>();
        HashMap<Node,Node> Source_Target_Nodes = new HashMap<Node,Node>();
        for(DefaultLink link: StartStateGraph.edgeSet()){
            //将link的源节点和目标节点存储到HashMap<Node,Node>中
            Source_Target_Nodes = new HashMap<Node,Node>();
//            System.out.println("将link的源节点和目标节点存储到HashMap<Node,Node>中:");
            Source_Target_Nodes.put(link.getSource(), link.getTarget());
//            System.out.println("检查每次遍历过程中HashMap<Node,Node>的内容："+Source_Target_Nodes);
//            System.out.println("将link和HashMap<Node,Node>存储到HashMap<LabeledLink,HashMap<Node,Node>>中:");
            LabeledLink_Source_Target_Nodes.put((LabeledLink) link,Source_Target_Nodes);
//            System.out.println("检查每次遍历过程中HashMap<LabeledLink,HashMap<Node,Node>>的内容："+LabeledLink_Source_Target_Nodes);
        }

//        System.out.println("检查最后生成的HashMap<LabeledLink,HashMap<Node,Node>>的内容："+LabeledLink_Source_Target_Nodes);
//        System.out.println("检查最后生成的HashMap<LabeledLink,HashMap<Node,Node>>的大小："+LabeledLink_Source_Target_Nodes.size());

        /**为空图添加边**/
        for (LabeledLink link : LabeledLink_Source_Target_Nodes.keySet()) {
//            System.out.println("LabeledLink: " + link + " HashMap<Node,Node>: " + LabeledLink_Source_Target_Nodes.get(link));
            for(Node sourcenode: LabeledLink_Source_Target_Nodes.get(link).keySet()){
//                System.out.println("SourceNode: " + sourcenode + " TargetNode: " + LabeledLink_Source_Target_Nodes.get(link).get(sourcenode));
                NewStartStateGraph.addEdge(sourcenode,LabeledLink_Source_Target_Nodes.get(link).get(sourcenode),link);
            }
        }

        System.out.println("NewStartStateGraph.vertexSet().size():"+NewStartStateGraph.vertexSet().size());
        System.out.println("NewStartStateGraph.vertexSet().size():"+NewStartStateGraph.edgeSet().size());

        /**去除DirectedWeightedMultigraph<Node, DefaultLink> StartStateGraph中所有的边**/
//        for(DefaultLink link: StartStateGraph.edgeSet()) {
//            StartStateGraph.removeEdge(link);
//        }
//        System.out.println("图中的节点数1:"+StartStateGraph.vertexSet().size());
//        System.out.println("图中的边数1:"+StartStateGraph.edgeSet().size());


        /**考虑把DirectedWeightedMultigraph<Node, LabeledLink>转换为SemanticModel**/
//        SemanticModel(1,NewStartStateGraph);
//        StartStateSemanticModel=SemanticModel.readJson("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\train-graph\\new-train-graph-json\\s01-cb.csv.Train_1.train_1.graph.json.json");
        StartStateSemanticModel=SemanticModel.readJson("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\models-json\\s01-cb.csv.model.json");

        System.out.println("StartStateSemanticModel:"+StartStateSemanticModel);
        System.out.println("StartStateSemanticModel.getColumnNodes().size():"+StartStateSemanticModel.getColumnNodes().size());
        System.out.println("StartStateSemanticModel.edges().size():"+StartStateSemanticModel.getGraph().edgeSet().size());

        /**生成保存图为dot的文件名**/
//        DirectedWeightedMultigraph Source1 = Source.getGraph();
        String graphPath = "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\DirectedWeighedGraph-Node-DefaultLink-dot\\";
        String graphName = graphPath + "01" + Params.GRAPH_GRAPHVIZ_FILE_EXT;
//        GraphUtil.exportJson(Source1, graphName + ".json",true,true);

        GraphVizUtil.exportJGraphToGraphviz(StartStateGraph,
                "test20190531_alignment_without_steiner_n",
                false,
                GraphVizLabelType.LocalId,
                GraphVizLabelType.LocalUri,
                false,
                true,
                graphName + ".dot");

        return null;
    }

    public static  List<SemanticModel> TransitionFunction1(int SourceSemanticModelIndex, int StartSearchStateIndex) throws Exception {
        List<ColumnNode> Columnnodes = new ArrayList<ColumnNode>();
        List<ColumnNode> SearchStateColumnnodes = new ArrayList<ColumnNode>();
        List<ColumnNode> SearchStateColumnnodesEmptySM = new ArrayList<ColumnNode>();
        List<SemanticModel> StartSearchStates = new LinkedList<SemanticModel>();
        SemanticModel StartSearchState = null;
        DirectedWeightedMultigraph<Node, DefaultLink> IntegrationGraph = null;
        List<SemanticModel> Trees = new ArrayList<SemanticModel>();
        List<SemanticModel> NextStates = new ArrayList<SemanticModel>();


        /**获取Source Semantic Model**/
        if(SemanticModels == null) {
            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
        }
        SemanticModel SourceSemanticModel = SemanticModels.get(SourceSemanticModelIndex);

        /**获取source attributions**/
        Columnnodes = SourceSemanticModel.getColumnNodes();

        /**获取integration graph**/
        IntegrationGraph = getIntegrationGraph(0, new Integer[]{1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28});


        /**当初始搜索状态不为空时**/
        /**获取Start Search States**/
        StartSearchStates = getNewStartStatesSemanticModel(SourceSemanticModelIndex);
        StartSearchState = StartSearchStates.get(StartSearchStateIndex);//根据索引，获取某一个start search state

        /**获取start search state的attributions**/
        SearchStateColumnnodes = StartSearchState.getColumnNodes();


        List<SemanticModel> NextSearchStates = new ArrayList<SemanticModel>();
        Set<ColumnNode> NeededAddColumnNodes= new HashSet<ColumnNode>();//保存StartSearchState中的A'

        for(ColumnNode node: Columnnodes){
            if(!SearchStateColumnnodes.contains(node)){
                NeededAddColumnNodes.add(node);
            }
        }

        for(ColumnNode node_ai: NeededAddColumnNodes){
            //tree <- MergeIntoTree(St,Gint,ai)
            Trees = MergeIntoTree1(StartSearchState,IntegrationGraph,node_ai);
            System.out.println("Trees的大小："+Trees.size());
            //for st+1 <- trees do
            for (SemanticModel st : Trees) {
                NextStates.add(st);
            }
        }
        /**当初始搜索状态不为空时**/

        /**当初始搜索状态为空时**/
//        /**创建一个empty semantic model**/
//        DirectedWeightedMultigraph<Node,LabeledLink> EmptyGraph = new DirectedWeightedMultigraph<Node,LabeledLink>(LabeledLink.class);
//        SemanticModel EmptySemanticModel = new SemanticModel("EmptySemanticModel",EmptyGraph);
//
//        /**获取empty semantic model的attributions**/
//        SearchStateColumnnodesEmptySM = EmptySemanticModel.getColumnNodes();
//
//        Set<ColumnNode> NeededAddColumnNodesEmptySM = new HashSet<ColumnNode>();//保存EmptySM中的A'
//
//        for(ColumnNode node: Columnnodes){
//            if(!SearchStateColumnnodesEmptySM.contains(node)){
//                NeededAddColumnNodesEmptySM.add(node);
//            }
//        }
//        for(ColumnNode node_ai: NeededAddColumnNodesEmptySM){
//            //tree <- MergeIntoTree(St,Gint,ai)
//            Trees = MergeIntoEmptyTree(EmptySemanticModel,IntegrationGraph,node_ai);
//            System.out.println("Trees的大小："+Trees.size());
//            //for st+1 <- trees do
//            for (SemanticModel st : Trees) {
//                NextStates.add(st);
//            }
//        }
        /**当初始搜索状态为空时**/

        return NextStates;
    }

    /**获取semantic model中的root节点**/
    private static Node getSemanticModelRoot(SemanticModel sm){
        List<Node> SMTargetNodes = new ArrayList<Node>();//存储semantic model中所有的target nodes
        Node Root = null;
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
    /**5.19 获取semantic model中所有的root节点**/
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

    public static List<SemanticModel> MergeIntoEmptyTree(SemanticModel ST,DirectedWeightedMultigraph<Node, DefaultLink> Gint, ColumnNode Attribution) throws IOException {
        System.out.println("进入MergeIntoEmptyTree");
        System.out.println("输出search state的信息：" + "nodes个数：" + ST.getGraph().vertexSet().size() + "||links个数：" + ST.getGraph().edgeSet().size());
        System.out.println("输出Integration Graph的信息：" + "nodes个数：" + Gint.vertexSet().size() + "||links个数：" + Gint.edgeSet().size());
        System.out.println("输出此时Attribution的信息：" + Attribution.getId());
        List<SemanticModel> newTrees = new LinkedList<SemanticModel>();

        /**直接添加Attribution  需要考虑user semantic type吗？**/
        //首先获得Attribution的所有可能的semantictype  需要考虑user semantic type吗？
        List<SemanticType> candidatesemantictypes = getCandidateSteinerSets(Attribution, false, 4);
        System.out.println(Attribution.getColumnName() + "的MergeIntoEmptyTree中的candidatesemantictypes大小：" + candidatesemantictypes.size() + "||candidatesemantictypes:" + candidatesemantictypes);

        //用以辅佐去除重复的mntPt
        Set<String> mntPtcomplete = new HashSet<String>();
        SemanticModel InitialStartSearchStateSM = null;

        /**对于每个待添加的column node,mntPts中存储的应该是integration graph中和此column node的semantic types相同的nodes**/
        Set<DefaultLink> mntPts = new HashSet<DefaultLink>();
        //遍历每个node的semantic type,找到在integration graph中与该semantic type相同的nodes
        for (SemanticType semantictype : candidatesemantictypes) {
            for (DefaultLink link : Gint.edgeSet()) {
                if ((link.getSource().getUri().equals(semantictype.getDomain().getUri())) && (link.getUri().equals(semantictype.getType().getUri()))) {
                    mntPts.add(link);
                }
            }
        }
        System.out.println("MergeIntoEmptyTree中的mntPts.size():" + mntPts.size());

        for(DefaultLink mntPt : mntPts){
            /**已完成找路径的mntPt集合  判断要添加的columnnode在integration graph中的映射的具有相同semantic type的link是否重复
             * 如果重复就进入下一次循环
             * 否则就找其connctedPaths**/
            if(mntPtcomplete.contains(mntPt.getSource().getId() + "||" + mntPt.getUri())){
                continue;
            }
            mntPtcomplete.add(mntPt.getSource().getId() + "||" + mntPt.getUri());

            String mntPtlinkId = LinkIdFactory.getLinkId(mntPt.getId(), mntPt.getSource().getId(), Attribution.getId());
//                System.out.println("mntPtlinkId:" + mntPt.getId());
            LabeledLink mntPtlink = new DataPropertyLink(mntPtlinkId, new Label(mntPt.getUri()));

            InitialStartSearchStateSM = ST.clone();
            System.out.println("初始化时StartSearchState的nodes:" + ST.getGraph().vertexSet().size());
            System.out.println("初始化时StartSearchState的links:" + ST.getGraph().edgeSet().size());

            /**添加target node**/
            InitialStartSearchStateSM.getGraph().addVertex(Attribution);
            /**添加mntPt的source node**/
            InitialStartSearchStateSM.getGraph().addVertex(mntPt.getSource());
            /**添加mntPt的source node到Attribution的link**/
            InitialStartSearchStateSM.getGraph().addEdge(mntPt.getSource(), Attribution, mntPtlink);
            MergeIntoTreenumber++;
            DirectedWeightedMultigraph<Node,DefaultLink> NextSearchStateSM = (DirectedWeightedMultigraph<Node, DefaultLink>) InitialStartSearchStateSM.getGraph().clone();

            GraphVizUtil.exportJGraphToGraphviz(NextSearchStateSM,
                null,
                false,
                GraphVizLabelType.LocalId,
                GraphVizLabelType.LocalUri,
                false,
                true,
                    "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\next-state-graph-emptysm\\" + "next_state_emptysm" + MergeIntoTreenumber + ".graph.json" + ".dot");
//            GraphVizUtil.exportSemanticModelToGraphviz(InitialStartSearchStateSM, GraphVizLabelType.LocalId,
//                    GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\next-state-graph-emptysm\\" + "next_state_emptysm" + MergeIntoTreenumber + ".graph.json" + ".dot");

            newTrees.add(InitialStartSearchStateSM);
//                IsSemanticModeHasOnlyRoot(InitialStartSearchStateSM);//判断是否为tree
            System.out.println("InitialStartSearchState的nodes:" + InitialStartSearchStateSM.getGraph().vertexSet().size());
            System.out.println("InitialStartSearchState的links:" + InitialStartSearchStateSM.getGraph().edgeSet().size());
            continue;
        }
        System.out.println("MergeIntoEmptyTree中newTrees.size:"+newTrees.size());

        return newTrees;
    }

    public static List<SemanticModel> MergeIntoTree1(SemanticModel ST,DirectedWeightedMultigraph<Node, DefaultLink> Gint,ColumnNode Attribution) throws Exception {
        System.out.println("进入MergeIntoTree1");
        System.out.println("输出search state的信息：" + "nodes个数：" + ST.getGraph().vertexSet().size() + "||links个数：" + ST.getGraph().edgeSet().size());
        System.out.println("输出Integration Graph的信息：" + "nodes个数：" + Gint.vertexSet().size() + "||links个数：" + Gint.edgeSet().size());
        System.out.println("输出此时Attribution的信息：" + Attribution.getId());

        Set<InternalNode> SearchStateInternalnodes = new HashSet<InternalNode>();
        List<DefaultLink> IntegrationGraphLinks = new ArrayList<DefaultLink>();
        List<DefaultLink> SearchStateLinks = new ArrayList<DefaultLink>();
        Map<Node, Set<Node>> SearchStateInternalnodesMappingIntegrationGraph = new HashMap<Node, Set<Node>>();
        SemanticModel InitialStartSearchStateSM = null;
        SemanticModel MergeInitialStartSearchStateSM = null;
        SemanticModel NextSearchStateSM = null;

        List<SemanticModel> newTrees = new LinkedList<SemanticModel>();

        /**存储StartSearchState中的internal nodes到SearchStateInternalnodes中**/
        SearchStateInternalnodes = ST.getInternalNodes();

        /**存储integration graph中所有的link**/
        IntegrationGraphLinks = new ArrayList<DefaultLink>(Gint.edgeSet());

        /**存储ST(tree)中的所有link**/
        SearchStateLinks = new ArrayList<DefaultLink>(ST.getGraph().edgeSet());

        /**遍历语义模型中的Internal node,找到其在integration graph中对应的nodes**/
        for (InternalNode node : SearchStateInternalnodes) {
            Set<Node> SearchStateInternalnodesMapping = new HashSet<Node>();
            System.out.println("SearchStateInternalnodes的node信息：" + node.getId());
            //获得每个internal node在integration graph中的映射nodes
            for (Node integrationnode : Gint.vertexSet()) {
                if (integrationnode.getId().equals(node.getId())) {
                    SearchStateInternalnodesMapping.add(integrationnode);
                }
            }
//            System.out.println("SearchStateInternalnodesMapping的size:" + SearchStateInternalnodesMapping.size());
            //获得所有internal nodes在integration graph中的映射信息
            SearchStateInternalnodesMappingIntegrationGraph.put(node, SearchStateInternalnodesMapping);
        }

        /**获取StartSearchState的root node  改**/
        Node Root = null;
        Root = getSemanticModelRoot(ST);
        /**5.19**/
        List<Node> RootList = new ArrayList<Node>();
        RootList = getSemanticModelRootList(ST);

        /**取出root在integration graph中的mapping nodes set  改**/
        Set<Node> RootMappingNodes = new HashSet<Node>();
        Set<Node> InternalnodeintreeMappingNodes = new HashSet<Node>();
        /**5.19**/


        List<List<String>> AllconnectedPaths;//存储所有可能的paths(path中的元素是nodeId)
        List<List<Node>> AllconnectedPathsNode_intomount;//存储merge into mount这种情况的所有可能paths(path中的元素是node)
        List<List<Node>> AllconnectedPathsNode_intotree;//存储merge into tree这种情况的所有可能paths(path中的元素是node)
        List<List<Node>> AllconnectedPathsNode_triangle;//存储merge tree and mount这种情况的所有可能paths(path中的元素是node)


        /**找mntPt及其所有可能的paths 并进行添加**/

        //初始化path要添加的nodes集合
        List<Node> eachPathAddedNodes = new ArrayList<Node>();
        //初始化path要添加的links集合
        List<DefaultLink> eachPathAddedLinks = new ArrayList<DefaultLink>();
        List<DefaultLink> eachPathAddedLinks_intomount = new ArrayList<DefaultLink>();
        List<DefaultLink> eachPathAddedLinks_intotree = new ArrayList<DefaultLink>();
        List<DefaultLink> eachPathAddedLinks_treeroot = new ArrayList<DefaultLink>();
        List<DefaultLink> eachPathAddedLinks_mntPtsource = new ArrayList<DefaultLink>();
        //已完成找路径的mntPt semantic type集合,Map<String,Srting>中存放的为link的source node id和link上的信息(uri)
        Set<String> mntPtcomplete = new HashSet<String>();
        //获取每个待添加columnnode的所有可能semantictypes
        /**这个地方是不是还要考虑其正确的user semantic type？(2022.5.8)**/
        List<SemanticType> candidatesemantictypes = getCandidateSteinerSets(Attribution, true, 4);
//        System.out.println(Attribution.getColumnName() + "的candidatesemantictypes大小：" + candidatesemantictypes.size() + "||candidatesemantictypes:" + candidatesemantictypes);
        /**对于每个待添加的column node,mntPts中存储的应该是integration graph中和此column node的semantic types相同的nodes**/
        Set<DefaultLink> mntPts = new HashSet<DefaultLink>();
        //遍历每个node的semantic type,找到在integration graph中与该semantic type相同的nodes
        for (SemanticType semantictype : candidatesemantictypes) {
            for (DefaultLink link : Gint.edgeSet()) {
                if ((link.getSource().getUri().equals(semantictype.getDomain().getUri())) && (link.getUri().equals(semantictype.getType().getUri()))) {
                    mntPts.add(link);//优化  存储link.getSource_Id及link.getUri
                }
            }
        }
//        System.out.println("mntPts.size():" + mntPts.size());

        Set<List<DefaultLink>> AllPaths = new HashSet<List<DefaultLink>>();
        Set<List<DefaultLink>> AllPaths_1 = null;
        Set<List<DefaultLink>> AllPaths_2 = null;
        Set<List<DefaultLink>> AllPaths_3 = null;
//        Set<Node> tree_AncestorNodes = new HashSet<Node>();//存储ST(tree)的root在integration graph中的ancestor nodes
//        tree_AncestorNodes = findAncestorNodesInIntegrationGraph(Gint,Root);//获得tree的ancestornodes列表
        /**找所有可能的paths并进行添加(分两大种情况)  1.直接映射  2.tree和mntPt的merge**/
        //遍历所有可能的mntPt

        Integer WithDefaultlink = 0;
        List<SemanticModel> InitialSMList = new ArrayList<SemanticModel>();
        Map<Integer,List<SemanticModel>> WithOrWithoutDefaultlink = new HashMap<Integer,List<SemanticModel>>();
        WithOrWithoutDefaultlink.put(0,InitialSMList);
        WithOrWithoutDefaultlink.put(1,InitialSMList);
        System.out.println("输出WithOrWithoutDefaultlink:" + WithOrWithoutDefaultlink);
        Boolean iswithDefaultlink = false;
        List<SemanticModel> tempSemanticModelList = new ArrayList<SemanticModel>();

        for (DefaultLink mntPt : mntPts) {
            //存储当前mntPt的所有可能paths(path中的元素为要添加的links) 最后要依据此列表来添加nodes和links
            AllPaths_1 = new HashSet<List<DefaultLink>>();//intomount
            AllPaths_2 = new HashSet<List<DefaultLink>>();//intotree
            AllPaths_3 = new HashSet<List<DefaultLink>>();//triangle

            /**已完成找路径的mntPt集合  判断要添加的columnnode在integration graph中的映射的具有相同semantic type的link是否重复
             * 如果重复就进入下一次循环
             * 否则就找其connctedPaths**/
            if (mntPtcomplete.contains(mntPt.getSource().getId() + "||" + mntPt.getUri())) {
                continue;
            }
            mntPtcomplete.add(mntPt.getSource().getId() + "||" + mntPt.getUri());

            boolean ExistInIntegrationGraph = false;//判断此mntPt的source node是否在semantic model tree中
            boolean IsRoot = false;//判断此mntPt的source node是否为semantic model tree中的root
//            System.out.println("mntPt:" + mntPt.getSource().getId());

            /**2022.5.8 21：47**/
            /**一.直接映射**/
            //判断此mntPt的source node是否在StartSearchState(ST)中
            //如果此mntPt的source node在StartSearchState(ST)中,则只需要直接映射到StartSearchState(ST)中,添加此mntPt的target node
            //检查StartSearchState(ST)的所有Internal nodes或nodes中是否包含mntPt的source node
            if (ST.getGraph().vertexSet().contains(mntPt.getSource())) {
                String mntPtlinkId = LinkIdFactory.getLinkId(mntPt.getId(), mntPt.getSource().getId(), Attribution.getId());
//                System.out.println("mntPtlinkId:" + mntPt.getId());
                LabeledLink mntPtlink = new DataPropertyLink(mntPtlinkId, new Label(mntPt.getUri()));

                InitialStartSearchStateSM = ST.clone();
//                System.out.println("Direct方式添加attr时,初始StartSearchState的nodes.size:" + ST.getGraph().vertexSet().size());
//                System.out.println("Direct方式添加attr时,初始StartSearchState的links.size:" + ST.getGraph().edgeSet().size());
                /**添加target node**/
                InitialStartSearchStateSM.getGraph().addVertex(Attribution);
                /**添加link**/
                InitialStartSearchStateSM.getGraph().addEdge(mntPt.getSource(), Attribution, mntPtlink);
                MergeIntoTreenumber++;

                GraphVizUtil.exportSemanticModelToGraphviz(InitialStartSearchStateSM, GraphVizLabelType.LocalId,
                        GraphVizLabelType.LocalUri, true, true, Params.ROOT_DIR + "next-state-graph/" + "next_state_Direct" + MergeIntoTreenumber + ".graph.json" + ".dot");

                tempSemanticModelList = new ArrayList<SemanticModel>(WithOrWithoutDefaultlink.get(WithDefaultlink));
                tempSemanticModelList.add(InitialStartSearchStateSM);
                WithOrWithoutDefaultlink.put(WithDefaultlink,tempSemanticModelList);

//                newTrees.add(InitialStartSearchStateSM);

//                System.out.println("Direct方式添加attr后,NextSearchState的nodes.size:" + InitialStartSearchStateSM.getGraph().vertexSet().size());
//                System.out.println("Direct方式添加attr后,NextSearchState的links.size:" + InitialStartSearchStateSM.getGraph().edgeSet().size());
                continue;
            }
            /**一.直接映射**/

            /**二.merge tree和mount**/
            //如果此mntPt的source node不在StartSearchState(ST)中,则需要找三种类型的所有paths,并按照paths添加到StartSearchState(ST)中
            else {
                AllconnectedPathsNode_intomount = new ArrayList<List<Node>>();//intomount
                AllconnectedPathsNode_intotree = new ArrayList<List<Node>>();//intotree
                AllconnectedPathsNode_triangle = new ArrayList<List<Node>>();//triangle

                //初始化要添加的mntPt link
                String mntPtlinkId = LinkIdFactory.getLinkId(mntPt.getId(), mntPt.getSource().getId(), Attribution.getId());
//                System.out.println("mntPtlinkId:" + mntPt.getId());
                LabeledLink mntPtlink = new DataPropertyLink(mntPtlinkId, new Label(mntPt.getUri()));
                //添加mntPt的node(source node和target node)及其link
                MergeInitialStartSearchStateSM = ST.clone();
//                System.out.println("Merge方式添加atrr时,初始StartSearchState的nodes.size:" + ST.getGraph().vertexSet().size());
//                System.out.println("Merge方式添加atrr时,初始StartSearchState的links.size:" + ST.getGraph().edgeSet().size());

                /**添加mntPt**/
                MergeInitialStartSearchStateSM.getGraph().addVertex(Attribution);//添加mntPt的target node
                MergeInitialStartSearchStateSM.getGraph().addVertex(mntPt.getSource());//添加mntPt的source node
                MergeInitialStartSearchStateSM.getGraph().addEdge(mntPt.getSource(), Attribution, mntPtlink);//添加表示mntPt的link
                /**添加mntPt**/

//                System.out.println("Merge方式添加atrr时,添加mntPt-link后MergeInitialStartSearchStateSM的nodes.size:" + MergeInitialStartSearchStateSM.getGraph().vertexSet().size());
//                System.out.println("Merge方式添加atrr时,添加mntPt-link后MergeInitialStartSearchStateSM的links.size:" + MergeInitialStartSearchStateSM.getGraph().edgeSet().size());


                /**1.tree添加到mntPt的paths  intomount**/
                //以mntPt的source node为source,以tree的root为target 找到所有可能的paths(此时path中的元素为node)  path长度最大为3:表示mntPt和tree-root之间最多间隔一个node
                //取出root在integration graph中的mapping nodes set  改Root->RootList

                for(Node root: RootList){
                    System.out.println("输出root:" + root.getUri());
                    //遍历每个root 查找其在integration graph中的映射nodes
                    RootMappingNodes = SearchStateInternalnodesMappingIntegrationGraph.get(root);
//                    System.out.println("RootMappingNodesPerRoot:" + RootMappingNodes.size());
                    //遍历每个root映射到integration中的nodes
                    for (Node rootmappingnode : RootMappingNodes) {
                        connectedPathsNode = new ArrayList<List<Node>>();
                        findAllPathNode(IntegrationGraphLinks, mntPt.getSource().getId(), rootmappingnode.getId(), 3);

                        AllconnectedPathsNode_intomount.addAll(connectedPathsNode);//改成这个
                    }
                }


//                System.out.println("AllconnectedPathsNode_intomount.size1:" + mntPt.getId() + "||" + AllconnectedPathsNode_intomount.size());

                //以set的形式暂存当前node pair的links
                Set<DefaultLink> temp_nodepair_links_intomount = null;
                List<DefaultLink> eachPathAddedLinksWithoutDefaultlink = new ArrayList<DefaultLink>();

                for (List<Node> path : AllconnectedPathsNode_intomount) {//遍历每条路径  为其生成需要添加到图中的links列表
                    iswithDefaultlink = false;//用以判断此path中是否有defaultlink  初始状态为没有
                    eachPathAddedLinks = new ArrayList<DefaultLink>();
                    eachPathAddedLinksWithoutDefaultlink = new ArrayList<DefaultLink>();
                    //存储每个path要添加的links信息
                    for (int i = 0; i < path.size() - 1; i++) {
                        temp_nodepair_links_intomount = new HashSet<DefaultLink>();
                        /**检查当前pathnode的nodes(除tree-root外)是否存在于StartSearchState的InternalNodes中  避免出现环**/
                        if (ST.getGraph().vertexSet().contains(path.get(i))) {
                            eachPathAddedLinks = new ArrayList<DefaultLink>();
                            break;
                        }
                        //此处已经检查完此path不会出现环,则将path转换成元素是link的列表
                        else {
                            for (DefaultLink integrationlink : Gint.edgeSet()) {
                                if((integrationlink.getSource().getId().equals(path.get(i).getId())) && (integrationlink.getTarget().getId().equals(path.get(i + 1).getId()))){
                                    temp_nodepair_links_intomount.add(integrationlink);//存储了当前node pair所有links
                                }
                            }
                            //计算temp_nodepair_links中defaultlink的数量
                            int defaultlinknum = 0;
                            for(DefaultLink link: temp_nodepair_links_intomount){
                                if(link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink")){
                                    defaultlinknum++;
                                }
                            }
                            if(defaultlinknum == temp_nodepair_links_intomount.size()){
                                iswithDefaultlink = true;
//                                System.out.println("AllPath1_添加了defaultlink");
                                /**保留包含defaultlink的path**/
                                eachPathAddedLinks.add(new ArrayList<DefaultLink>(temp_nodepair_links_intomount).get(0));
                                /**保留包含defaultlink的path**/
                                /**去除包含defaultlink的path**/
                                eachPathAddedLinksWithoutDefaultlink = new ArrayList<DefaultLink>();
//                                break;
                                /**去除包含defaultlink的path**/
                            }
                            else{
//                                System.out.println("AllPath1_添加了nondefaultlink");
                                for(DefaultLink link: temp_nodepair_links_intomount){
                                    if(!(link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink"))){
//                                        System.out.println(link.getId());
                                        eachPathAddedLinks.add(link);
                                        if(!iswithDefaultlink){
                                            eachPathAddedLinksWithoutDefaultlink.add(link);
                                        }
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    if (eachPathAddedLinksWithoutDefaultlink.size() == (path.size()-1)) {
                        AllPaths_1.add(eachPathAddedLinksWithoutDefaultlink);
                    }
                    else {
                        if (eachPathAddedLinks.size() == (path.size() - 1)) {
                            AllPaths_1.add(eachPathAddedLinks);
                        }
                    }
                }
                AllPaths.addAll(AllPaths_1);
//                System.out.println("AllPaths_1.size:" + mntPt.getId() + "||" + AllPaths_1.size());
//                System.out.println("AllPaths.size:" + mntPt.getId() + "||" + AllPaths.size());


                /**2.mntPt添加到tree的paths  intotree  注意此时mntPt的class node(source node)不在tree中**/
                //以tree中的任一class node为source,以mntPt的source node为target  找到所有可能的paths(此时path中的元素为node)
                //判断mntPt的class node是否在tree中  如果在tree中 则跳过 不为其查找添加到tree中的paths 然后检查下一个mntPt  否则,为其查找添加到tree中的paths
//                System.out.println("判断mntPt的class node是否在tree中");
                if (ST.getGraph().vertexSet().contains(mntPt.getSource())) {
//                    System.out.println("mntPt的class node在ST tree中");
                    continue;
                } else {
//                    System.out.println("mntPt的class node不在ST tree中");
                    //遍历tree(ST)中每个Internal node(共11个internal node)
                    for (Node internalnodeIntree : ST.getInternalNodes()) {
                        //取出每个internalnodeIntree在Integration Graph中对应的nodes列表
                        InternalnodeintreeMappingNodes = SearchStateInternalnodesMappingIntegrationGraph.get(internalnodeIntree);
                        //遍历InternalnodeintreeMappingNodes集合,以每个node为source,以mntPt的source node为target,找到所有可能的paths(此时path中的元素为node)
//                        System.out.println("InternalnodeintreeMappingNodes.size:" + InternalnodeintreeMappingNodes.size());
                        for (Node internalnodeintreemappingnode : InternalnodeintreeMappingNodes) {
//                            System.out.println("找paths");
                            connectedPathsNode = new ArrayList<List<Node>>();
                            findAllPathNode(IntegrationGraphLinks, internalnodeintreemappingnode.getId(), mntPt.getSource().getId(), 3);
                            for (List<Node> pathnode : connectedPathsNode) {
                                AllconnectedPathsNode_intotree.add(pathnode);
                            }
//                            System.out.println("以每个internalnodeintreemappingnode为source的connectedPathsNode.size:" + connectedPathsNode.size());
                        }
                    }
                }
//                System.out.println("AllconnectedPathsNode_intotree.size2:" + mntPt.getId() + "||" + AllconnectedPathsNode_intotree.size());

                //以set的形式暂存当前node pair的links
                Set<DefaultLink> temp_nodepair_links_intotree = null;
                for (List<Node> path : AllconnectedPathsNode_intotree) {
                    iswithDefaultlink = false;//用以判断此path中是否有defaultlink  初始状态为没有
                    eachPathAddedLinks = new ArrayList<DefaultLink>();
                    eachPathAddedLinksWithoutDefaultlink = new ArrayList<DefaultLink>();
                    //存储每个path要添加的links信息
                    for (int i = 0; i < path.size() - 1; i++) {
                        temp_nodepair_links_intotree = new HashSet<DefaultLink>();
                        /**依次遍历path中的node pair(1-2,2-3,3-4...)
                         * 检查当前node pair是否在tree中有路径 如果有则不添加node pair之间对应到integration graph上的link信息
                         * 如果没有则添加对应到integration graph上的link信息**/
                        connectedPathsNode = new ArrayList<List<Node>>();
                        findAllPathNode(SearchStateLinks, path.get(i).getId(), path.get(i + 1).getId(), 50);//长度变更
                        if (connectedPathsNode.size() > 0) {
                            continue;
                        }
                        /**如果path.size()>2 检查当前pathnode的nodes(除第一个node外)是否存在于StartSearchState的InternalNodes中  避免出现环**/
                        if ((i!=path.size()-2)&&(ST.getGraph().vertexSet().contains(path.get(i + 1)))) {
                            eachPathAddedLinks = new ArrayList<DefaultLink>();
                            break;
                        }
                        else {
                            for (DefaultLink integrationlink : Gint.edgeSet()) {
                                if ((integrationlink.getSource().getId().equals(path.get(i).getId())) && (integrationlink.getTarget().getId().equals(path.get(i + 1).getId()))) {
                                    temp_nodepair_links_intotree.add(integrationlink);//存储了当前node pair所有links
                                }
                            }
                            //计算temp_nodepair_links中defaultlink的数量
                            int defaultlinknum = 0;
                            for (DefaultLink link : temp_nodepair_links_intotree) {
                                if (link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink")) {
                                    defaultlinknum++;
                                }
                            }
                            if (defaultlinknum == temp_nodepair_links_intotree.size()) {
                                iswithDefaultlink = true;
//                            System.out.println("AllPath2_添加了defaultlink");
                                /**保留包含Defaultlink的path**/
                                eachPathAddedLinks.add(new ArrayList<DefaultLink>(temp_nodepair_links_intotree).get(0));
                                /**保留包含Defaultlink的path**/
                                /**去除包含Defaultlink的path**/
                                eachPathAddedLinksWithoutDefaultlink = new ArrayList<DefaultLink>();
//                                break;
                                /**去除包含Defaultlink的path**/
                            } else {
//                            System.out.println("AllPath2_添加了nondefaultlink");
                                for (DefaultLink link : temp_nodepair_links_intotree) {
                                    if (!(link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink"))) {
//                                        System.out.println(link.getId());
                                        eachPathAddedLinks.add(link);
                                        if(!iswithDefaultlink){
                                            eachPathAddedLinksWithoutDefaultlink.add(link);
                                        }
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    if (eachPathAddedLinksWithoutDefaultlink.size() == (path.size()-1)) {
                        AllPaths_2.add(eachPathAddedLinksWithoutDefaultlink);
                    }
                    else {
                        if (eachPathAddedLinks.size() == (path.size() - 1)) {
                            AllPaths_2.add(eachPathAddedLinks);
                        }
                    }
                }
                AllPaths.addAll(AllPaths_2);
//                System.out.println("AllPaths_2.size:" + mntPt.getId() + "||" + AllPaths_2.size());
//                System.out.println("AllPaths.size:" + mntPt.getId() + "||" + AllPaths.size());

                /**3.mntPt和tree到common nodes的paths**/
                //分别查找mntPt和tree在integration graph中的ancestor nodes
                Set<Node> mntPt_AncestorNodes = new HashSet<Node>();
                mntPt_AncestorNodes = findAncestorNodesInIntegrationGraph(Gint,mntPt.getSource());//获得mntPt的ancestornodes列表
                //遍历每个Root 找到其tree_AncestorNodes
                Set<Node> tree_AncestorNodes = new HashSet<Node>();//存储ST(tree)的root在integration graph中的ancestor nodes
                List<DefaultLink> eachPathAddedLinks_treerootWithoutDefaultlink = new ArrayList<DefaultLink>();
                List<DefaultLink> eachPathAddedLinks_mntPtsourceWithoutDefaultlink = new ArrayList<DefaultLink>();
                for(Node root: RootList){
                    Set<Node> tree_ANsCommonWithmntPt_AN = new HashSet<Node>();
//                System.out.println(mntPt.getId()+"的mntPt和tree到common nodes的paths");
                    tree_AncestorNodes = new HashSet<Node>();
                    tree_AncestorNodes = findAncestorNodesInIntegrationGraph(Gint,root);
//                    System.out.println("mntPt_AncestorNodes的初始大小："+mntPt_AncestorNodes.size());
//                    System.out.println("tree_AncestorNodes的初始大小："+tree_AncestorNodes.size());
                    tree_ANsCommonWithmntPt_AN.addAll(tree_AncestorNodes);
                    tree_ANsCommonWithmntPt_AN.retainAll(mntPt_AncestorNodes);
//                    System.out.println("tree_AncestorNodes和mntPt_AncestorNodes的交集大小" + tree_ANsCommonWithmntPt_AN.size());
                    //遍历tree_ANsCommonWithmntPt_AN  找到其中每一个节点到tree root的commonnode_tree_paths和到mntPt source node的commonnode_mntPt_paths
                    for(Node commonnode: tree_ANsCommonWithmntPt_AN) {
                        if (!ST.getGraph().vertexSet().contains(commonnode)){//避免出现环
                            connectedPathsNode = new ArrayList<List<Node>>();
                            connectedPathsNode_ANs_tree = new HashSet<List<Node>>();
                            connectedPathsNode_ANs_mntPt = new HashSet<List<Node>>();
                            List<List<DefaultLink>> pathTreeMntPtPerCommon = new ArrayList<List<DefaultLink>>();
                            //以common node为source,以tree root为target
                            findAllPathNode(IntegrationGraphLinks, commonnode.getId(), Root.getId(), 3);
                            connectedPathsNode_ANs_tree.addAll(connectedPathsNode);
//                          System.out.println("connectedPathsNode_ANs_tree-connectedPathsNode的大小：" + connectedPathsNode.size());
//                          System.out.println("connectedPathsNode_ANs_tree的大小：" + connectedPathsNode_ANs_tree.size());
//                          System.out.println("connectedPathsNode_ANs_tree的get(0)的大小：" + new ArrayList<>(connectedPathsNode_ANs_tree).get(0).size());
                            //以common node为source,以mntPt source node为target
                            connectedPathsNode = new ArrayList<List<Node>>();
                            findAllPathNode(IntegrationGraphLinks, commonnode.getId(), mntPt.getSource().getId(), 3);
                            connectedPathsNode_ANs_mntPt.addAll(connectedPathsNode);
//                          System.out.println("connectedPathsNode_ANs_mntPt-connectedPathsNode的大小：" + connectedPathsNode.size());
//                          System.out.println("connectedPathsNode_ANs_mntPt的大小：" + connectedPathsNode_ANs_mntPt.size());
//                          System.out.println("connectedPathsNode_ANs_mntPt的get(0)的大小：" + new ArrayList<>(connectedPathsNode_ANs_mntPt).get(0).size());

                            //以set的形式暂存当前node pair的links
                            Set<DefaultLink> temp_nodepair_links = null;

                            for (List<Node> path_ans_tree : connectedPathsNode_ANs_tree) {
                                iswithDefaultlink = false;//用以判断此path中是否有defaultlink  初始状态为没有
                                eachPathAddedLinks_treeroot = new ArrayList<DefaultLink>();
                                eachPathAddedLinks_treerootWithoutDefaultlink = new ArrayList<DefaultLink>();
                                //存储每个path要添加的links信息
                                for (int i = 0; i < path_ans_tree.size() - 1; i++) {
                                    /**依次遍历path中的node pair(1-2,2-3,3-4...)
                                     * 添加对应到integration graph上的link信息**/
                                    //以set的形式暂存当前node pair的links
                                    temp_nodepair_links = new HashSet<DefaultLink>();
                                    /**检查当前pathnode的nodes(除tree-root外)是否存在于StartSearchState的InternalNodes中  避免出现环**/
                                    if ((i!=path_ans_tree.size()-2)&&(ST.getGraph().vertexSet().contains(path_ans_tree.get(i + 1)))) {
                                        eachPathAddedLinks_treeroot = new ArrayList<DefaultLink>();
                                        break;
                                    }
                                    else{
                                        for (DefaultLink integrationlink : Gint.edgeSet()) {
                                            if ((integrationlink.getSource().getId().equals(path_ans_tree.get(i).getId())) && (integrationlink.getTarget().getId().equals(path_ans_tree.get(i + 1).getId()))) {
                                                temp_nodepair_links.add(integrationlink);//存储了当前node pair所有links
                                            }
                                        }
                                        //计算temp_nodepair_links中defaultlink的数量
                                        int defaultlinknum = 0;
                                        for (DefaultLink link : temp_nodepair_links) {
                                            if (link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink")) {
                                                defaultlinknum++;
                                            }
                                        }
                                        if (defaultlinknum == temp_nodepair_links.size()) {
                                            iswithDefaultlink = true;
//                                            System.out.println("添加了defaultlink");
                                            /**保留包含Defaultlink的path**/
                                            eachPathAddedLinks_treeroot.add(new ArrayList<DefaultLink>(temp_nodepair_links).get(0));
                                            /**保留包含Defaultlink的path**/
                                            /**去除包含Defaultlink的path**/
                                            eachPathAddedLinks_treerootWithoutDefaultlink = new ArrayList<DefaultLink>();
//                                            break;
                                            /**去除包含Defaultlink的path**/
                                        } else {
//                                            System.out.println("添加了nondefaultlink");
                                            for (DefaultLink link : temp_nodepair_links) {
                                                if (!(link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink"))) {
//                                              System.out.println(link.getId());
                                                    eachPathAddedLinks_treeroot.add(link);
                                                    if(!iswithDefaultlink){
                                                        eachPathAddedLinks_treerootWithoutDefaultlink.add(link);
                                                    }
                                                    break;
                                                }
                                            }
                                        }
                                    }
                                }
                                if (eachPathAddedLinks_treerootWithoutDefaultlink.size() == (path_ans_tree.size() - 1)) {
                                    eachPathAddedLinks_treeroot = new ArrayList<DefaultLink>(eachPathAddedLinks_treerootWithoutDefaultlink);
                                }
                                if(eachPathAddedLinks_treeroot.size()==0){
                                    continue;
                                }
//                              System.out.println("eachPathAddedLinks_treeroot的get(0)的大小：" + eachPathAddedLinks_treeroot.size());
//                              System.out.println("结束了一次path_ans_tree");

                                for (List<Node> path_ans_mntPt : connectedPathsNode_ANs_mntPt) {
                                    //这里判断如果两个childpath大小之和大于5 则continue 否则继续以下操作
                                    if((path_ans_tree.size()+path_ans_mntPt.size())>5){
                                        continue;
                                    }
                                    iswithDefaultlink = false;//用以判断此path中是否有defaultlink  初始状态为没有
                                    eachPathAddedLinks_mntPtsource = new ArrayList<DefaultLink>();
                                    eachPathAddedLinks_mntPtsourceWithoutDefaultlink = new ArrayList<DefaultLink>();
                                    //存储每个path要添加的links信息
                                    for (int i = 0; i < path_ans_mntPt.size() - 1; i++) {
                                        /**依次遍历path中的node pair(1-2,2-3,3-4...)
                                         * 添加对应到integration graph上的link信息**/
                                        //以set的形式暂存当前node pair的links
                                        temp_nodepair_links = new HashSet<DefaultLink>();
                                        /**检查当前pathnode的nodes(除mntPt source node外)是否存在于StartSearchState的InternalNodes中  避免出现环**/
                                        if ((ST.getGraph().vertexSet().contains(path_ans_mntPt.get(i + 1)))) {
                                            eachPathAddedLinks_mntPtsource = new ArrayList<DefaultLink>();
                                            break;
                                        }
                                        for (DefaultLink integrationlink : Gint.edgeSet()) {
                                            if ((integrationlink.getSource().getId().equals(path_ans_mntPt.get(i).getId())) && (integrationlink.getTarget().getId().equals(path_ans_mntPt.get(i + 1).getId()))) {
                                                temp_nodepair_links.add(integrationlink);//存储了当前node pair所有links
                                            }
                                        }
                                        //计算temp_nodepair_links中defaultlink的数量
                                        int defaultlinknum = 0;
                                        for (DefaultLink link : temp_nodepair_links) {
                                            if (link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink")) {
                                                defaultlinknum++;
                                            }
                                        }
                                        if (defaultlinknum == temp_nodepair_links.size()) {
                                            iswithDefaultlink = true;
//                                          System.out.println("在mntPt时添加了defaultlink");
                                            /**保留包含Defaultlinkdepath**/
                                            eachPathAddedLinks_mntPtsource.add(new ArrayList<DefaultLink>(temp_nodepair_links).get(0));
                                            /**保留包含Defaultlinkdepath**/
                                            /**去除包含Defaultlinkdepath**/
                                            eachPathAddedLinks_mntPtsourceWithoutDefaultlink = new ArrayList<DefaultLink>();
//                                            break;
                                            /**去除包含Defaultlinkdepath**/
                                        } else {
//                                          System.out.println("在mntPt时添加了nondefaultlink");
                                            for (DefaultLink link : temp_nodepair_links) {
                                                if (!(link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink"))) {
//                                                  System.out.println(link.getId());
                                                    eachPathAddedLinks_mntPtsource.add(link);
                                                    if(!iswithDefaultlink){
                                                        eachPathAddedLinks_mntPtsourceWithoutDefaultlink.add(link);
                                                    }
                                                    break;
                                                }
                                            }
                                        }
                                    }
                                    if(eachPathAddedLinks_mntPtsourceWithoutDefaultlink.size() == (path_ans_mntPt.size()-1)){
                                        eachPathAddedLinks_mntPtsource = new ArrayList<DefaultLink>(eachPathAddedLinks_mntPtsourceWithoutDefaultlink);
                                    }
//                                  System.out.println("eachPathAddedLinks_mntPtsource的get(0)的大小：" + eachPathAddedLinks_mntPtsource.size());

                                    List<DefaultLink> path_tree_with_mntPt = new ArrayList<DefaultLink>();
                                    if(eachPathAddedLinks_mntPtsource.size()>0) {
//                                        path_tree_with_mntPt.addAll(eachPathAddedLinks_treeroot);
                                        if (!(eachPathAddedLinks_treeroot.get(0).getUri().toString().equals(eachPathAddedLinks_mntPtsource.get(0).getUri().toString()))) {
                                            path_tree_with_mntPt.addAll(eachPathAddedLinks_treeroot);
                                            path_tree_with_mntPt.addAll(eachPathAddedLinks_mntPtsource);
                                        } else {
                                            continue;
                                        }
                                    }
                                    else{
                                        continue;
                                    }
                                    int commonnodenum = 0;
                                    for(DefaultLink link: path_tree_with_mntPt){
                                        if(link.getSource().getId().equals(commonnode.getId())){
                                            commonnodenum++;
                                        }
                                    }
                                    if(commonnodenum==2) {
                                        pathTreeMntPtPerCommon.add(path_tree_with_mntPt);
                                    }
                                }
                            }
//                          if(pathTreeMntPtPerCommon.size()>0) {
//                              System.out.println("pathTreeMntPtPerCommon的大小：" + pathTreeMntPtPerCommon.get(0).size());
//                          }

//                          if(pathTreeMntPtPerCommon.size()>0) {
//                              System.out.println("pathTreeMntPtPerCommon的大小：" + pathTreeMntPtPerCommon.size());
//                          }
                            if(pathTreeMntPtPerCommon.size()>0) {
                                AllPaths_3.addAll(pathTreeMntPtPerCommon);
                            }
                        }
                    }
                }

//                System.out.println(mntPt.getId() + "的AllPaths_3大小" + AllPaths_3.size());
                /**3.mntPt和tree到common nodes的paths**/

                //遍历tree的ancestor nodes
                //查看mntPt的ancestor nodes中是否包含当前的tree ancestor node
                //如果包含则取该node为common node,查找common node到tree root node的path以及common node到mntPt source node的path
                //依据这一对path添加信息 生成triangle类型的nextsearchstate

            }
            /**二.merge tree和mount**/



            /**添加其中任意一种类型(如AllPaths_1)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/
            for(List<DefaultLink> addpath: AllPaths_1){
                if(addpath.size()>0) {
//                    tempSemanticModelList = new ArrayList<SemanticModel>();
                    WithDefaultlink = 0;
                    NextSearchStateSM = MergeInitialStartSearchStateSM.clone();
//            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().vertexSet().size());
//            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().edgeSet().size());
                    for (int i = 0; i < addpath.size(); i++) {
                        if(addpath.get(i).getUri().equals("http://isi.edu/integration/karma/dev#defaultLink")){
                            WithDefaultlink = 1;
                        }
                        LabeledLink addedlink = new DataPropertyLink(addpath.get(i).getId(), new Label(addpath.get(i).getUri()));
                        NextSearchStateSM.getGraph().addVertex(addpath.get(i).getSource());
                        NextSearchStateSM.getGraph().addVertex(addpath.get(i).getTarget());
                        NextSearchStateSM.getGraph().addEdge(addpath.get(i).getSource(), addpath.get(i).getTarget(), addedlink);
                    }
                    MergeIntoTreenumber++;

                    /**保存Json文件**/

                    /**保存dot文件**/
                    GraphVizUtil.exportSemanticModelToGraphviz(NextSearchStateSM, GraphVizLabelType.LocalId,
                            GraphVizLabelType.LocalUri, true, true, Params.ROOT_DIR +"next-state-graph/" + "next_state_IntoMount" + Beam_Search + "_" + MergeIntoTreenumber + ".graph.json" + ".dot");

                    if(WithDefaultlink==0){
                        System.out.println("AllPaths_1中有不包含Defaultlink的path");
                    }
                    tempSemanticModelList = new ArrayList<SemanticModel>(WithOrWithoutDefaultlink.get(WithDefaultlink));
                    tempSemanticModelList.add(NextSearchStateSM);
                    WithOrWithoutDefaultlink.put(WithDefaultlink,tempSemanticModelList);

//                    newTrees.add(NextSearchStateSM);

//                    System.out.println("NextSearchStateSM的nodes:" + NextSearchStateSM.getGraph().vertexSet().size());
//                    System.out.println("NextSearchStateSM的links:" + NextSearchStateSM.getGraph().edgeSet().size());
                }
            }
            /**添加其中任意一种类型(如AllPaths_1)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/

            /**添加其中任意一种类型(如AllPaths_2)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/
            for(List<DefaultLink> addpath: AllPaths_2){
                if(addpath.size()>0) {
//                    tempSemanticModelList = new ArrayList<SemanticModel>();
                    WithDefaultlink = 0;
                    NextSearchStateSM = MergeInitialStartSearchStateSM.clone();
//            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().vertexSet().size());
//            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().edgeSet().size());
                    for (int i = 0; i < addpath.size(); i++) {
                        if(addpath.get(i).getUri().equals("http://isi.edu/integration/karma/dev#defaultLink")){
                            WithDefaultlink = 1;
                        }
                        LabeledLink addedlink = new DataPropertyLink(addpath.get(i).getId(), new Label(addpath.get(i).getUri()));
                        NextSearchStateSM.getGraph().addVertex(addpath.get(i).getSource());
                        NextSearchStateSM.getGraph().addVertex(addpath.get(i).getTarget());
                        NextSearchStateSM.getGraph().addEdge(addpath.get(i).getSource(), addpath.get(i).getTarget(), addedlink);
                    }
                    MergeIntoTreenumber++;

                    GraphVizUtil.exportSemanticModelToGraphviz(NextSearchStateSM, GraphVizLabelType.LocalId,
                            GraphVizLabelType.LocalUri, true, true, Params.ROOT_DIR +"next-state-graph/" + "next_state_IntoTree" + Beam_Search + "_" + MergeIntoTreenumber + ".graph.json" + ".dot");


                    if(WithDefaultlink==0){
                        System.out.println("AllPaths_2中有不包含Defaultlink的path");
                    }
                    tempSemanticModelList = new ArrayList<SemanticModel>(WithOrWithoutDefaultlink.get(WithDefaultlink));
                    tempSemanticModelList.add(NextSearchStateSM);
                    WithOrWithoutDefaultlink.put(WithDefaultlink,tempSemanticModelList);

//                    newTrees.add(NextSearchStateSM);

//                    System.out.println("NextSearchStateSM的nodes:" + NextSearchStateSM.getGraph().vertexSet().size());
//                    System.out.println("NextSearchStateSM的links:" + NextSearchStateSM.getGraph().edgeSet().size());
                }
            }
            /**添加其中任意一种类型(如AllPaths_2)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/

            /**添加其中任意一种类型(如AllPaths_3)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/
            for(List<DefaultLink> addpath: AllPaths_3){
//                System.out.println("AllPaths_3:" + addpath.size());
                if(addpath.size()>0) {
//                    tempSemanticModelList = new ArrayList<SemanticModel>();
                    WithDefaultlink = 0;
                    NextSearchStateSM = MergeInitialStartSearchStateSM.clone();
//            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().vertexSet().size());
//            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().edgeSet().size());
                    for (int i = 0; i < addpath.size(); i++) {
                        if(addpath.get(i).getUri().equals("http://isi.edu/integration/karma/dev#defaultLink")){
                            WithDefaultlink = 1;
                        }
                        LabeledLink addedlink = new DataPropertyLink(addpath.get(i).getId(), new Label(addpath.get(i).getUri()));
                        NextSearchStateSM.getGraph().addVertex(addpath.get(i).getSource());
                        NextSearchStateSM.getGraph().addVertex(addpath.get(i).getTarget());
                        NextSearchStateSM.getGraph().addEdge(addpath.get(i).getSource(), addpath.get(i).getTarget(), addedlink);
                    }
                    MergeIntoTreenumber++;

                    GraphVizUtil.exportSemanticModelToGraphviz(NextSearchStateSM, GraphVizLabelType.LocalId,
                            GraphVizLabelType.LocalUri, true, true, Params.ROOT_DIR +"next-state-graph/" + "next_state_triangle" + Beam_Search + "_" + MergeIntoTreenumber + ".graph.json" + ".dot");


                    if(WithDefaultlink==0){
                        System.out.println("AllPaths_3中有不包含Defaultlink的path");
                    }
                    tempSemanticModelList = new ArrayList<SemanticModel>(WithOrWithoutDefaultlink.get(WithDefaultlink));
                    tempSemanticModelList.add(NextSearchStateSM);
                    WithOrWithoutDefaultlink.put(WithDefaultlink,tempSemanticModelList);

//                    newTrees.add(NextSearchStateSM);

//                    System.out.println("NextSearchStateSM的nodes:" + NextSearchStateSM.getGraph().vertexSet().size());
//                    System.out.println("NextSearchStateSM的links:" + NextSearchStateSM.getGraph().edgeSet().size());
                }
            }
            /**添加其中任意一种类型(如AllPaths_3)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/

            /**2022.5.8 22：10 注释**/
//            /**判断mntPt类型(三种)**/
//            for (Node i : SearchStateInternalnodesMappingIntegrationGraph.keySet()) {
//                /**判断mntPt的source是不是已经存在于semantic model tree中
//                 * 1.如果存在于semantic model tree中，并且不是映射到semantic model tree的root上，则只需要找semantic model tree的root到mntPt的source node之间的路径
//                 * 2.如果此mntPt的source node映射到semantic model tree中的root上，则需要找common node将semantic model tree与mntPt连接起来
//                 * 3.如果mntPt的source node不存在于semantic model tree中,则找semantic model tree中的任意internal node到mntPt的source node之间的路径**/
//                if (SearchStateInternalnodesMappingIntegrationGraph.get(i).contains(mntPt.getSource())) {
//                    ExistInIntegrationGraph = true;//mntPt的source node存在于semantic model tree中
//                    if (mntPt.getSource().getId().equals(Root.getId())) {
//                        IsRoot = true;
//                    }
//                    break;
//                }
//            }
//            System.out.println("ExistInIntegrationGraph:" + ExistInIntegrationGraph);
//            System.out.println("IsRoot:" + IsRoot);
//
//
//            //1.如果mntPt的source node存在于semantic model tree中，并且为semantic model tree中的root，则需找common node将两者联系起来
//            if (ExistInIntegrationGraph && IsRoot) {
//                //保存每个mntPt的所有的待添加路径信息
//                AllconnectedPaths = new ArrayList<List<String>>();
//                AllconnectedPathsNode = new ArrayList<List<Node>>();
//                System.out.println("找common node----------");
//            }
//            //2.如果mntPt的source node存在于semantic model tree中，且不为root，则需找root到mntPt之间的路径
//            else if (ExistInIntegrationGraph) {
//                //保存每个mntPt的所有的待添加路径信息
//                AllconnectedPaths = new ArrayList<List<String>>();
//                AllconnectedPathsNode = new ArrayList<List<Node>>();
//
//                System.out.println("找root到mntPt之间的路径----------");
//                //取出root在integration graph中的mapping nodes set
//                RootMappingNodes = SearchStateInternalnodesMappingIntegrationGraph.get(Root);
//                System.out.println("RootMappingNodes:" + RootMappingNodes.size());
//
//                //遍历每个root到integration中的nodes
//                for (Node rootmappingnode : RootMappingNodes) {
//                    System.out.println("rootmappingnode:" + rootmappingnode.getId() + "||" + mntPt.getSource().getId());
//                    connectedPathsNode = new ArrayList<List<Node>>();
//                    findAllPathNode(IntegrationGraphLinks, rootmappingnode.getId(), mntPt.getSource().getId(), 3);
//                    System.out.println("connectedPathsNode.size:" + connectedPathsNode.size());
//                    //connectedPaths ← all paths that connect leaves or root of st with mntPt
//                    int index = 0;//用于测试,对于每个要添加的node,现只连接其第一条路径
//
//                    //获得每个mntPt的所有待添加路径信息
//                    for (List<Node> path : connectedPathsNode) {
//                        AllconnectedPathsNode.add(path);
//                    }
//
//                    System.out.println("AllconnectedPathsNode.size:" + AllconnectedPathsNode.size());
//                    for (List<Node> path : AllconnectedPathsNode) {
//                        InitialStartSearchStateSM = ST.clone();
//                        System.out.println("初始化时StartSearchState的nodes:" + ST.getGraph().vertexSet().size());
//                        System.out.println("初始化时StartSearchState的links:" + ST.getGraph().edgeSet().size());
//
//                        eachPathAddedNodes.add(Attribution);//添加需要add的mntPt target(column) node
//                        /**添加target node**/
//                        InitialStartSearchStateSM.getGraph().addVertex(Attribution);
//                        /**添加mntPt**/
//                        String mntPtlinkId = LinkIdFactory.getLinkId(mntPt.getId(), mntPt.getSource().getId(), Attribution.getId());
//                        System.out.println("mntPtlinkId:" + mntPt.getId());
//                        LabeledLink mntPtlink = new DataPropertyLink(mntPtlinkId, new Label(mntPt.getUri()));
//                        InitialStartSearchStateSM.getGraph().addEdge(mntPt.getSource(), Attribution, mntPtlink);
//                        /**完成target(column) node和mntPt的添加**/
//                        System.out.println(mntPt.getSource().getId() + "的connectedPaths:" + path);
//                        //存储每个path要添加的nodes
//                        for (Node nodeInfo : path) {
//                            for (Node integrationnode : Gint.vertexSet()) {
//                                if (integrationnode.getId().equals(nodeInfo.getId())) {
////                                    InitialStartSearchState.addVertex(integrationnode);//添加每个path要add的nodes\
//                                    InitialStartSearchStateSM.getGraph().addVertex(integrationnode);
//                                    eachPathAddedNodes.add(integrationnode);
//                                }
//                            }
//                        }
////                            //输出每条(第一条)path要添加的nodes信息
////                            for(Node pathnode: eachPathAddedNodes) {
////                                //向semantic model tree中添加这些nodes
////                                System.out.println("输出每条(第一条)path要添加的nodes信息" + pathnode.getId());
////                            }////////////////////////////////////////////
//                        //存储每个path要添加的links信息
//                        for (int i = 0; i < path.size() - 1; i++) {
//                            for (DefaultLink integrationlink : Gint.edgeSet()) {
//                                if ((integrationlink.getSource().getId().equals(path.get(i).getId())) && (integrationlink.getTarget().getId().equals(path.get(i + 1).getId()))) {//待添加的links
//                                    boolean isaddedlink = true;
//                                    LabeledLink addedlink = new DataPropertyLink(integrationlink.getId(), new Label(integrationlink.getUri()));
//                                    for (LabeledLink semanticmodeltreelink : ST.getGraph().edgeSet()) {//遍历semantic model tree中的links
//                                        if (integrationlink.getId().equals(semanticmodeltreelink.getId())) {
//                                            isaddedlink = false;
//                                            break;
//                                        }
//                                    }
//                                    if (isaddedlink) {
//                                        InitialStartSearchStateSM.getGraph().addEdge(integrationlink.getSource(), integrationlink.getTarget(), addedlink);
//                                    }
//                                    eachPathAddedLinks.add(integrationlink);//测试
//                                }
//                            }
//                        }
////                            //输出每条(第一条)path要添加的links信息
////                            for(DefaultLink pathlink: eachPathAddedLinks) {
////                                //向semantic model tree中添加这些nodes
////                                System.out.println("输出每条(第一条)path要添加的links信息" + pathlink.getId());
////                            }//////////////////////////////
//
//                        /**保存添加一个target(column) node的nextsearchstate**/
//
//                        MergeIntoTreenumber++;
//
//                        GraphVizUtil.exportSemanticModelToGraphviz(InitialStartSearchStateSM, GraphVizLabelType.LocalId,
//                                GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\next-state-graph\\" + "next_state_" + MergeIntoTreenumber + ".graph.json" + ".dot");
//
//                        newTrees.add(InitialStartSearchStateSM);
//                        System.out.println("InitialStartSearchState的nodes:" + InitialStartSearchStateSM.getGraph().vertexSet().size());
//                        System.out.println("InitialStartSearchState的links:" + InitialStartSearchStateSM.getGraph().edgeSet().size());
//                    }
//                }
//            }
//            //3.如果mntPt的source node不存在于semantic model tree中,则找semantic model tree中的任意internal node到mntPt的source node之间的路径
//            else{
//                //保存每个mntPt的所有的待添加路径信息
//                AllconnectedPaths = new ArrayList<List<String>>();
//                AllconnectedPathsNode = new ArrayList<List<Node>>();
//                System.out.println("找semantic model tree中任一internal node到mntPt的source node之间的路径");
//            }
            /**2022.5.8 22：10 注释**/
        }

        /**找完三种类型的所有paths 按照每个path添加信息  生成所有的nextsearchstate(有误)**/
//        for (List<DefaultLink> addpath : AllPaths) {
//            NextSearchStateSM = MergeInitialStartSearchStateSM.clone();
////            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().vertexSet().size());
////            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().edgeSet().size());
//            for (int i = 0; i < addpath.size(); i++) {
//                LabeledLink addedlink = new DataPropertyLink(addpath.get(i).getId(), new Label(addpath.get(i).getUri()));
//                NextSearchStateSM.getGraph().addVertex(addpath.get(i).getSource());
//                NextSearchStateSM.getGraph().addVertex(addpath.get(i).getTarget());
//                NextSearchStateSM.getGraph().addEdge(addpath.get(i).getSource(), addpath.get(i).getTarget(), addedlink);
//            }
//            MergeIntoTreenumber++;
//
//            GraphVizUtil.exportSemanticModelToGraphviz(NextSearchStateSM, GraphVizLabelType.LocalId,
//                    GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\next-state-graph\\" + "next_state_" + MergeIntoTreenumber + ".graph.json" + ".dot");
//
//            newTrees.add(NextSearchStateSM);
//            System.out.println("NextSearchStateSM的nodes:" + NextSearchStateSM.getGraph().vertexSet().size());
//            System.out.println("NextSearchStateSM的links:" + NextSearchStateSM.getGraph().edgeSet().size());
//
//        }
        /**找完三种类型的所有paths 按照每个path添加信息  生成所有的nextsearchstate(有误)**/

        //往newTrees中添加除直接连接方式的其他三种策略生成的语义模型  首先判断没有defaultlink的model的数量,然后选择添加多少个有defaultlink的models
//            if(WithOrWithoutDefaultlink.get(0).size()>0) {
//            int InitialnewTreesNum = newTrees.size();
        System.out.println("输出InitialnewTreesNum.size:" + newTrees.size());
//        System.out.println("输出AllPaths_1.size:" + AllPaths_1.size());
//        System.out.println("输出AllPaths_2.size:" + AllPaths_2.size());
//        System.out.println("输出AllPaths_3.size:" + AllPaths_3.size());
        if(WithOrWithoutDefaultlink.get(0).size()>0) {
            newTrees.addAll(WithOrWithoutDefaultlink.get(0));
            System.out.println("输出WithOrWithoutDefaultlink.get(0).size:" + WithOrWithoutDefaultlink.get(0).size());
        }
        if(WithOrWithoutDefaultlink.get(1).size()>0) {
            Collections.shuffle(WithOrWithoutDefaultlink.get(1));
            newTrees.addAll(WithOrWithoutDefaultlink.get(1));
            System.out.println("输出WithOrWithoutDefaultlink.get(1).size:" + WithOrWithoutDefaultlink.get(1).size());
        }

        return newTrees;
    }

    public static List<SemanticModel> MergeIntoTree(int SourceSemanticModelIndex, int StartSearchStateIndex) throws Exception {

        System.out.println("进入MergeIntoTree");
        List<ColumnNode> Columnnodes = new ArrayList<ColumnNode>();
        List<ColumnNode> SearchStateColumnnodes = new ArrayList<ColumnNode>();
        Set<InternalNode> SearchStateInternalnodes = new HashSet<InternalNode>();
        List<SemanticModel> StartSearchStates = new LinkedList<SemanticModel>();
        SemanticModel StartSearchState = null;
        SemanticModel InitialStartSearchStateSM = null;
        DirectedWeightedMultigraph<Node,DefaultLink> InitialStartSearchState = null;
        DirectedWeightedMultigraph<Node, DefaultLink> IntegrationGraph = null;
        Map<Node,Set<Node>> SearchStateInternalnodesMappingIntegrationGraph = new HashMap<Node,Set<Node>>();
        List<DefaultLink> IntegrationGraphLinks = new ArrayList<DefaultLink>();
        int number = 0;//文件名序号

        List<SemanticModel> newTrees = new LinkedList<SemanticModel>();
        List<SemanticType> candidatesemantictypes = new LinkedList<SemanticType>();
        //存储每个path要添加的nodes
        Set<Node> eachPathAddedNodes;
        //存储每个path要添加的links
        Set<DefaultLink> eachPathAddedLinks;

        /**获取Source Semantic Model**/
        if(SemanticModels == null) {
            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
        }
        SemanticModel SourceSemanticModel = SemanticModels.get(SourceSemanticModelIndex);

        /**获取Start Search States**/
        StartSearchStates = getNewStartStatesSemanticModel(0);
        StartSearchState = StartSearchStates.get(StartSearchStateIndex);//根据索引，获取某一个start search state

        /**获取source attributions**/
        Columnnodes = SourceSemanticModel.getColumnNodes();

        /**获取start search state的attributions**/
        SearchStateColumnnodes = StartSearchState.getColumnNodes();

        /**获取integration graph**/
        IntegrationGraph = getIntegrationGraph(0, new Integer[]{1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28});

        List<SemanticModel> NextSearchStates = new LinkedList<SemanticModel>();

        //需要添加的columnnodes
        Set<ColumnNode> NeededAddColumnNodes= new HashSet<ColumnNode>();

        /**用于检查Integration graph中node的信息*/
//        for(Node node: IntegrationGraph.vertexSet()){
//            System.out.println("输出integration graph中的node Id:" + node.getId());
//        }

        /**需要添加的column nodes**/
        for(ColumnNode node: Columnnodes){
            if(!SearchStateColumnnodes.contains(node)){
                NeededAddColumnNodes.add(node);
            }
        }

        /**存储StartSearchState中的internal nodes到SearchStateInternalnodes中**/
        for(InternalNode node:StartSearchState.getInternalNodes()){
            SearchStateInternalnodes.add(node);
        }


        /**存储integration graph中所有的link**/
        IntegrationGraphLinks = new ArrayList<DefaultLink>(IntegrationGraph.edgeSet());

        //遍历语义模型中的Internal node,找到其在integration graph中对应的nodes
        for(InternalNode node:SearchStateInternalnodes) {
            Set<Node> SearchStateInternalnodesMapping = new HashSet<Node>();
            System.out.println("SearchStateInternalnodes的node信息：" + node.getId());
            //获得每个internal node在integration graph中的映射nodes
            for(Node integrationnode: IntegrationGraph.vertexSet()){
                if(integrationnode.getId().equals(node.getId())){
                    SearchStateInternalnodesMapping.add(integrationnode);
                }
            }
            System.out.println("SearchStateInternalnodesMapping的size:"+SearchStateInternalnodesMapping.size());
            //获得所有internal nodes在integration graph中的映射信息
            SearchStateInternalnodesMappingIntegrationGraph.put(node,SearchStateInternalnodesMapping);
        }
//        System.out.println("SearchStateInternalnodesMappingIntegrationGraph的size:"+SearchStateInternalnodesMappingIntegrationGraph.size());


//        SemanticType semantictype = new SemanticType();
        List<SemanticType> IntegrationGraphSemanticTypes = new LinkedList<SemanticType>();
        /**遍历integration graph中所有的internode和相关link组成的semantic types信息**/
//        for(DefaultLink link: IntegrationGraph.edgeSet()){
//            System.out.println("link.getType().toString():"+link.getUri());
//        }

        /**获取StartSearchState的root node**/
        Node Root = null;
        Root = getSemanticModelRoot(StartSearchState);


        //取出root在integration graph中的mapping nodes set
        Set<Node> RootMappingNodes = new HashSet<Node>();
        List<List<String>> AllconnectedPaths;
        List<List<Node>> AllconnectedPathsNode;

        for(ColumnNode node: NeededAddColumnNodes){
            //初始化path要添加的nodes集合
            eachPathAddedNodes = new HashSet<Node>();
            //初始化path要添加的links集合
            eachPathAddedLinks = new HashSet<DefaultLink>();
            //已完成找路径的mntPt semantic type集合,Map<String,Srting>中存放的为link的source node id和link上的信息(uri)
            Set<String> mntPtcomplete = new HashSet<String>();
            //获取每个待添加columnnode的所有可能semantictypes
            /**这个地方是不是还要考虑其正确的user semantic type？(2022.5.8)**/
            candidatesemantictypes = getCandidateSteinerSets(node,false,4);
            System.out.println(node.getColumnName()+"的candidatesemantictypes大小："+candidatesemantictypes.size()+"||candidatesemantictypes:"+candidatesemantictypes);
            /**对于每个待添加的column node,mntPts中存储的应该是integration graph中和此column node的semantic types相同的nodes**/
            Set<DefaultLink> mntPts = new HashSet<DefaultLink>();
            //遍历每个node的semantic type,找到在integration graph中与该semantic type相同的nodes
            for(SemanticType semantictype: candidatesemantictypes){
//                System.out.println("semantictype.getType().getUri():"+semantictype.getType().getUri());
                for(DefaultLink link: IntegrationGraph.edgeSet()){
                    if((link.getSource().getUri().equals(semantictype.getDomain().getUri()))&&(link.getUri().equals(semantictype.getType().getUri()))){
                        mntPts.add(link);
                    }
                }
            }
            System.out.println("mntPts.size():"+mntPts.size());
            for(DefaultLink mntPt: mntPts){
                /**已完成找路径的mntPt集合  判断要添加的columnnode在integration graph中的映射的具有相同semantic type的link是否重复
                 * 如果重复就进入下一次循环
                 * 否则就找其connctedPaths**/
                if(mntPtcomplete.contains(mntPt.getSource().getId() + "||" + mntPt.getUri())){
                    continue;
                }
                mntPtcomplete.add(mntPt.getSource().getId() + "||" + mntPt.getUri());

                boolean ExistInIntegrationGraph = false;//判断此mntPt的source node是否在semantic model tree中
                boolean IsRoot = false;//判断此mntPt的source node是否为semantic model tree中的root
                System.out.println("mntPt:"+mntPt.getSource().getId());
                //遍历mntPt的source node,将其作为findAllPath函数的target,
                //二次遍历得到每个integration graph中的mapping node,将其作为findAllPath函数的source,
                //findAllPath函数的LinkList为integration graph中的所有links
                for(Node i:SearchStateInternalnodesMappingIntegrationGraph.keySet()){
                    /**判断mntPt的source是不是已经存在于semantic model tree中
                     * 如果存在于semantic model tree中，并且不是映射到semantic model tree的root上，则只需要找semantic model tree的root到mntPt的source node之间的路径
                     * 如果此mntPt的source node映射到semantic model tree中的root上，则需要找common node将semantic model tree与mntPt连接起来
                     * 如果mntPt的source node不存在于semantic model tree中,则找semantic model tree中的任意internal node到mntPt的source node之间的路径**/
                    if(SearchStateInternalnodesMappingIntegrationGraph.get(i).contains(mntPt.getSource())){
                        ExistInIntegrationGraph = true;//mntPt的source node存在于semantic model tree中
                        if(mntPt.getSource().getId().equals(Root.getId())) {
                            IsRoot = true;
                        }
                        break;
                    }
//                    for(Node j: SearchStateInternalnodesMappingIntegrationGraph.get(i)){
//                        System.out.println("输出映射信息：" + i.getId() + "||" + j.getId());
//                    }
                }
                System.out.println("ExistInIntegrationGraph:" + ExistInIntegrationGraph);
                System.out.println("IsRoot:" + IsRoot);


                //如果mntPt的source node存在于semantic model tree中，并且为semantic model tree中的root，则需找common node将两者联系起来
                if(ExistInIntegrationGraph&&IsRoot){
                    //保存每个mntPt的所有的待添加路径信息
                    AllconnectedPaths = new ArrayList<List<String>>();
                    AllconnectedPathsNode = new ArrayList<List<Node>>();
                    System.out.println("找common node----------");
                }
                //如果mntPt的source node存在于semantic model tree中，且不为root，则需找root到mntPt之间的路径
                else if(ExistInIntegrationGraph){
                    //保存每个mntPt的所有的待添加路径信息
                    AllconnectedPaths = new ArrayList<List<String>>();
                    AllconnectedPathsNode = new ArrayList<List<Node>>();

                    System.out.println("找root到mntPt之间的路径----------");
                    //取出root在integration graph中的mapping nodes set
                    RootMappingNodes = SearchStateInternalnodesMappingIntegrationGraph.get(Root);
                    System.out.println("RootMappingNodes:" + RootMappingNodes.size());

                    //遍历每个root到integration中的nodes
                    for(Node rootmappingnode: RootMappingNodes){
                        System.out.println("rootmappingnode:" + rootmappingnode.getId()+"||"+mntPt.getSource().getId());
                        connectedPathsNode = new ArrayList<List<Node>>();
                        findAllPathNode(IntegrationGraphLinks,rootmappingnode.getId(),mntPt.getSource().getId(),3);
                        System.out.println("connectedPathsNode.size:"+connectedPathsNode.size());
                        //connectedPaths ← all paths that connect leaves or root of st with mntPt
                        int index = 0;//用于测试,对于每个要添加的node,现只连接其第一条路径

                        //获得每个mntPt的所有待添加路径信息
                        for(List<Node> path: connectedPathsNode) {
                            AllconnectedPathsNode.add(path);
                        }
//                        for(List<String> path: connectedPaths){
//                            AllconnectedPaths.add(path);
//                            InitialStartSearchState = (DirectedWeightedMultigraph<Node,DefaultLink>) StartSearchState.getGraph().clone();//初始化semantic model tree
////                            System.out.println("初始化时InitialStartSearchState的nodes:"+InitialStartSearchState.vertexSet().size());
////                            System.out.println("初始化时InitialStartSearchState的links:"+InitialStartSearchState.edgeSet().size());
//                            System.out.println("初始化时StartSearchState的nodes:"+StartSearchState.getGraph().vertexSet().size());
//                            System.out.println("初始化时StartSearchState的links:"+StartSearchState.getGraph().edgeSet().size());
//
//                            eachPathAddedNodes.add(node);//添加需要add的mntPt target(column) node
//                            /**添加target node**/
//                            InitialStartSearchState.addVertex(node);
//                            /**添加mntPt**/
//                            String mntPtlinkId = LinkIdFactory.getLinkId(mntPt.getId(), mntPt.getSource().getId(), node.getId());
//                            System.out.println("mntPtlinkId:" + mntPt.getId());
//                            LabeledLink mntPtlink = new DataPropertyLink(mntPtlinkId,new Label(mntPt.getUri()));
////                            System.out.println("mntPtlink.getUri:"+mntPtlink.getUri());
//                            InitialStartSearchState.addEdge(mntPt.getSource(),node,mntPtlink);
//                            /**完成target(column) node和mntPt的添加**/
//
////                            index++;
////                            if(index > 1)
////                                break;
//                            System.out.println(mntPt.getSource().getId()+"的connectedPaths:"+path);
//                            //存储每个path要添加的nodes
//                            for(String nodeId: path) {
//                                for(Node integrationnode: IntegrationGraph.vertexSet()) {
//                                    if(integrationnode.getId().equals(nodeId)) {
//                                        InitialStartSearchState.addVertex(integrationnode);//添加每个path要add的nodes
//                                        eachPathAddedNodes.add(integrationnode);
//                                    }
//                                }
//                            }
////                            //输出每条(第一条)path要添加的nodes信息
////                            for(Node pathnode: eachPathAddedNodes) {
////                                //向semantic model tree中添加这些nodes
////                                System.out.println("输出每条(第一条)path要添加的nodes信息" + pathnode.getId());
////                            }////////////////////////////////////////////
//                            //存储每个path要添加的links信息
//                            for(int i=0;i<path.size()-1;i++){
////                                System.out.println("输出i的信息:" + path.get(i)+"||"+path.get(i+1));
//                                for(DefaultLink integrationlink: IntegrationGraph.edgeSet()){
//                                    if((integrationlink.getSource().getId().equals(path.get(i)))&&(integrationlink.getTarget().getId().equals(path.get(i+1)))){//待添加的links
//                                        boolean isaddedlink = true;
//                                        LabeledLink addedlink = new DataPropertyLink(integrationlink.getId(),new Label(integrationlink.getUri()));
//                                        for(LabeledLink semanticmodeltreelink: StartSearchState.getGraph().edgeSet()) {//遍历semantic model tree中的links
////                                            if(!(integrationlink.getSource().getId()+integrationlink.getId()))
//                                            if(integrationlink.getId().equals(semanticmodeltreelink.getId())) {
//                                                isaddedlink = false;
//                                                break;
//                                            }
//                                        }
//                                        if(isaddedlink) {
//                                            InitialStartSearchState.addEdge(integrationlink.getSource(), integrationlink.getTarget(), addedlink);
//                                        }
//                                        eachPathAddedLinks.add(integrationlink);//测试
//                                    }
//                                }
//                            }
////                            //输出每条(第一条)path要添加的links信息
////                            for(DefaultLink pathlink: eachPathAddedLinks) {
////                                //向semantic model tree中添加这些nodes
////                                System.out.println("输出每条(第一条)path要添加的links信息" + pathlink.getId());
////                            }//////////////////////////////
//
//                            /**保存添加一个target(column) node的nextsearchstate**/
//
//                            number++;
//                            GraphVizUtil.exportJGraphToGraphviz(InitialStartSearchState,
//                                    "next_state_graph",
//                                    false,
//                                    GraphVizLabelType.LocalId,
//                                    GraphVizLabelType.LocalUri,
//                                    false,
//                                    true,
//                                    "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\next-state-graph\\" + "next_state_" + number + ".graph.json" + ".dot");
//
//                            System.out.println("InitialStartSearchState的nodes:"+InitialStartSearchState.vertexSet().size());
//                            System.out.println("InitialStartSearchState的links:"+InitialStartSearchState.edgeSet().size());
//                        }
                    }

                    /****/
                    System.out.println("AllconnectedPathsNode.size:" + AllconnectedPathsNode.size());
                    for(List<Node> path: AllconnectedPathsNode){
                        InitialStartSearchStateSM = StartSearchState.clone();
//                        InitialStartSearchState = (DirectedWeightedMultigraph<Node,DefaultLink>) StartSearchState.getGraph().clone();//初始化semantic model tree
//                            System.out.println("初始化时InitialStartSearchState的nodes:"+InitialStartSearchState.vertexSet().size());
//                            System.out.println("初始化时InitialStartSearchState的links:"+InitialStartSearchState.edgeSet().size());
                        System.out.println("初始化时StartSearchState的nodes:"+StartSearchState.getGraph().vertexSet().size());
                        System.out.println("初始化时StartSearchState的links:"+StartSearchState.getGraph().edgeSet().size());

                        eachPathAddedNodes.add(node);//添加需要add的mntPt target(column) node
                        /**添加target node**/
//                        InitialStartSearchState.addVertex(node);
                        InitialStartSearchStateSM.getGraph().addVertex(node);
                        /**添加mntPt**/
                        String mntPtlinkId = LinkIdFactory.getLinkId(mntPt.getId(), mntPt.getSource().getId(), node.getId());
                        System.out.println("mntPtlinkId:" + mntPt.getId());
                        LabeledLink mntPtlink = new DataPropertyLink(mntPtlinkId,new Label(mntPt.getUri()));
//                            System.out.println("mntPtlink.getUri:"+mntPtlink.getUri());
//                        InitialStartSearchState.addEdge(mntPt.getSource(),node,mntPtlink);
                        InitialStartSearchStateSM.getGraph().addEdge(mntPt.getSource(),node,mntPtlink);
                        /**完成target(column) node和mntPt的添加**/

//                            index++;
//                            if(index > 1)
//                                break;
                        System.out.println(mntPt.getSource().getId()+"的connectedPaths:"+path);
                        //存储每个path要添加的nodes
                        for(Node nodeInfo: path) {
                            for(Node integrationnode: IntegrationGraph.vertexSet()) {
                                if(integrationnode.getId().equals(nodeInfo.getId())) {
//                                    InitialStartSearchState.addVertex(integrationnode);//添加每个path要add的nodes\
                                    InitialStartSearchStateSM.getGraph().addVertex(integrationnode);
                                    eachPathAddedNodes.add(integrationnode);
                                }
                            }
                        }
//                            //输出每条(第一条)path要添加的nodes信息
//                            for(Node pathnode: eachPathAddedNodes) {
//                                //向semantic model tree中添加这些nodes
//                                System.out.println("输出每条(第一条)path要添加的nodes信息" + pathnode.getId());
//                            }////////////////////////////////////////////
                        //存储每个path要添加的links信息
                        for(int i=0;i<path.size()-1;i++){
//                                System.out.println("输出i的信息:" + path.get(i)+"||"+path.get(i+1));
                            for(DefaultLink integrationlink: IntegrationGraph.edgeSet()){
                                if((integrationlink.getSource().getId().equals(path.get(i).getId()))&&(integrationlink.getTarget().getId().equals(path.get(i+1).getId()))){//待添加的links
                                    boolean isaddedlink = true;
                                    LabeledLink addedlink = new DataPropertyLink(integrationlink.getId(),new Label(integrationlink.getUri()));
                                    for(LabeledLink semanticmodeltreelink: StartSearchState.getGraph().edgeSet()) {//遍历semantic model tree中的links
//                                            if(!(integrationlink.getSource().getId()+integrationlink.getId()))
                                        if(integrationlink.getId().equals(semanticmodeltreelink.getId())) {
                                            isaddedlink = false;
                                            break;
                                        }
                                    }
                                    if(isaddedlink) {
//                                        InitialStartSearchState.addEdge(integrationlink.getSource(), integrationlink.getTarget(), addedlink);
                                        InitialStartSearchStateSM.getGraph().addEdge(integrationlink.getSource(), integrationlink.getTarget(), addedlink);
                                    }
                                    eachPathAddedLinks.add(integrationlink);//测试
                                }
                            }
                        }
//                            //输出每条(第一条)path要添加的links信息
//                            for(DefaultLink pathlink: eachPathAddedLinks) {
//                                //向semantic model tree中添加这些nodes
//                                System.out.println("输出每条(第一条)path要添加的links信息" + pathlink.getId());
//                            }//////////////////////////////

                        /**保存添加一个target(column) node的nextsearchstate**/

                        number++;
//                        GraphVizUtil.exportJGraphToGraphviz(InitialStartSearchState,
//                                "next_state_graph",
//                                false,
//                                GraphVizLabelType.LocalId,
//                                GraphVizLabelType.LocalUri,
//                                false,
//                                true,
//                                "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\next-state-graph\\" + "next_state_" + number + ".graph.json" + ".dot");
                        GraphVizUtil.exportSemanticModelToGraphviz(InitialStartSearchStateSM,GraphVizLabelType.LocalId,
                            GraphVizLabelType.LocalUri,true,true,"E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\next-state-graph\\" + "next_state_" + number + ".graph.json" + ".dot");

                        newTrees.add(InitialStartSearchStateSM);
                        System.out.println("InitialStartSearchState的nodes:"+InitialStartSearchStateSM.getGraph().vertexSet().size());
                        System.out.println("InitialStartSearchState的links:"+InitialStartSearchStateSM.getGraph().edgeSet().size());
                    }
                }
                else{
                    //保存每个mntPt的所有的待添加路径信息
                    AllconnectedPaths = new ArrayList<List<String>>();
                    AllconnectedPathsNode = new ArrayList<List<Node>>();
                    System.out.println("找semantic model tree中任一internal node到mntPt的source node之间的路径");
                }
            }
        }
        System.out.println("newTrees的大小："+newTrees.size());
        return null;
    }

    public static void SearchForIntegrationGraph(int SourceSemanticModelIndex) throws Exception {
        System.out.println("进入SearchForIntegrationGraph");
        DataPropertyLink addlink,addlink1,addlink2,addlink3,addlink4,addlink5,addlink6;
        ClassInstanceLink adddatalink;
        Node source = null,target = null,source1=null,target1=null,source2=null,target2=null;
        List<DefaultLink> LinkList = new ArrayList<DefaultLink>();


//        DirectedWeightedMultigraph<Node, DefaultLink> IntegrationGraph = null;
//        /**获取integration graph**/
//        IntegrationGraph = getIntegrationGraph(0, new Integer[]{1});
//
//        System.out.println(IntegrationGraph.edgeSet().size());
//        System.out.println(IntegrationGraph.vertexSet().size());
//
//        /**保存integration graph**/
//        GraphUtil.exportJson(IntegrationGraph, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\alignment-graph\\" + "00-01" + ".graph.json" + ".json",true,true);
//        GraphVizUtil.exportJGraphToGraphviz(IntegrationGraph,
//                "train_model_integration_graph",
//                false,
//                GraphVizLabelType.LocalId,
//                GraphVizLabelType.LocalUri,
//                false,
//                true,
//                "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\alignment-graph\\" + "00-01" + ".graph.json" + ".dot");
//        System.out.println("完成SearchForIntegrationGraph");

        /**获取Source Semantic Model**/
        if(SemanticModels == null) {
            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
        }
        SemanticModel SourceSemanticModel = SemanticModels.get(SourceSemanticModelIndex);
        /**添加一个internal node**/
        Label internalnodelabel = new Label("http://erlangen-crm.org/current/E35_Title");
        InternalNode internalnode = new InternalNode("http://erlangen-crm.org/current/E35_Title2",internalnodelabel);

        SourceSemanticModel.getGraph().addVertex(internalnode);

        for(Node node:SourceSemanticModel.getGraph().vertexSet()){
            if(node.getId().equals("http://erlangen-crm.org/current/E22_Man-Made_Object1")){
                System.out.println("添加link");
                Label internallink = new Label("http://erlangen-crm.org/current/P102_has_title");
                addlink = new DataPropertyLink("http://erlangen-crm.org/current/E12_Production1---http://erlangen-crm.org/current/P102_has_title---http://erlangen-crm.org/current/E35_Title2",internallink);
                SourceSemanticModel.getGraph().addEdge(node,internalnode,addlink);
            }
            if(node.getId().equals("http://erlangen-crm.org/current/E54_Dimension1")){
                System.out.println("添加internallink");
                Label internallink = new Label("http://www.w3.org/2000/01/rdf-schema#label");
                addlink = new DataPropertyLink("http://erlangen-crm.org/current/E35_Title2---http://www.w3.org/2000/01/rdf-schema#label---http://erlangen-crm.org/current/E54_Dimension1",internallink);
                SourceSemanticModel.getGraph().addEdge(internalnode,node,addlink);
            }
            if(node.getId().equals("http://erlangen-crm.org/current/E21_Person1")){
                source = node;
            }
            if(node.getId().equals("http://erlangen-crm.org/current/E52_Time-Span3")){
                target = node;
            }
            if(node.getId().equals("http://erlangen-crm.org/current/E67_Birth1")){
                source1 = node;
            }
            if(node.getId().equals("http://erlangen-crm.org/current/E69_Death1")){
                target1 = node;
            }
            if(node.getId().equals("http://erlangen-crm.org/current/E35_Title1")){
                source2 = node;
            }
            if(node.getId().equals("http://erlangen-crm.org/current/E35_Title2")){
                target2 = node;
            }

//            System.out.println("node.getId():"+node.getId());
        }
        Label internallinksourcetotarget = new Label("http://www.w3.org/2000/01/rdf-schema#label");
        Label internallinktargettosource = new Label("http://erlangen-crm.org/current/P3_has_note");
        addlink1 = new DataPropertyLink("http://erlangen-crm.org/current/E21_Person1---http://www.w3.org/2000/01/rdf-schema#label---http://erlangen-crm.org/current/E52_Time-Span3",internallinksourcetotarget);
        addlink2 = new DataPropertyLink("http://erlangen-crm.org/current/E52_Time-Span3---http://erlangen-crm.org/current/P3_has_note---http://erlangen-crm.org/current/E21_Person1",internallinktargettosource);
        addlink3 = new DataPropertyLink("http://erlangen-crm.org/current/E67_Birth1---http://erlangen-crm.org/current/P3_has_note---http://erlangen-crm.org/current/E69_Death1",internallinktargettosource);
        addlink4 = new DataPropertyLink("http://erlangen-crm.org/current/E69_Death1---http://www.w3.org/2000/01/rdf-schema#label---http://erlangen-crm.org/current/E67_Birth1",internallinksourcetotarget);
        addlink5 = new DataPropertyLink("http://erlangen-crm.org/current/E35_Title1---http://www.w3.org/2000/01/rdf-schema#label---http://erlangen-crm.org/current/E35_Title2",internallinksourcetotarget);
        addlink6 = new DataPropertyLink("http://erlangen-crm.org/current/E35_Title2---http://www.w3.org/2000/01/rdf-schema#label---http://erlangen-crm.org/current/E35_Title1",internallinksourcetotarget);
        SourceSemanticModel.getGraph().addEdge(source,target,addlink1);
        SourceSemanticModel.getGraph().addEdge(target,source,addlink2);
        SourceSemanticModel.getGraph().addEdge(source1,target1,addlink3);
        SourceSemanticModel.getGraph().addEdge(target1,source1,addlink4);
        SourceSemanticModel.getGraph().addEdge(source2,target2,addlink5);
        SourceSemanticModel.getGraph().addEdge(target2,source2,addlink6);


        for(ColumnNode columnnode:SourceSemanticModel.getColumnNodes()){
            if(columnnode.getColumnName().equals("Title")){
                System.out.println("添加datalink");
                adddatalink = new ClassInstanceLink("http://erlangen-crm.org/current/E35_Title2---http://www.w3.org/2000/01/rdf-schema#label---HN1385");
                SourceSemanticModel.getGraph().addEdge(internalnode,columnnode,adddatalink);
            }
        }

        System.out.println(SourceSemanticModel.getGraph().vertexSet().size());
        System.out.println(SourceSemanticModel.getGraph().edgeSet().size());
//        System.out.println(SourceSemanticModel.getInternalNodes().size());
        GraphVizUtil.exportSemanticModelToGraphviz(SourceSemanticModel,GraphVizLabelType.LocalId,
                GraphVizLabelType.LocalUri,true,true,"E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\alignment-graph\\" + "00" + ".graph.json" + ".dot");

        //遍历语义模型中所有的边
        for(LabeledLink link: SourceSemanticModel.getGraph().edgeSet()){
            System.out.println("getSource:"+link.getSource().getId());
            System.out.println("getTarget:"+link.getTarget().getId());
            LinkList.add(link);//定义一个列表以存储SourceSemanticModel中的所有link
        }
//        connectedPaths = new ArrayList<List<String>>();
        connectedPathsNode = new ArrayList<List<Node>>();
        connectedPathsLink = new ArrayList<List<DefaultLink>>();//////5.13
//        findAllPath(LinkList,"http://erlangen-crm.org/current/E22_Man-Made_Object1","HN1385",2);
//        findAllPathNode(LinkList,"http://erlangen-crm.org/current/E22_Man-Made_Object1","HN1385",3);
        newfindAllPathLink(LinkList,"http://erlangen-crm.org/current/E22_Man-Made_Object1","HN1386",6);

//        List<String> list1 = Arrays.asList("http://erlangen-crm.org/current/E22_Man-Made_Object1", "http://erlangen-crm.org/current/E35_Title1", "HN1385");
//        List<String> list2 = Arrays.asList("http://erlangen-crm.org/current/E22_Man-Made_Object1", "http://erlangen-crm.org/current/E35_Title1", "http://erlangen-crm.org/current/E35_Title2", "HN1385");
//        System.out.println("list1:"+list1);
//        System.out.println("list2:"+list2);
//        connectedPaths.add(list1);
//        connectedPaths.add(list2);

//        System.out.println("connectedPaths.size():" + connectedPaths.size());
//        System.out.println("connectedPaths:" + connectedPaths);
//        System.out.println("connectedPaths.size():" + connectedPathsNode.size());
//        System.out.println("connectedPaths:" + connectedPathsNode);
        System.out.println("connectedNodePaths.size():" + connectedPathsNode.size());
        System.out.println("connectedLinkPaths.size():" + connectedPathsLink.size());
        System.out.println("connectedNodePaths:" + connectedPathsNode);
//        System.out.println("connectedLinkPaths:" + connectedPathsLink);
//        for(int i=0;i<connectedPaths.size();i++){
//            System.out.println("path信息:" + connectedPaths.get(i));
//        }
//        for(int i=0;i<connectedPathsNode.size();i++){
//            System.out.println("path信息:" + connectedPathsNode.get(i));
//        }
        for(int i=0;i<connectedPathsNode.size();i++){
            System.out.println("nodepath信息:" + connectedPathsNode.get(i));
            for(Node node: connectedPathsNode.get(i)){
                System.out.println("nodepath的link信息:" + node.getId());
            }
        }

        for(int i=0;i<connectedPathsLink.size();i++){
            System.out.println("path信息:" + connectedPathsLink.get(i));
            for(DefaultLink link: connectedPathsLink.get(i)){
                System.out.println("path的link信息:" + link.getId());
            }

        }

    }

    /**找source和target之间所有的路径**/
    public static void findAllPath(List<DefaultLink> LinkList,String source,String target,int length){
//        System.out.println("进入findAllPath函数中");
        if(nowPath.contains(source)){
//            System.out.println("输出环:"+nowPath);
            nowPath.remove(nowPath.size()-1);//返回上一个node
            return;
        }

        //遍历图中的所有link
        for(int i=0;i<LinkList.size();i++){
            DefaultLink link = LinkList.get(i);
            if(link.getSource().getId().equals(source)){//如果此边的source为要查找路径的起始source
                nowPath.add(link.getSource().getId());
                if(nowPath.size()>=length){
                    nowPath.remove(nowPath.size()-1);
                    continue;
                }
                if(link.getTarget().getId().equals(target)){//如果此边的target为要查找路径的终点target
                    nowPath.add(link.getTarget().getId());
                    nowPath.toArray();

                    connectedPaths.add(Arrays.asList(Arrays.copyOf(nowPath.toArray(),nowPath.toArray().length, String[].class)));

                    System.out.println("输出路径：" + nowPath);

                    /**因为添加了终点路径，所以要返回两次**/
                    nowPath.remove(nowPath.size()-1);
                    nowPath.remove(nowPath.size()-1);
                    /**已经找到路径，返回上层找其他路径**/
                    continue;
                }
                findAllPath(LinkList,link.getTarget().getId(),target,length);
            }
        }
        /**如果找不到下个节点，返回上层**/
        if(nowPath.size()>0){
//            System.out.println("如果找不到下个节点，返回上层");
            nowPath.remove(nowPath.size()-1);
        }
//        if(nowPath.size() == 0){
//            System.out.println("findAllPath中的connectedPaths.size():" + connectedPaths.size());
//            System.out.println("findAllPath中的connectedPaths:" + connectedPaths);
//        }
    }

    /**存储Node信息的findAllPathNode函数**/
    public static void findAllPathNode(List<DefaultLink> LinkList,String source,String target,int length){
//        System.out.println("进入findAllPathNode函数中");
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

//                    System.out.println("输出路径：" + nowPathNode);

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

    /**存储Link信息的findAllPathLink函数**/
    public static void findAllPathLink(List<DefaultLink> LinkList,String source,String target,int length){
        System.out.println("进入findAllPathLink函数中");
        if(nowPathLink.size()>1) {
            for(int i=0;i<nowPathLink.size() - 1;i++){
                if(nowPathLink.get(nowPathLink.size() - 1).getTarget().getId().equals(nowPathLink.get(i).getSource().getId())){
                    nowPathLink.remove(nowPathLink.size()-1);//返回上一个node
                    return;
                }
            }
//            DefaultLink previouslink = nowPathLink.get(nowPathLink.size() - 2);
//            for(DefaultLink link: nowPathLink){
//                if(link.getSource().getId().equals(previouslink.getTarget().getId())&&link.getTarget().getId().equals(previouslink.getSource().getId())){
//                    nowPathLink.remove(nowPathLink.size()-1);//返回上一个node
//                    return;
//                }
//            }
        }

        //遍历图中的所有link
        for(int i=0;i<LinkList.size();i++) {
            DefaultLink link = LinkList.get(i);
            if (link.getSource().getId().equals(source)) {//如果此边的source为要查找路径的起始source
                nowPathLink.add(link);
                if(nowPathLink.size() >= length){
                    nowPathLink.remove(nowPathLink.size()-1);
                    continue;
                }
                if(link.getTarget().getId().equals(target)){//如果此边的target为要查找路径的最终target
//                    nowPathLink.add(link);
                    nowPathLink.toArray();
                    connectedPathsLink.add(Arrays.asList(Arrays.copyOf(nowPathLink.toArray(), nowPathLink.toArray().length, DefaultLink[].class)));

                    System.out.println("输出路径：" + nowPathLink);

                    /**因为添加了终点路径，所以要返回一次**/
                    nowPathLink.remove(nowPathLink.size() - 1);
//                    nowPathNode.remove(nowPathNode.size() - 1);
                    /**已经找到路径，返回上层找其他路径**/
                    continue;
                }
                findAllPathLink(LinkList, link.getTarget().getId(), target, length);
            }
        }
        /**如果找不到下个节点，返回上层**/
        if(nowPathLink.size()>0){
            nowPathLink.remove(nowPathLink.size()-1);
        }
    }

    /**7.19 存储link信息的newfindAllPathLink函数**/
    public static void newfindAllPathLink(List<DefaultLink> LinkList,String source,String target,int length){
//        System.out.println("进入newfindAllPathLink函数中");
        for(Node node: nowPathNode){
            if(node.getId().equals(source)){
                nowPathNode.remove(nowPathNode.size()-1);//返回上一个node
                nowPathLink.remove(nowPathLink.size()-1);
                return;
            }
        }
        //遍历图中的所有link
        for(int i=0;i<LinkList.size();i++) {
            DefaultLink link = LinkList.get(i);
            if ((link.getSource().getId().equals(source))) {//如果此边的source为要查找路径的起始source
                nowPathNode.add(link.getSource());
                nowPathLink.add(link);
//                System.out.println("输出node:" + link.getSource().getId());
//                System.out.println("输出link:" + link.getId());
                if(nowPathNode.size() >= length){
                    nowPathNode.remove(nowPathNode.size()-1);
                    nowPathLink.remove(nowPathLink.size()-1);
                    continue;
                }
                if(link.getTarget().getId().equals(target)){//如果此边的target为要查找路径的最终target
                    nowPathNode.add(link.getTarget());
//                    nowPathLink.add(link);
                    nowPathNode.toArray();
                    nowPathLink.toArray();
//                    System.out.println("输出nowPathNode:" + nowPathNode);
//                    System.out.println("输出nowPathLink:" + nowPathLink);

                    connectedPathsNode.add(Arrays.asList(Arrays.copyOf(nowPathNode.toArray(), nowPathNode.toArray().length, Node[].class)));
                    connectedPathsLink.add(Arrays.asList(Arrays.copyOf(nowPathLink.toArray(), nowPathLink.toArray().length, DefaultLink[].class)));
//                    System.out.println("输出路径：" + nowPathNode);

                    /**因为添加了终点路径，所以要返回两次**/
                    nowPathNode.remove(nowPathNode.size() - 1);
                    nowPathNode.remove(nowPathNode.size() - 1);
                    nowPathLink.remove(nowPathLink.size() - 1);
                    /**已经找到路径，返回上层找其他路径**/
                    continue;
                }
                newfindAllPathLink(LinkList, link.getTarget().getId(), target, length);
            }
        }
        /**如果找不到下个节点，返回上层**/
        if(nowPathNode.size()>0){
            nowPathNode.remove(nowPathNode.size()-1);
            nowPathLink.remove(nowPathLink.size()-1);
        }
    }

    /**7.19 存储link信息的newfindAllPathLinkForPath3**/
    public static void newfindAllPathLinkForClearPath(List<DefaultLink> LinkList,String source,String target,int length){
//        System.out.println("进入newfindAllPathLink函数中");
        for(Node node: nowPathNode){
            if(node.getId().equals(source)){
                nowPathNode.remove(nowPathNode.size()-1);//返回上一个node
                nowPathLink.remove(nowPathLink.size()-1);
                return;
            }
        }
        //遍历图中的所有link
        for(int i=0;i<LinkList.size();i++) {
            DefaultLink link = LinkList.get(i);
            if ((!(link.getUri().equals("http://isi.edu/integration/karma/dev#defaultLink")))&&(link.getSource().getId().equals(source))) {//如果此边的source为要查找路径的起始source
                nowPathNode.add(link.getSource());
                nowPathLink.add(link);
//                System.out.println("输出node:" + link.getSource().getId());
//                System.out.println("输出link:" + link.getId());
                if(nowPathNode.size() >= length){
                    nowPathNode.remove(nowPathNode.size()-1);
                    nowPathLink.remove(nowPathLink.size()-1);
                    continue;
                }
                if(link.getTarget().getId().equals(target)){//如果此边的target为要查找路径的最终target
                    nowPathNode.add(link.getTarget());
//                    nowPathLink.add(link);
                    nowPathNode.toArray();
                    nowPathLink.toArray();
//                    System.out.println("输出nowPathNode:" + nowPathNode);
//                    System.out.println("输出nowPathLink:" + nowPathLink);

                    connectedPathsNode.add(Arrays.asList(Arrays.copyOf(nowPathNode.toArray(), nowPathNode.toArray().length, Node[].class)));
                    connectedPathsLink.add(Arrays.asList(Arrays.copyOf(nowPathLink.toArray(), nowPathLink.toArray().length, DefaultLink[].class)));
//                    System.out.println("输出路径：" + nowPathNode);

                    /**因为添加了终点路径，所以要返回两次**/
                    nowPathNode.remove(nowPathNode.size() - 1);
                    nowPathNode.remove(nowPathNode.size() - 1);
                    nowPathLink.remove(nowPathLink.size() - 1);
                    /**已经找到路径，返回上层找其他路径**/
                    continue;
                }
                newfindAllPathLinkForClearPath(LinkList, link.getTarget().getId(), target, length);
            }
        }
        /**如果找不到下个节点，返回上层**/
        if(nowPathNode.size()>0){
            nowPathNode.remove(nowPathNode.size()-1);
            nowPathLink.remove(nowPathLink.size()-1);
        }
    }

    /**查找某一节点的祖先节点**/
    //输入是有向图 某一结点信息
    //输出是某节点的祖先节点列表
    public static void findAncestorNodes(int SourceSemanticModelIndex,String BeSearchedNodeId) throws Exception {
        System.out.println("进入findAncestorNodes函数");
        //首先读入某一语义模型，将其转换为有向图
        if(SemanticModels == null) {
            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
        }
        SemanticModel sourcesemanticmodel = SemanticModels.get(SourceSemanticModelIndex);
        DirectedWeightedMultigraph<Node,LabeledLink> BeSearchedGraph = null;
        BeSearchedGraph = sourcesemanticmodel.getGraph();
        List<DefaultLink> LinkList = new ArrayList<DefaultLink>();
        for(DefaultLink link: BeSearchedGraph.edgeSet()){
            LinkList.add(link);
        }

        //可以使用搜索方法找到root到BeSearchedNodeId的路径，路径上所有的的节点就是此BeSearchedNodeId的祖先节点
        connectedPathsNode = new ArrayList<List<Node>>();
        findAllPathNode(LinkList,"http://erlangen-crm.org/current/E22_Man-Made_Object1",BeSearchedNodeId,100);
        System.out.println(connectedPathsNode);
        for(List<Node> nodelist: connectedPathsNode){
            for(Node node: nodelist){
                System.out.println("输出路径上的节点信息:"+node.getId());
            }
        }
    }

    /**在Integration Graph中查找某一节点的祖先节点**/
    public static Set<Node> findAncestorNodesInIntegrationGraph(DirectedWeightedMultigraph<Node,DefaultLink> IntegrationGraph,Node BeSearchedNode) throws Exception {
        System.out.println("进入findAncestorNodesInIntegrationGraph函数");

        //存储integration graph中的所有links
        List<DefaultLink> LinkList = new ArrayList<DefaultLink>(IntegrationGraph.edgeSet());
        //存储BeSearchedNode的ancestor nodes
        Set<Node> AncestorNodes = new HashSet<Node>();

        //遍历integration graph中的所有links
        for(DefaultLink link: IntegrationGraph.edgeSet()){
            if(link.getTarget().equals(BeSearchedNode)){
                AncestorNodes.add(link.getSource());
            }
        }
        System.out.println("输出" + BeSearchedNode.getId() + "的ancestor nodes的个数:" + AncestorNodes.size());
//        if(BeSearchedNode.getId().equals("http://erlangen-crm.org/current/E30_Right1")){
//            for(Node node: AncestorNodes){
//                System.out.println("输出E30_Right1的ancestornode:" + node.getId());
//            }
//        }
        return AncestorNodes;
    }

    /**检查某一smenatic model是否为tree**/
    public static void IsSemanticModeHasOnlyRoot(SemanticModel sm){
        List<Node> RootList = new ArrayList<Node>();
        //遍历sm中的所有internal nodes
        for(Node internalnode: sm.getInternalNodes()){
            //遍历sm中的所有links
            for(DefaultLink link: sm.getGraph().edgeSet()){
                if(link.getTarget()==internalnode){
                    //说明internalnode不是root 跳出循环 检查下一个internal node
                    break;
                }
            }
            RootList.add(internalnode);
        }
        if(RootList.size()==1){
            System.out.println("sm不是tree");
        }
        else{
            System.out.println("sm是tree");
        }
    }

    /**存储节点及其IncomingLinks和OutgoingLinks**/
    public static void NodeIncomingOutgoing(int SourceSemanticModelIndex,String nodeId) throws Exception {
        System.out.println("进入NodeIncomingOutgoing函数");
        //首先读入某一语义模型，将其转换为有向图
        if (SemanticModels == null) {
            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
        }
        SemanticModel sourcesemanticmodel = SemanticModels.get(SourceSemanticModelIndex);
        DirectedWeightedMultigraph<Node, LabeledLink> BeSearchedGraph = null;
        BeSearchedGraph = sourcesemanticmodel.getGraph();

        NodeLinks nodelinks = null;
        for (Node node : BeSearchedGraph.vertexSet()) {
            if (node.getId().equals(nodeId)) {
                nodelinks = new NodeLinks(node,getIncomingAndOutgoingLinks(SourceSemanticModelIndex, node).get(0),getIncomingAndOutgoingLinks(SourceSemanticModelIndex, node).get(1));
            }
        }
        System.out.println("nodelinks:"+nodelinks.Node.getId());
        System.out.println("nodelinks:"+nodelinks.IncomingLinks.size());
        System.out.println("nodelinks:"+nodelinks.OutgoingLinks.size());
    }

    /**获取每一个node的IncomingLinks及OutgoingLinks,将其存储在列表中**/
    public static List<List<DefaultLink>> getIncomingAndOutgoingLinks(int SourceSemanticModelIndex, Node node) throws Exception {
        List<DefaultLink> IncomingLinks = new ArrayList<DefaultLink>();
        List<DefaultLink> OutgoingLinks = new ArrayList<DefaultLink>();
        List<List<DefaultLink>> IncomingAndOutgoing = new ArrayList<List<DefaultLink>>();

        //首先读入某一语义模型，将其转换为有向图
        if(SemanticModels == null) {
            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
        }
        SemanticModel sourcesemanticmodel = SemanticModels.get(SourceSemanticModelIndex);
        for(DefaultLink sourcesmlink: sourcesemanticmodel.getGraph().edgeSet()){
            if(sourcesmlink.getTarget().equals(node)){
                IncomingLinks.add(sourcesmlink);
            }
            if(sourcesmlink.getSource().equals(node)){
                OutgoingLinks.add(sourcesmlink);
            }
        }

        IncomingAndOutgoing.add(IncomingLinks);
        IncomingAndOutgoing.add(OutgoingLinks);

        return IncomingAndOutgoing;
    }

    /**5.17 测试两个SemanticModel是否相同**/
    public static Boolean IsSame() throws Exception{
        Boolean issame = false;
        Double a = null;
        /**获取Semantic Models**/
        if(SemanticModels == null) {
            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "negative-examples-json", ".json");
        }
        System.out.println("SemanticModels.size:"+SemanticModels.size());
        SemanticModel sm1 = SemanticModels.get(0);
        SemanticModel sm2 = SemanticModels.get(12);
        issame = sm1.getGraph().vertexSet().equals(sm2.getGraph().vertexSet());
        return issame;
    }

    /**给定语义模型 获取其嵌入表示  返回200dim 数据类型为BigDecimal的嵌入数组**/
    public static BigDecimal[] SemanticModelEmbedding(JSONObject jsonObject,SemanticModel sm) throws Exception{
        //获取嵌入表jsonObject

        /**获取语义模型**/
//        if(SemanticModels == null) {
//            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
//        }
//        SemanticModel sm = SemanticModels.get(8);
        /**获取语义模型**/
//        System.out.println("输出sm的vertexSet.size:" + sm.getGraph().vertexSet().size());
//        System.out.println("输出sm的edgeSet.size:" + sm.getGraph().edgeSet().size());
        //获取sm的link列表
        List<BigDecimal> source_embedding = new ArrayList<BigDecimal>();
        List<BigDecimal> target_embedding = new ArrayList<BigDecimal>();
        BigDecimal[] source_embedding_array = new BigDecimal[200];
        BigDecimal[] target_embedding_array = new BigDecimal[200];
        BigDecimal[][] relation_embedding_2darray = new BigDecimal[sm.getGraph().edgeSet().size()][200];//定义二维数组保存每条link的embedding
        List<BigDecimal[]> relation_embedding_array_list = new ArrayList<BigDecimal[]>();//由relation_source和relation_target求和取平均所得
        BigDecimal[] relation_embedding_array = new BigDecimal[200];
        int array_index = 0;
        int LinkTargetWithoutEmbedding = 0;
        for(DefaultLink link: sm.getGraph().edgeSet()){
            //查找每条link的source和target node的embeddings
            if(link.getSource().getId().equals("http://erlangen-crm.org/current/E55_Type3")){
                source_embedding = (List<BigDecimal>) JSON.parseObject(jsonObject.getString(link.getUri())).get("http://erlangen-crm.org/current/E55_Type1");
            }
            else {
                source_embedding = (List<BigDecimal>) JSON.parseObject(jsonObject.getString(link.getUri())).get(link.getSource().getId());
            }
            if(link.getTarget().getId().equals("http://erlangen-crm.org/current/E55_Type3")){
                target_embedding = (List<BigDecimal>) JSON.parseObject(jsonObject.getString(link.getUri())).get("http://erlangen-crm.org/current/E55_Type1");
            }
            else {
                target_embedding = (List<BigDecimal>) JSON.parseObject(jsonObject.getString(link.getUri())).get(link.getTarget().getId());
            }

            source_embedding_array = ListToArray(source_embedding);
            target_embedding_array = ListToArray(target_embedding);
            relation_embedding_array = AddArrays(source_embedding_array,target_embedding_array);//获取每个link对应的embedding
//            relation_embedding_array_list.add(relation_embedding_array);//存储每个link对应的embedding
            relation_embedding_2darray[array_index] = relation_embedding_array;//存储每个link对应的embedding
            ++array_index;
        }
        //遍历relation_embedding_array_list
        BigDecimal[] sm_embedding_array = new BigDecimal[200];//保存最终sm embedding

        System.out.println("输出relation_embedding_2darray.size:" + relation_embedding_2darray.length);

//        for(BigDecimal i: sm_embedding_array) {
//            System.out.println("输出sm_embedding_array的元素:" + i);
//        }
//        sm_embedding_array = AddArrays(relation_embedding_array_list.get(0),relation_embedding_array_list.get(1));
        BigDecimal temp_column = new BigDecimal(0);
        int num = relation_embedding_2darray.length;
        System.out.println("输出num:" + num);
        for(int i = 0;i<200;i++) {
            for(int j = 0;j<relation_embedding_2darray.length;j++) {
                temp_column = temp_column.add(relation_embedding_2darray[j][i]);
//            System.out.println("输出embedding.length:" + (relation_embedding_array_list.get(i)).length);
            }
            sm_embedding_array[i] = temp_column.divide(BigDecimal.valueOf(num),BigDecimal.ROUND_HALF_UP);
            temp_column = BigDecimal.valueOf(0);
        }
//        List<BigDecimal> sm_embedding_list =  Arrays.asList(sm_embedding_array);
//        System.out.println("输出sm_embedding_list:" + sm_embedding_list);
//        System.out.println("输出sm_embedding_list.size:" + sm_embedding_list.size());
        return sm_embedding_array;
    }

    /**读取embedding.jsonw文件**/
    public static JSONObject ReadEmbeddingJson(String pathname) throws Exception{
        String JsonFile = FileUtils.readFileToString(new File(pathname), "UTF-8");
        JSONObject jsonObject=JSON.parseObject(JsonFile);      //转换成object
        return jsonObject;
    }

    /**将List<BigDecimal>转换成BigDecimal[]**/
    public static BigDecimal[] ListToArray(List<BigDecimal> A){
        BigDecimal[] BigDecimal_Array = new BigDecimal[A.size()];
//        System.out.println("输出BigDecimal_Array.size:" + BigDecimal_Array.length);
        Object[] Object_BigDecimal_Array = A.toArray();
        BigDecimal_Array = Arrays.copyOfRange(Object_BigDecimal_Array,0,A.size(),BigDecimal[].class);
        return BigDecimal_Array;
    }

    /**两个数组对应元素相加并取平均值**/
    public static BigDecimal[] AddArrays(BigDecimal[] A,BigDecimal[] B){
        BigDecimal[] A_B = new BigDecimal[A.length];
        for (int i=0;i<A.length;i++) {
            A_B[i]=(A[i].add(B[i])).divide(BigDecimal.valueOf(2));
        }
        return A_B;
    }

    /**6.23 保存Double类型的二维数组到txt中**/
    public static void save2dDoubleArray(Double[][] array,String SavePath){
        FileWriter writeFile = null;
        try {
            File file = new File(SavePath);
            if(!file.exists()) {
                file.createNewFile();
            }
            writeFile = new FileWriter(file);
            for(int i = 0; i < array.length; i++) {
                for(int j = 0; j < array[0].length - 1; j++) {
                    writeFile.write(array[i][j] + ",");
                }
                writeFile.write(array[i][array[0].length - 1] + "");
                writeFile.write("\n");
            }
            writeFile.flush();
        } catch (Exception e) {//10.异常捕获
            e.printStackTrace();
        } finally {
            try {
                if(writeFile != null)
                    writeFile.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    /**6.23 保存二维数组到txt中**/
    public static void save2dArray(BigDecimal[][] array,String SavePath){
        FileWriter writeFile = null;
        try {
            File file = new File(SavePath);
            if(!file.exists()) {
                file.createNewFile();
            }
            writeFile = new FileWriter(file);
            for(int i = 0; i < array.length; i++) {
                for(int j = 0; j < array[0].length - 1; j++) {
                    writeFile.write(array[i][j] + ",");
                }
                writeFile.write(array[i][array[0].length - 1] + "");
                writeFile.write("\n");
            }
            writeFile.flush();
        } catch (Exception e) {//10.异常捕获
            e.printStackTrace();
        } finally {
            try {
                if(writeFile != null)
                    writeFile.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }
    /**6.23 读取txt文件转换为二维数组**/
    public static BigDecimal[][] readArray(String ReadPath) {
        //1.声明一个字符输入流
        FileReader reader = null;
        //2.声明一个字符输入缓冲流
        BufferedReader readerBuf = null;
        //3.声明一个二维数组
        BigDecimal[][] array = null;
        try {
            //4.指定reader的读取路径
            reader = new FileReader(ReadPath);
            //5.通过BufferedReader包装字符输入流
            readerBuf = new BufferedReader(reader);
            //6.创建一个集合，用来存放读取的文件的数据
            List<String> strList = new ArrayList<>();
            //7.用来存放一行的数据
            String lineStr;
            //8.逐行读取txt文件中的内容
            while((lineStr = readerBuf.readLine()) != null) {
                //9.把读取的行添加到list中
                strList.add(lineStr);
            }
            //10.获取文件有多少行
            int lineNum = strList.size();
            //11.获取数组有多少列
            String s =  strList.get(0);
            int columnNum = s.split("\\,").length;
            //12.根据文件行数创建对应的数组
            array = new BigDecimal[strList.size()][columnNum];
            //13.记录输出当前行
            int count = 0;
            //14.循环遍历集合，将集合中的数据放入数组中
            for(String str : strList) {
                //15.将读取的str按照","分割，用字符串数组来接收
                String[] strs = str.split("\\,");
                for(int i = 0; i < columnNum; i++) {
                    array[count][i] = BigDecimal.valueOf(Long.parseLong(strs[i]));
                }
                //16.将行数 + 1
                count++;
            }
        } catch (Exception e) {
            e.printStackTrace();
        } finally {
            //17.关闭字符输入流
            try {
                if(reader != null)
                    reader.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
            //18.关闭字符输入缓冲流
            try {
                if(readerBuf != null)
                    readerBuf.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
        //19.返回稀疏数组
        return array;
    }

    /**6.24 给定List<SemanticModel> 存储所有sm的embeddings**/
    public static BigDecimal[][] SaveSMListEmbedding(List<SemanticModel> SMList,JSONObject jsonObject,String SavePath) throws Exception{
        BigDecimal[] sm_embedding_array;//保存最终sm embedding
        BigDecimal[][] all_sm_embedding_array = new BigDecimal[SMList.size()][200];
        //遍历所有的sm
        int sm_index = 0;
        for(SemanticModel sm: SMList) {
            sm_embedding_array = SemanticModelEmbedding(jsonObject, sm);
            List<BigDecimal> sm_embedding_list = Arrays.asList(sm_embedding_array);
            System.out.println("输出sm_embedding_list:" + sm_embedding_list);
            System.out.println("输出sm_embedding_list.size:" + sm_embedding_list.size());
            all_sm_embedding_array[sm_index] = sm_embedding_array;//存储每个link对应的embedding
            ++sm_index;
        }
        System.out.println("输出all_sm_embedding_array.size:" + all_sm_embedding_array.length);
        //存储all_sm_embedding_array到txt中
        save2dArray(all_sm_embedding_array,SavePath);

        return all_sm_embedding_array;
    }

    /**6.23 给定sm文件夹 存储所有sm的embeddings**/
    public static BigDecimal[][] SaveSMEmbedding(String ReadPath,String SavePath) throws Exception {
        if(SemanticModels == null) {
            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(ReadPath, Params.MODEL_MAIN_FILE_EXT);
        }
//        SemanticModel sm = SemanticModels.get(27);
        JSONObject jsonObject = ReadEmbeddingJson("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\final_embedding_correct.json");
        BigDecimal[] sm_embedding_array;//保存最终sm embedding
        BigDecimal[][] all_sm_embedding_array = new BigDecimal[SemanticModels.size()][200];
        //遍历所有的sm
        int sm_index = 0;
        for(SemanticModel sm: SemanticModels) {
            sm_embedding_array = SemanticModelEmbedding(jsonObject, sm);
            List<BigDecimal> sm_embedding_list = Arrays.asList(sm_embedding_array);
            System.out.println("输出sm_embedding_list:" + sm_embedding_list);
            System.out.println("输出sm_embedding_list.size:" + sm_embedding_list.size());
            all_sm_embedding_array[sm_index] = sm_embedding_array;//存储每个link对应的embedding
            ++sm_index;
        }
        System.out.println("输出all_sm_embedding_array.size:" + all_sm_embedding_array.length);
        //存储all_sm_embedding_array到txt中
        save2dArray(all_sm_embedding_array,SavePath);

        return all_sm_embedding_array;
    }

    /**6.23 根据给定的路径创建文件夹**/
    public static void CreateFile(String DirectoryPath){
        File file = new File(DirectoryPath);
        if(!file.exists()) {
            if (file.mkdirs()) {
                System.out.println("创建" + DirectoryPath + "成功");
            } else {
                System.out.println("创建" + DirectoryPath + "失败");
            }
        }
    }

    /**6.23 给定正确的SemanticModel 求衍生出的所有正确的子语义模型**/
    public static List<SemanticModel> CorrectSubSemanticModels(SemanticModel sm,int SourceSMIndex,String SavePath,JSONObject jsonObject) throws Exception {

        //创建保存子语义模型的文件夹
        String SubSM_Graphviz = SavePath+"positive-models-graphviz/"+sm.getName();
        String SubSM_Json = SavePath+"positive-models-json/"+sm.getName();
        CreateFile(SubSM_Graphviz);
        CreateFile(SubSM_Json);

        List<SemanticModel> NewStartStatesSemanticModels = new LinkedList<SemanticModel>();

        //保存结果的列表
        List<List<String>> combine_results = new ArrayList<List<String>>();
        /**NoOrder**/
//        //保存输入的语义模型ColumnNodes的列表
//        List<String> arr = new ArrayList<String>();
//        //用于下面函数使用，记录每个组合的成员
//        List<String> temp = new ArrayList<String>();
//
//        //遍历SM中的所有ColumnNodes 将其Name存储到arr中
//        for(ColumnNode node: sm.getColumnNodes()){
//            arr.add(node.getColumnName());
//        }
//
//        String[] arrs = new String[arr.size()];
//        arr.toArray(arrs);
//
//        int num = sm.getColumnNodes().size()+1;//保存要划分得到的组合中元素最大个数
//        System.out.println("输出num:" + num);
//
//        System.out.println("输出arrs.length:" + arrs.length);
//        System.out.println("输出arr:" + arr);
//
//        //根据组合长度不同进行划分,遍历长度1-size,依次计算每个长度的组合有哪些
//        for(int i=2;i<num;i++){
//            combine(combine_results,arrs,0,i,temp);
//        }
//
//        Map<Integer,List<List<String>>> Num_CombineResults = new HashMap<Integer,List<List<String>>>();
//        if(num>=14){
//            //遍历每种长度下的combine_results 并将其保存到Map中
//            for(List<String> combine_list: combine_results){
//                List<List<String>> tmp = new ArrayList<List<String>>();
//                //计算每个combine_list的长度
//                if(!Num_CombineResults.keySet().contains(combine_list.size())){
//                    tmp.add(combine_list);
//                    Num_CombineResults.put(combine_list.size(),tmp);
//                }
//                else{
//                    tmp = Num_CombineResults.get(combine_list.size());
//                    tmp.add(combine_list);
//                    Num_CombineResults.put(combine_list.size(),tmp);
//                }
//            }
//            combine_results = new ArrayList<List<String>>();
//            for(Integer i: Num_CombineResults.keySet()){
//                System.out.println("输出i:" + i + "||" + Num_CombineResults.get(i).size());
//                //只随机获取每种长度下  不超过400个组合
////                List<List<String>> tmp = new ArrayList<List<String>>();
//                if(Num_CombineResults.get(i).size()>400) {
//                    Collections.shuffle(Num_CombineResults.get(i));
//                    combine_results.addAll(Num_CombineResults.get(i).subList(0, 400));
//                }
//                else{
//                    combine_results.addAll(Num_CombineResults.get(i));
//                }
//            }
//            System.out.println("输出num>=14的combine_results.size:" + combine_results.size());
//        }
        /**NoOrder**/

        /**WithOrder**/
        int AttributionOrderSize = 0;
        List<List<String>> AttributionOrder = new LinkedList<List<String>>();
        AttributionOrder = ReadAttributionOrder(Params.ROOT_DIR +"AttributionOrder.txt");
        /**cu-linux**/
//        AttributionOrderSize = AttributionOrder.size()-1;
//        System.out.println("输出AttributionOrder.get(SourceSMIndex):" + AttributionOrder.get(AttributionOrderSize-SourceSMIndex));
//        combine_results = CombineOrder(AttributionOrder.get(AttributionOrderSize-SourceSMIndex));
        /**cu-linux**/

        /**gpu-local**/
        System.out.println("输出AttributionOrder.get(SourceSMIndex):" + AttributionOrder.get(SourceSMIndex));
        combine_results = CombineOrder(AttributionOrder.get(SourceSMIndex));
        /**gpu-local**/

//        combine_results = CombineOrderOnce(AttributionOrder.get(SourceSMIndex));
        /**WithOrder**/

        //遍历得到的组合
        System.out.println("输出combine_results.size:" + combine_results.size());

        Set<String> RemoveListByList;
        List<Set<String>> DelList = new ArrayList<Set<String>>();
        for(List<String> combine_list: combine_results){
//            System.out.println("输出combine_list:" + combine_list);
            /**cu-linux**/
//            RemoveListByList = new HashSet<String>(AttributionOrder.get(AttributionOrderSize-SourceSMIndex));
            /**cu-linux**/

            /**gpu-local**/
            RemoveListByList = new HashSet<String>(AttributionOrder.get(SourceSMIndex));
            /**gpu-local**/

            RemoveListByList.removeAll(combine_list);
            DelList.add(RemoveListByList);
            System.out.println("输出CorrectSubSemanticModels中的combine_list:" + combine_list);
        }
        for(Set<String> delList: DelList){
            System.out.println("输出delList:" + delList);
        }
        System.out.println("输出DelList.size:" + DelList.size());

        int Index = 0;
        SemanticModel NewSource = null;//待删除的semantic model
        SemanticModel newsemanticmodel = null;
        for(Set<String> hashSet: DelList){
            Index++;
            System.out.println("ColumnNodes_hashSet:"+Index+"_"+hashSet);
            /**删除节点和边操作**/
            NewSource =  sm.clone();
            newsemanticmodel = NewEliminatedSemanticModelsForSubSM(NewSource,Index,hashSet,SubSM_Graphviz,SubSM_Json);
            NewStartStatesSemanticModels.add(newsemanticmodel);
        }
        System.out.println("输出NewStartStatesSemanticModels大小："+NewStartStatesSemanticModels.size());

        /**生成正确子语义模型的embeddings**/
        BigDecimal[] sm_embedding_array;//保存最终sm embedding
        BigDecimal[][] all_sm_embedding_array = new BigDecimal[NewStartStatesSemanticModels.size()][200];
        //遍历所有的sm
        int sm_index = 0;
        for(SemanticModel negativesm: NewStartStatesSemanticModels){
            /**保存Embeddings**/
            sm_embedding_array = SemanticModelEmbedding(jsonObject,negativesm);
            List<BigDecimal> sm_embedding_list = Arrays.asList(sm_embedding_array);
            System.out.println("输出sm_embedding_list:" + sm_embedding_list);
            System.out.println("输出sm_embedding_list.size:" + sm_embedding_list.size());
            all_sm_embedding_array[sm_index] = sm_embedding_array;//存储每个link对应的embedding
            ++sm_index;
            /**保存Embeddings**/
        }
        System.out.println("输出all_sm_embedding_array.size:" + all_sm_embedding_array.length);
        //存储all_sm_embedding_array到txt中
        save2dArray(all_sm_embedding_array,SubSM_Graphviz+"/correct_sm_embeddings.txt");
        /**生成正确子语义模型的embeddings**/

        return NewStartStatesSemanticModels;
    }
    public static void combine(List<List<String>> res, String[] arr, int start, int len, List<String> temp) {
        //如果没有剩余的长度了，即此时的temp中存放了足够的成员，即输出到结果集，需要注意的是要新new一个ArrayList，若只用一个的话，它的值会跟着后面改变而改变
        if(len==0) {
            List<String> t = new ArrayList<>();
            for(String a:temp) t.add(a);
            res.add(t);
            return;
        }
        //遍历完数组，退出
        if(start>=arr.length) return;
        //要当前值
        temp.add(arr[start]);
        combine(res, arr, start+1, len-1, temp);
        //不要当前值
        temp.remove(temp.size()-1);
        combine(res, arr, start+1, len, temp);
    }
    /**6.25 CombineOrder**/
    public static List<List<String>> CombineOrder(List<String> NeededCombine){
        List<List<String>> combine_results = new ArrayList<List<String>>();
        Map<Integer,List<List<String>>> Size_CombineResult = new HashMap<Integer,List<List<String>>>();
        List<List<String>> temp;
        System.out.println("输出NeededCombine:" + NeededCombine);
        for(int i=0;i<NeededCombine.size()-1;i++){
            for(int j=i+1;j<NeededCombine.size();j++){
                temp = new ArrayList<List<String>>();
                if(!Size_CombineResult.keySet().contains(NeededCombine.subList(i,j+1).size())){
                    temp.add(NeededCombine.subList(i,j+1));
                    Size_CombineResult.put(NeededCombine.subList(i,j+1).size(),temp);
                }
                else{
                    temp = Size_CombineResult.get(NeededCombine.subList(i,j+1).size());
                    temp.add(NeededCombine.subList(i,j+1));
                    Size_CombineResult.put(NeededCombine.subList(i,j+1).size(),temp);
                }
            }
        }
//        System.out.println("输出Size_CombineResult:" + Size_CombineResult);
        for(Integer i: Size_CombineResult.keySet()){
            combine_results.addAll(Size_CombineResult.get(i));
        }
        System.out.println("输出combine_results.size:" + combine_results.size());
        for(List<String> combine_result: combine_results) {
            System.out.println("输出combine_result:" + combine_result);
        }
        return combine_results;
    }
    /**6.25 CombineOrderOnce**/
    public static List<List<String>> CombineOrderOnce(List<String> NeededCombine){
        List<List<String>> combine_results = new ArrayList<List<String>>();
        System.out.println("输出NeededCombine:" + NeededCombine);
        for(int j=1;j<NeededCombine.size();j++){
            combine_results.add(NeededCombine.subList(0,j+1));
        }
        System.out.println("输出combine_results.size:" + combine_results.size());
//        System.out.println("输出combine_results:" + combine_results);
        return combine_results;
    }

    /**6.25 读取AttributionOrder.txt**/
    public static List<List<String>> ReadAttributionOrder(String filename) throws IOException {
        File myFile = new File(filename);//通过字符串创建File类型对象，指向该字符串路径下的文件

        List<List<String>> AttributionOrder = new LinkedList<List<String>>();
        if (myFile.isFile() && myFile.exists()) { //判断文件是否存在
            InputStreamReader Reader = new InputStreamReader(new FileInputStream(myFile), "UTF-8");
            //考虑到编码格式，new FileInputStream(myFile)文件字节输入流，以字节为单位对文件中的数据进行读取
            //new InputStreamReader(FileInputStream a, "编码类型")
            //将文件字节输入流转换为文件字符输入流并给定编码格式
            BufferedReader bufferedReader = new BufferedReader(Reader);
            //BufferedReader从字符输入流中读取文本，缓冲各个字符，从而实现字符、数组和行的高效读取。
            //通过BuffereReader包装实现高效读取
            String lineTxt = null;
            List<String> AttributionOrderPerSource;

            while ((lineTxt = bufferedReader.readLine()) != null) {
                //buffereReader.readLine()按行读取写成字符串
                AttributionOrderPerSource = new LinkedList<String>();
                System.out.println(lineTxt);
                if(StringUtils.isNotBlank(lineTxt)){
                    AttributionOrderPerSource = Arrays.asList(lineTxt.split(","));
                    AttributionOrder.add(AttributionOrderPerSource);
                }
            }
        }
        return AttributionOrder;
    }

    /**7.23  写string到指定文件**/
    public static void saveASFileWrite(String content){
        FileWriter fwrite = null;
        try{
            fwrite = new FileWriter(sm_embedding_joint_filePath);
            fwrite.write(content);
        } catch (IOException e) {
            e.printStackTrace();
        }finally {
            try{
                fwrite.flush();
                fwrite.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    /**7.23  调用cross-modal model计算得到最好的语义模型**/
    public static String NewGetScoreWithCrossModalModel(String source_emedding, String sm_embedding_joint_filePath){
        String predict_result = null;
        try{
            String[] args1 = new String[] {"python", "F:\\Cross-Modal Retrieval Model IN Linux\\Cross-Modal Retrieval Model Triple Loss\\my_predict_triple2.py", source_emedding, sm_embedding_joint_filePath};
            Process proc = Runtime.getRuntime().exec(args1);//执行py文件
            //用输入输出流来截取结果
            BufferedReader in = new BufferedReader(new InputStreamReader(proc.getInputStream()));
            String line = null;
//            while((line = in.readLine()) != null){
//                System.out.println("输出line:"+line);
//            }

            if((line = in.readLine()) != null){
                predict_result = line;
            }

            in.close();
            proc.waitFor();

        } catch (IOException e) {
            e.printStackTrace();
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
        return predict_result;
    }

    /**6.12 调用cross-modal model计算score**/
    public static String GetScoreWithCrossModalModel(String source_emedding, String sm_embedding){
        String predict_result = null;
        try{
            String[] args1 = new String[] {"python", "F:\\Cross-Modal Retrieval Model IN Linux\\Cross-Modal Retrieval Model Triple Loss\\my_predict_triple.py", source_emedding, sm_embedding};
            Process proc = Runtime.getRuntime().exec(args1);//执行py文件
            //用输入输出流来截取结果
            BufferedReader in = new BufferedReader(new InputStreamReader(proc.getInputStream()));
            String line = null;
//            while((line = in.readLine()) != null){
//                System.out.println("输出line:"+line);
//            }

            if((line = in.readLine()) != null){
                predict_result = line;
            }

            in.close();
            proc.waitFor();

        } catch (IOException e) {
            e.printStackTrace();
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
        return predict_result;
    }

    /**7.12 读取correct sub source embedding.txt文件**/
    public static List<String> ReadTxt (String pathname) throws IOException {
        List<String> Read_Content = new ArrayList<String>();
        File file = new File(pathname);
        FileInputStream readIn = new FileInputStream(file);
        InputStreamReader read = new InputStreamReader(readIn, "utf-8");
        BufferedReader bufferedReader = new BufferedReader(read);
        String oneLine = null;
        while ((oneLine = bufferedReader.readLine()) != null) {
            Read_Content.add(oneLine);
//            System.out.println("while online:"+oneLine);
        }
        read.close();
//        System.out.println("Read_Content:" + Read_Content);
        return Read_Content;
    }

    /**7.12 将String转换为BigDecimal类型的数组  这部分只用于测试**/
    public static BigDecimal[] String2BigDecimalArray(String embedding_string){
        BigDecimal[] embedding_bigdecimal_array = new BigDecimal[200];
        String[] embedding_string_array = embedding_string.split(",");
        for(int i=0;i<embedding_string_array.length;i++){
            embedding_bigdecimal_array[i] = new BigDecimal(embedding_string_array[i]);
        }
//        System.out.println("embedding_bigdecimal_array.size:" + embedding_bigdecimal_array.length);
        return embedding_bigdecimal_array;
    }
    /**7.12 将BigDecimal类型数组转为string**/
    public static String BigDecimalArray2String(BigDecimal[] embedding_bigdecimal_array){
        String embedding_string = null;
        String[] embedding_string_array = new String[200];
        for(int i=0;i<embedding_bigdecimal_array.length;i++){
            embedding_string_array[i] = embedding_bigdecimal_array[i].toString();
        }
//        System.out.println("BigDecimalArray2String中embedding_string_array:" + embedding_string_array);
        embedding_string = StringUtils.join(embedding_string_array, ",");
//        System.out.println("BigDecimalArray2String中embedding_string:" + embedding_string);
        return embedding_string;
    }

    /**7.22 将single_embedding_string转为embeddings_string**/
//    public static String StringJoint(String single_string){
//        String string_joint =
//    }

    public static void main(String[] args) throws Exception {
        /**5.16测试**/
//        /**获取Source Semantic Model**/
//        Node E22_Man_Made_Object1 = null, E12_Production1 = null, E54_Dimension1 = null, E55_Type1 = null, Dimentions = null, Medium = null;
//        if(SemanticModels == null) {
//            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-after-semanticLabeling", Params.MODEL_MAIN_FILE_EXT);
//        }
//        SemanticModel SourceSemanticModel = SemanticModels.get(0);
////        System.out.println(SourceSemanticModel.getColumnNodes().size());
//        List<ColumnNode> Columnnodes = new ArrayList<ColumnNode>();
//        Columnnodes = SourceSemanticModel.getColumnNodes();
////        System.out.println(Columnnodes.size());
//
//        /**去掉medium及其相应的links
//         * 先去掉links**/
////        for(DefaultLink link: SourceSemanticModel.getGraph().edgeSet()){
////            if(link.getSource().getId().equals("http://erlangen-crm.org/current/E12_Production1")&&link.getTarget().getId().equals("http://erlangen-crm.org/current/E55_Type1")){
////                SourceSemanticModel.getGraph().removeEdge(link.getSource(),link.getTarget());
////            }
////            if(link.getSource().getId().equals("http://erlangen-crm.org/current/E55_Type1")&&link.getTarget().getId().equals("HN1387")){
////                SourceSemanticModel.getGraph().removeEdge(link.getSource(),link.getTarget());
////            }
////        }
//        for(Node node:SourceSemanticModel.getGraph().vertexSet()){
//            if(node.getId().equals("http://erlangen-crm.org/current/E22_Man-Made_Object1")){
//                E22_Man_Made_Object1 = node;
//            }
//            if(node.getId().equals("http://erlangen-crm.org/current/E12_Production1")){
//                E12_Production1 = node;
//            }
//            if(node.getId().equals("http://erlangen-crm.org/current/E54_Dimension1")){
//                E54_Dimension1 = node;
//            }
//            if(node.getId().equals("http://erlangen-crm.org/current/E55_Type1")){
//                E55_Type1 = node;
//            }
//            if(node.getId().equals("HN1388")){//Dimentions
//                Dimentions = node;
//            }
//            if(node.getId().equals("HN1387")){//Dimentions
//                Medium = node;
//            }
//        }
//        //添加nodes
//        Node E33_Linguistic_Object1 = new InternalNode("http://erlangen-crm.org/current/E33_Linguistic_Object1",new Label("http://erlangen-crm.org/current/E33_Linguistic_Object"));
//        Node E57_Material1 = new InternalNode("http://erlangen-crm.org/current/E57_Material1",new Label("http://erlangen-crm.org/current/E57_Material"));
//        SourceSemanticModel.getGraph().addVertex(E33_Linguistic_Object1);
//        SourceSemanticModel.getGraph().addVertex(E57_Material1);
//        //添加links
//        //E33_Linguistic_Object1->P129_is_about->E22_Man-Made_Object1
//        String addedlinkId = LinkIdFactory.getLinkId("http://erlangen-crm.org/current/P129_is_about", "http://erlangen-crm.org/current/E33_Linguistic_Object1", "http://erlangen-crm.org/current/E22_Man-Made_Object1");
//        LabeledLink addedlink = new DataPropertyLink(addedlinkId, new Label("http://erlangen-crm.org/current/P129_is_about"));
//        SourceSemanticModel.getGraph().addEdge(E33_Linguistic_Object1,E22_Man_Made_Object1,addedlink);
//        //E33_Linguistic_Object1->defaultLink->E57_Material1
//        addedlinkId = LinkIdFactory.getLinkId("http://isi.edu/integration/karma/dev#defaultLink", "http://erlangen-crm.org/current/E33_Linguistic_Object1", "http://erlangen-crm.org/current/E57_Material1");
//        addedlink = new DataPropertyLink(addedlinkId, new Label("http://isi.edu/integration/karma/dev#defaultLink"));
//        SourceSemanticModel.getGraph().addEdge(E33_Linguistic_Object1,E57_Material1,addedlink);
//        //E57_Material1->label->Medium
//        addedlinkId = LinkIdFactory.getLinkId("http://www.w3.org/2000/01/rdf-schema#label", "http://erlangen-crm.org/current/E57_Material1", "HN1387");
//        addedlink = new DataPropertyLink(addedlinkId, new Label("http://www.w3.org/2000/01/rdf-schema#label"));
//        SourceSemanticModel.getGraph().addEdge(E57_Material1,Medium,addedlink);
//
//        //删除links和nodes
//        SourceSemanticModel.getGraph().removeEdge(E22_Man_Made_Object1,E54_Dimension1);
//        SourceSemanticModel.getGraph().removeEdge(E54_Dimension1,Dimentions);
//        SourceSemanticModel.getGraph().removeVertex(E54_Dimension1);
//        SourceSemanticModel.getGraph().removeVertex(Dimentions);
//
//        SourceSemanticModel.getGraph().removeEdge(E12_Production1,E55_Type1);
//        SourceSemanticModel.getGraph().removeEdge(E55_Type1,Medium);
//        SourceSemanticModel.getGraph().removeVertex(E55_Type1);
//
//        GraphVizUtil.exportSemanticModelToGraphviz(SourceSemanticModel, GraphVizLabelType.LocalId,
//                GraphVizLabelType.LocalUri, true, true, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\" + "test" + ".graph.json" + ".dot");
//
//        System.out.println("SourceSemanticModel的links"+SourceSemanticModel.getGraph().edgeSet().size());
//        System.out.println("SourceSemanticModel的nodes"+SourceSemanticModel.getGraph().vertexSet().size());
//
//        SemanticModel sm = SourceSemanticModel.clone();
//        System.out.println("sm的links"+sm.getGraph().edgeSet().size());
//        System.out.println("sm的nodes"+sm.getGraph().vertexSet().size());
//        for(Node node: sm.getGraph().vertexSet()){
//            if(node.getId().equals("http://erlangen-crm.org/current/E55_Type1")){
//                System.out.println("输出:"+node.getId());
//            }
//        }
//
//        /**获取integration graph**/
//        DirectedWeightedMultigraph<Node, DefaultLink> IntegrationGraph = null;//集成图
//        IntegrationGraph = getIntegrationGraph(0, new Integer[]{1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28});
//        TransitionFunction2(SourceSemanticModel,IntegrationGraph,Columnnodes);
        /**测试**/

//        TransitionFunction(0);
//        TransitionFunction1(0,4);////////5.14
//        GenNegativeExamples(10);////5.17
//        GenNegativeExamplesForEmbedding(0);////6.23
        /**6.25 读取AttributionOrder.txt**/
//        List<List<String>> AttributionOrder = new LinkedList<List<String>>();
//        AttributionOrder = ReadAttributionOrder("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\AttributionOrder.txt");
//        System.out.println("输出AttributionOrder.get(0):" + AttributionOrder.get(0));
//        CombineOrder(AttributionOrder.get(0));
        /**6.25 读取AttributionOrder.txt**/
        /**6.24 生成negative examples及其embeddings**/
//        JSONObject jsonObject = ReadEmbeddingJson(Params.ROOT_DIR +"final_embedding_correct.json");
//        GenNegativeExamplesPerFolderForEmbedding(6,jsonObject);///6.24
        /**6.24 生成negative examples及其embeddings**/
        PredictSemanticModels (28);//////7.12
//        SemanticModelEmbedding();/////6.17
        /**7.11 应用cross-modal model计算score**/
//        //获取correct sub source embedding
//        List<String> sub_source_embedding = new ArrayList<String>();
//        String source_embedding_pathname = "F:\\EmbdiForSourcesEmbeddings\\source20220314-embedding\\s01\\embeddings\\s01_Sub1-embedding.txt";
//        sub_source_embedding = ReadTxt(source_embedding_pathname);
//        System.out.println("sub_source_embedding:" + sub_source_embedding.get(0));
//        //获取semantic model embedding
//        List<String> correct_sm_embedding = new ArrayList<String>();
//        String correct_sm_embedding_pathname = "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\positive-models\\positive-models-graphviz\\s01.csv\\correct_sm_embeddings.txt";
////        String correct_sm_embedding_pathname = "F:\\GenerateExamples0630\\s01\\s01.csv.Sub1.State1\\sm_embeddings.txt";
//        correct_sm_embedding = ReadTxt(correct_sm_embedding_pathname);
//        System.out.println("correct_sm_embedding[0]:" + correct_sm_embedding.get(0));
//        //取出correct_sm_embedding.get(0)  即第一个sm_embedding(string)
//        BigDecimal[] embedding_bigdecimal_array = String2BigDecimalArray(correct_sm_embedding.get(0));
//        System.out.println("embedding_bigdecimal_array.size:" + embedding_bigdecimal_array.length);
//        String correct_sm_embedding_string = BigDecimalArray2String(embedding_bigdecimal_array);
//        System.out.println("correct_sm_embedding_string:" + correct_sm_embedding_string);
//
//        float score = 0;
//        score = Float.parseFloat(GetScoreWithCrossModalModel(sub_source_embedding.get(0), correct_sm_embedding_string));
//        System.out.println("score:" + score);
        /**7.11 应用cross-modal model计算score**/

        /**8.4 semi**/
//        if(SemanticModels == null) {
//            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles("E:\\semi-master\\evaluation\\taheriyan2016\\task_02\\semantic_models_gt\\json", ".model.json");
//        }
//        System.out.println("输出SemanticModels.size:" + SemanticModels.size());
//        for(SemanticModel sm: SemanticModels){
//            System.out.println("sm.node.size:" + sm.getGraph().vertexSet().size() + "||sm.link.size:" + sm.getGraph().edgeSet().size());
//            GraphVizUtil.exportSemanticModelToGraphviz(sm, GraphVizLabelType.LocalId,
//                GraphVizLabelType.LocalUri, true, true, "E:\\semi-master\\evaluation\\taheriyan2016\\task_02\\semantic_models_gt\\dot\\" + sm.getName() + ".dot");
//        }


        /**输入sm 输出sm_embedding**/
//        BigDecimal[][] sm_embedding_array = SaveSMEmbedding("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\models-json-SemanticLabeling-20220430","E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\semantic-model-embedding\\gold_sm_embeddings.txt");
        /**输入sm 输出sm_embedding**/

        /**给定正确的SemanticModel 为其生成衍生的正确的子SemanticModels**/
//        if(SemanticModels == null) {
//            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles("E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
//        }
//        //遍历语义模型
////        for(SemanticModel CorrectSMIn29: SemanticModels) {
//            CorrectSubSemanticModels(SemanticModels.get(27), "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\positive-models\\");
////        }
        /**给定正确的SemanticModel 为其生成衍生的正确的子SemanticModels**/

//        BeamSearch(0,9);
//        MergeIntoTree(0,0);
//        SearchForIntegrationGraph(0);
//        findAncestorNodes(0,"HN2033");
//        NodeIncomingOutgoing(0,"http://erlangen-crm.org/current/E12_Production1");
    }
}
