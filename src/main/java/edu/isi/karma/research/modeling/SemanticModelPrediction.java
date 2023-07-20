package edu.isi.karma.research.modeling;

import com.alibaba.fastjson.JSONObject;
import com.opencsv.CSVReader;
import com.opencsv.CSVReaderBuilder;
import edu.isi.karma.modeling.alignment.*;
import edu.isi.karma.modeling.alignment.learner.ModelLearningGraph;
import edu.isi.karma.modeling.alignment.learner.ModelLearningGraphType;
import edu.isi.karma.modeling.alignment.learner.ModelReader;
import edu.isi.karma.modeling.ontology.OntologyManager;
import edu.isi.karma.modeling.research.Params;
import edu.isi.karma.rep.alignment.*;
import edu.isi.karma.webserver.ContextParametersRegistry;
import edu.isi.karma.webserver.ServletContextParameterMap;
import org.hsqldb.Column;
import org.jgrapht.graph.DirectedWeightedMultigraph;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.*;

import static edu.isi.karma.research.modeling.EliminateNodes.getRegionSemanticModels;
import static edu.isi.karma.research.modeling.EliminateNodes.getSemanticModelRootList;
import static edu.isi.karma.research.modeling.FindPaths.findAllPathNode;
import static edu.isi.karma.research.modeling.GenerateNegativeSamples.*;
import static edu.isi.karma.research.modeling.GenerateTriples.getPartitionRegionTriplesStringForOneSemanticModel;
import static edu.isi.karma.research.modeling.ModelLearner_KnownModels4.getIntegrationGraphWithCandidateSemanticTypesForTraining;
import static edu.isi.karma.research.modeling.PartitionSamples.SortMap;
import static edu.isi.karma.research.modeling.PartitionSamples.getInternalNodeName;
import static edu.isi.karma.research.modeling.SearchForSemanticModels.CreateFile;
import static edu.isi.karma.research.modeling.SearchForSemanticModels.deleteFile;
import static edu.isi.karma.research.modeling.SortUtils.getSubDataSourceTxtName;

public class SemanticModelPrediction {
    private static String semanticModelsPath = Params.ROOT_DIR_2023;
    private static String partitionModelsPath = "D:/ASM/CRM/partition-models/";
    private static String regionDataSourceSavePath = "F:/SMCMR/";
    private static String predictedSemanticModelSavePath = "F:/SMCMR/predicted_semantic_model/";
    private static List<SemanticModel> semanticModels = null;
    private static List<SemanticModel> semanticModelsWithCandidateSemanticTypes = null;
    private static Map<String,Integer> attribute_index_dict = new HashMap<String,Integer>();
    private static String dataSourceName = null;
//    private static OntologyManager ontologyManager = null;
//    private static NodeIdFactory nodeIdFactory = null;

    private static List<Double> evaluateWithInverseForPredict(SemanticModel positiveSemanticModel,SemanticModel evaluatedSemanticModel) throws IOException {
        double f1_score = 0.0;
        List<Double> scores = new ArrayList<Double>();
        ModelEvaluation evaluateModel = evaluatedSemanticModel.newEvaluateForSpecifiedUri(positiveSemanticModel);
        if(evaluateModel.getPrecision()+evaluateModel.getRecall() == 0.0) {
            scores.add(evaluateModel.getPrecision());
            scores.add(evaluateModel.getRecall());
            scores.add(f1_score);
            return scores;
        }
        scores.add(evaluateModel.getPrecision());
        scores.add(evaluateModel.getRecall());
        f1_score = 2*(evaluateModel.getPrecision()*evaluateModel.getRecall())/(evaluateModel.getPrecision()+evaluateModel.getRecall());
        scores.add(f1_score);
        return scores;
    }

    private static void getInfoForInvokeInference(List<SemanticModel> semanticModels, String dataSetName) throws Exception {
        boolean notFlushFlag = false;
        String regionTriplesForOneSubSemanticModel;
        File candidate_semantic_models_txt_file = null;
        for(SemanticModel semantic_model: semanticModels){
            regionTriplesForOneSubSemanticModel = (String) getPartitionRegionTriplesStringForOneSemanticModel(semantic_model, partitionModelsPath, true, dataSetName).keySet().toArray()[0]; //obtain the region triples for one candidate semantic model ("head1,edge1,tail1;head2,edge2,tail2||head3,edge3,tail3;head4,edge4,tail4;head5,edge5,tail5")

            if(!notFlushFlag) {
                //create semantic_models.txt
                candidate_semantic_models_txt_file = new File(regionDataSourceSavePath + "semantic_model/semantic_models.txt");
                try{
                    FileWriter fileWriter = new FileWriter(candidate_semantic_models_txt_file);
                    //write regionTriplesForOneSubSemanticModel into .txt file
                    fileWriter.write(regionTriplesForOneSubSemanticModel);
                    fileWriter.write("\n");
                    fileWriter.close();
                } catch (Exception e) {
                    e.printStackTrace();
                }

                notFlushFlag = true;
            }
            else{
                try{
                    FileWriter fileWriter = new FileWriter(candidate_semantic_models_txt_file,true);
                    //write regionTriplesForOneSubSemanticModel into .txt file
                    fileWriter.write(regionTriplesForOneSubSemanticModel);
                    fileWriter.write("\n");
                    fileWriter.close();
                } catch (Exception e) {
                    e.printStackTrace();
                }
            }
        }
    }

    private static  SemanticModel transitionFunctionForPredict(SemanticModel searchSemanticModelState, DirectedWeightedMultigraph<Node, DefaultLink> Gint, List<ColumnNode> attributeNodes, Set<InternalNode> internalNodesWithUseOntPaths, String dataSetName) throws Exception {

        System.out.println("enter transitionFunctionForPredict");
        List<ColumnNode> columnNodesOfSearchSemanticModelState = new ArrayList<ColumnNode>();
        List<SemanticModel> semanticModelTrees = new ArrayList<SemanticModel>();
//        List<SemanticModel> nextSearchSemanticModelStates = new ArrayList<SemanticModel>();
        Set<ColumnNode> needAddedColumnNodes= new HashSet<ColumnNode>();
        Boolean hasOntPaths = false;
        String sub_data_source_emb_file = null;
        int best_sm_index = 0;
        List<SemanticModel> bestSemanticModels = new ArrayList<SemanticModel>();
        List<SemanticModel> candidateBestSemanticModels = new ArrayList<SemanticModel>();
        SemanticModel bestNextSemanticModel = null;

        if((internalNodesWithUseOntPaths != null) && (internalNodesWithUseOntPaths.size()>0))
            hasOntPaths = true;

        //obtain all attribute nodes(column nodes) of the search semantic model state
        columnNodesOfSearchSemanticModelState = searchSemanticModelState.getColumnNodes();
        //obtain all need added column nodes for the current search semantic model state
        for(ColumnNode node: attributeNodes){
            if(!columnNodesOfSearchSemanticModelState.contains(node)){
                needAddedColumnNodes.add(node);
            }
        }
        //return empty semantic models list if no added attribute node, else continue to invoke mergeIntoTree to add only one attribute node
        if(needAddedColumnNodes.size()>0) {
            for (ColumnNode added_column_node : needAddedColumnNodes) {
                //tree <- MergeIntoTree(St,Gint,ai)
                semanticModelTrees = mergeIntoTree(searchSemanticModelState, Gint, added_column_node, false,internalNodesWithUseOntPaths,hasOntPaths);//add a missing node to the current search semantic model

                if(semanticModelTrees.size() > 1) {
                    //get and save semantic models info and their corresponding data source txt file name
                    Map<String, Integer> columnNodesMap = new HashMap<String, Integer>();//save the column nodes info for obtaining the attributes name in order
                    for (ColumnNode columnNode : semanticModelTrees.get(0).getColumnNodes()) {
                        columnNodesMap.put(columnNode.getColumnName(), attribute_index_dict.get(columnNode.getColumnName()));//save the column nodes info
                    }
                    sub_data_source_emb_file = dataSourceName + "_" + "Sub" + (columnNodesOfSearchSemanticModelState.size() + 1) + "_" + getSubDataSourceTxtName(columnNodesMap) + ".emb";
                    System.out.println("sub_data_source_emb_file: " + sub_data_source_emb_file);
                    getInfoForInvokeInference(semanticModelTrees, dataSetName);
                    //invoke inference.py to select the best semantic model as the next search semantic model
                    best_sm_index = Integer.parseInt(getBestSemanticModelIndex("semantic_models.txt", dataSourceName + "/" + sub_data_source_emb_file, "info3.pt", "model24"));
                    System.out.println("best_sm_index: " + best_sm_index);
                    bestSemanticModels.add(semanticModelTrees.get(best_sm_index));
                }
                else if(semanticModelTrees.size() == 1){
                    candidateBestSemanticModels.addAll(semanticModelTrees);
                }
                else{
                    System.out.println("not candidate semantic models while adding " + added_column_node.getColumnName());
                }
//                //for st+1 <- trees do
//                if(semanticModelTrees.size()>0)
//                    nextSearchSemanticModelStates.addAll(semanticModelTrees);
            }

//            int index = 0;
//            for(SemanticModel next_search_semantic_model_state: nextSearchSemanticModelStates) {
//                index++;
//                GraphVizUtil.exportSemanticModelToGraphviz(next_search_semantic_model_state, GraphVizLabelType.LocalId,
//                        GraphVizLabelType.LocalUri, true, true, Params.ROOT_DIR +"next-search-states/" + Beam_Search + "_" + TransitionFunctionIndex + "_" + index + ".graph.json" + ".dot");
//            }
        }
        if(bestSemanticModels.size() > 0){
            Collections.shuffle(bestSemanticModels);
            bestNextSemanticModel = bestSemanticModels.get(0);
        }
        else{
            if(candidateBestSemanticModels.size() > 0){
                Collections.shuffle(candidateBestSemanticModels);
                bestNextSemanticModel = candidateBestSemanticModels.get(0);
            }
        }
        if(bestNextSemanticModel == null)
            System.out.println("invalid bestNextSemanticModel in transitionFunctionForPredict!");
        assert bestNextSemanticModel != null: "invalid bestNextSemanticModel";

        return bestNextSemanticModel;
    }

    private static SemanticModel beamSearchForPredict(SemanticModel positiveSemanticModel, List<SemanticModel> startSemanticModelState, DirectedWeightedMultigraph<Node, DefaultLink> integrationGraph, List<ColumnNode> completeColumnNodes, String Path, Set<InternalNode> internalNodesWithUseOntPaths, String dataSetName) throws Exception {
        /**test for generating correct semantic models while startSemanticModelState is not a list**/
//        List<SemanticModel> searchStates = new ArrayList<SemanticModel>();
//        List<SemanticModel> nextSemanticModelStates = new ArrayList<SemanticModel>();
//        List<SemanticModel> totalSemanticModelStates = new ArrayList<SemanticModel>();
//        List<SemanticModel> predictedSemanticModels = new ArrayList<SemanticModel>();
//        int addedAttributesNum = 0;
//        List<Double> similarityScores = new ArrayList<Double>();
//
//        System.out.println("beamSearch integration graph links size:" + integrationGraph.edgeSet().size());
//        System.out.println("beamSearch integration graph nodes size:" + integrationGraph.vertexSet().size());
//
//        /**if searchState is not empty**/
//        searchStates.add(startSemanticModelState);
//        assert searchStates.size() == 1: "initial number of search semantic model state is not 1";
//        /**obtain the num of attributes to be added for the start semantic model state**/
//        addedAttributesNum = completeColumnNodes.size() - startSemanticModelState.getColumnNodes().size();
//
//        // stop beam search if searchStates ia empty, else continue to obtain the complete semantic models
//        while(addedAttributesNum > 0){
//            double bestScore = 0.0;
//            System.out.println("addedAttributesNum: " + addedAttributesNum);
//            totalSemanticModelStates = new ArrayList<SemanticModel>();
//            //loop all search semantic model states in searchStates and invoke transitionFunction for generating next search semantic model states by adding one node
//            for(SemanticModel search_sm_state: searchStates) {
//                nextSemanticModelStates = transitionFunction(search_sm_state, integrationGraph, completeColumnNodes, internalNodesWithUseOntPaths);
//                if (nextSemanticModelStates.size() > 0)
//                    for (SemanticModel nextSearchState : nextSemanticModelStates) {
//                        /**comment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/
////                        if (evaluateWithInversePrecision(positiveSemanticModel, nextSearchState) == 1) {
////                            totalSemanticModelStates.add(nextSearchState);
////                        }
//                        /**comment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/
//
//                        /**uncomment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/
//                        double similarityScore = evaluateWithInverse(positiveSemanticModel,nextSearchState);
//                        if(similarityScore>bestScore) {
//                            totalSemanticModelStates = new ArrayList<SemanticModel>();
//                            bestScore = similarityScore;
//                            totalSemanticModelStates.add(nextSearchState);
//                        }
//                        /**uncomment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/
//                    }
//                System.out.println("totalSemanticModelStates.size in loop:" + totalSemanticModelStates.size());
//            }
//            /**uncomment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/
//            assert totalSemanticModelStates.size() == 1: "totalSemanticModelStates.size != 1";
//            /**uncomment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/
//            System.out.println("totalSemanticModelStates.size out of loop:" + totalSemanticModelStates.size());
//
//            /**if addedAttributesNum == 1 (that is the last beam search for generating final negative semantic models),
//             * we need to evaluate the score between the sm in totalSemanticModelStates and positive semantic model, and
//             * add the negative semantic models with score less than 1 into the selectedSemanticModels;
//             * else we need to add all negative semantic models in totalSemanticModelStates into the selectedSemanticModels.**/
//            if((addedAttributesNum>1) && (totalSemanticModelStates.size()>0)){
//                searchStates = new ArrayList<SemanticModel>();//complete once beam search by adding one attribute, and clear the searchStates
//                if(totalSemanticModelStates.size()>10) {
//                    searchStates.addAll(totalSemanticModelStates.subList(0,10));
//                }
//                else{
//                    searchStates.addAll(totalSemanticModelStates);
//                }
//            }
//            else if((addedAttributesNum == 1) && (totalSemanticModelStates.size()>0)){
//                //loop all predicted semantic models in totalSemanticModelStates and compute the score between them and the positive semantic model
//                for(SemanticModel predicted_semantic_model: totalSemanticModelStates){
//                    assert predicted_semantic_model.getColumnNodes().size() == positiveSemanticModel.getColumnNodes().size(): "predicted_semantic_model.columns.size != positiveSemanticModel.columns.size";
//                    double score = evaluateWithInverse(positiveSemanticModel,predicted_semantic_model);
//                    /**comment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/
////                    if(score==1) {
////                        predictedSemanticModels.add(predicted_semantic_model);//get all predicted semantic models with scores equals to 1
////                        similarityScores.add(score);
////                    }
//                    /**comment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/
//
//                    /**uncomment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/
//                    predictedSemanticModels.add(predicted_semantic_model);//get all predicted semantic models with scores equals to 1
//                    similarityScores.add(score);
//                    /**uncomment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/
//                }
//            }
//            addedAttributesNum--;
//        }
//        assert predictedSemanticModels.size() == similarityScores.size(): "predictedSemanticModels.size != similarityScores.size";
//        System.out.println("predictedSemanticModels size after beam search: "+predictedSemanticModels.size());
//        System.out.println("similarityScores.get(0): " + similarityScores.get(0));
//
//        return predictedSemanticModels;
        /**test for generating correct semantic models while startSemanticModelState is not a list**/

        /**predict the plausible semantic model for an input semantic model**/
        List<SemanticModel> searchStates = startSemanticModelState;
        List<SemanticModel> nextSemanticModelStates = new ArrayList<SemanticModel>();
//        List<SemanticModel> totalSemanticModelStates = new ArrayList<SemanticModel>();
//        List<SemanticModel> predictedSemanticModels = new ArrayList<SemanticModel>();
        SemanticModel nextCandidateSemanticModel = null;
        int addedAttributesNum = 0;
        double bestScore = 0.0;
        List<Double> bestScores = new ArrayList<Double>();
        SemanticModel bestPredictedSemanticModel = null;
        List<Double> calculateScores = new ArrayList<Double>();
        int best_sm_index_smcmr = 0;
        SemanticModel bestPredictedSemanticModelSMCMR = null;
        List<Double> calculateScoresSMCMR = new ArrayList<Double>();


        System.out.println("beamSearchForPredict integration graph links size:" + integrationGraph.edgeSet().size());
        System.out.println("beamSearchForPredict integration graph nodes size:" + integrationGraph.vertexSet().size());

        //if searchStates is not empty
        assert searchStates.size() == completeColumnNodes.size(): "initial number of search semantic model states is not equal to column nodes num in predicted semantic model";
        //obtain the num of attributes to be added for the start semantic model state
        addedAttributesNum = completeColumnNodes.size() - searchStates.get(0).getColumnNodes().size();

        //stop beam search if searchStates is empty, else continue to obtain the complete semantic models
        while(addedAttributesNum > 0){
            System.out.println("addedAttributesNum: " + addedAttributesNum);
            nextSemanticModelStates = new ArrayList<SemanticModel>();
            //loop all search semantic model states in searchStates and invoke transitionFunction for generating next search semantic model states by adding one node
            for(SemanticModel search_sm_state: searchStates){
//                //obtain the best next semantic model for each search_sm_state
//                if(search_sm_state == null) {
//                    System.out.println("search_sm_state wrong");
//                    continue;
//                }
                nextCandidateSemanticModel = transitionFunctionForPredict(search_sm_state, integrationGraph, completeColumnNodes, internalNodesWithUseOntPaths, dataSetName);
                if(nextCandidateSemanticModel != null)
                    nextSemanticModelStates.add(nextCandidateSemanticModel);
//                nextSemanticModelStates.add(transitionFunctionForPredict(search_sm_state, integrationGraph, completeColumnNodes, internalNodesWithUseOntPaths));
            }
            assert (nextSemanticModelStates.size() > 0) && (nextSemanticModelStates.size() <= positiveSemanticModel.getColumnNodes().size()): "invalid nextSemanticModelStates whose size is greater than attribute num or less than 1";
            if(addedAttributesNum>1){
                searchStates = new ArrayList<SemanticModel>(nextSemanticModelStates);//complete once beam search by adding one attribute, and clear the searchStates
            }
            else {
                //compute the best predicted score
                //get and save semantic models info and their corresponding data source txt file name
                String sub_data_source_emb_file = dataSourceName + "_" + "Sub" + positiveSemanticModel.getColumnNodes().size() + "_" + getSubDataSourceTxtName(attribute_index_dict) + ".emb";
                System.out.println("sub_data_source_emb_file: " + sub_data_source_emb_file);
                getInfoForInvokeInference(nextSemanticModelStates, dataSetName);
                //invoke inference.py to select the best semantic model as the next search semantic model
                best_sm_index_smcmr = Integer.parseInt(getBestSemanticModelIndex("semantic_models.txt", dataSourceName + "/" + sub_data_source_emb_file, "info3.pt", "model24"));
                System.out.println("best_sm_index_smcmr: " + best_sm_index_smcmr);
                bestPredictedSemanticModelSMCMR = nextSemanticModelStates.get(best_sm_index_smcmr);
                calculateScoresSMCMR = evaluateWithInverseForPredict(positiveSemanticModel,bestPredictedSemanticModelSMCMR);
                for(double best_score: calculateScoresSMCMR) {
                    System.out.println("best score smcmr: " + best_score);
                }

                //loop all predicted semantic models in nextSemanticModelStates and compute the score between them and the positive semantic model
                for(SemanticModel predicted_semantic_model: nextSemanticModelStates){
                    assert predicted_semantic_model.getColumnNodes().size() == positiveSemanticModel.getColumnNodes().size(): "predicted_semantic_model.columns.size != positiveSemanticModel.columns.size";
                    calculateScores = evaluateWithInverseForPredict(positiveSemanticModel,predicted_semantic_model);
                    if(calculateScores.get(2) > bestScore){
                        bestPredictedSemanticModel = predicted_semantic_model;
                        bestScore = calculateScores.get(2);
                        bestScores = calculateScores;
                    }
                }
            }
            addedAttributesNum--;
        }
        if(bestPredictedSemanticModel == null)
            System.out.println("invalid bestPredictedSemanticModel");
        assert bestPredictedSemanticModel != null: "invalid bestPredictedSemanticModel";

        for(double best_score: bestScores) {
            System.out.println("best score: " + best_score);
        }
        return bestPredictedSemanticModel;

        /**predict the plausible semantic model for an input semantic model**/

    }

    public static List<List<String>> getSubSetsWithOneAttribute(List<String> Columns) {
        List<List<String>> subSets = new ArrayList<List<String>>();
        if (Columns.size() == 0 || Columns == null) {
            return subSets;
        }

        for(String column: Columns){
            subSets.add(new ArrayList<String>(Arrays.asList(column)));
        }

        return subSets;
    }

    private static List<SemanticModel> getStartSearchStates(SemanticModel sm, String savePath) throws IOException {
        String SM_Graphviz_Path = savePath + "sub-positive-models-graphviz/" + sm.getName().replace(".csv","");
        String SM_Json_Path = savePath + "sub-positive-models-json/" + sm.getName().replace(".csv","");

        deleteFile(SM_Graphviz_Path);
        deleteFile(SM_Json_Path);

        CreateFile(SM_Graphviz_Path);
        CreateFile(SM_Json_Path);

        List<ColumnNode> columnNodes = sm.getColumnNodes();
        List<List<String>> subSets = new ArrayList<List<String>>();
        SemanticModel cloneSM = null;
        List<SemanticModel> startSemanticModels = new ArrayList<SemanticModel>();

        /**obtain all start attribute lists for generating all start semantic models**/
        for(ColumnNode columnNode: columnNodes){
            subSets.add(new ArrayList<String>(Arrays.asList(columnNode.getColumnName())));
        }
        System.out.println("subSets.size: " + subSets.size());

        int indexWithoutDel = 0;

        for(List<String> subset: subSets){
            assert subset.size() == 1: "invalid subset for generating one start semantic model";
            ++indexWithoutDel;
            for(DefaultLink link: sm.getGraph().edgeSet()){
                if((link.getTarget() instanceof ColumnNode) && (((ColumnNode) link.getTarget()).getColumnName().equals(subset.get(0)))){
                    List<DefaultLink> delDefaultLinks = new ArrayList<DefaultLink>(sm.getGraph().edgeSet());
                    System.out.println("delDefaultLinks before:" + delDefaultLinks.size());
                    delDefaultLinks.remove(link);
                    System.out.println("delDefaultLinks after:" + delDefaultLinks.size());
                    //obtain the sub semantic model with only one class node and attribute node
                    cloneSM = sm.clone();
                    //delete redundant nodes and links
                    List<Node> delInternalNodes = new ArrayList<Node>();
                    for(DefaultLink delLink: delDefaultLinks){
                        if((!delLink.getSource().equals(link.getSource())) && (!delInternalNodes.contains(delLink.getSource()))) {
                            delInternalNodes.add(delLink.getSource());
                            cloneSM.getGraph().removeVertex(delLink.getSource());
                        }
                        if((delLink.getTarget() instanceof ColumnNode) || ((!delLink.getTarget().equals(link.getSource())) && (!delInternalNodes.contains(delLink.getTarget())))){
                            delInternalNodes.add(delLink.getTarget());
                            cloneSM.getGraph().removeVertex(delLink.getTarget());
                        }
                        cloneSM.getGraph().removeEdge((LabeledLink) delLink);
                    }
                    assert cloneSM.getGraph().vertexSet().size() == 2: "semantic model doesn't have 2 nodes";
                    assert cloneSM.getGraph().edgeSet().size() == 1: "semantic model doesn't have 1 link";
                    startSemanticModels.add(cloneSM);
                }
            }
            assert cloneSM != null: "invalid start semantic model";
            cloneSM.setName(sm.getName().replace(".csv","") + "_Sub1_" + indexWithoutDel + ".csv");

            //save the start semantic models with only one attribute node
            cloneSM.writeJson(SM_Json_Path + "/" + cloneSM.getName().replace(".csv", "") + Params.MODEL_MAIN_FILE_EXT);
            GraphVizUtil.exportSemanticModelToGraphviz(cloneSM, GraphVizLabelType.LocalId,
                    GraphVizLabelType.LocalUri, true, true, SM_Graphviz_Path + "/" + cloneSM.getName().replace(".csv", "") + Params.GRAPHVIS_MAIN_FILE_EXT);
        }

        assert indexWithoutDel == columnNodes.size(): "columnNodes.size != indexWithoutDel";

        return startSemanticModels;
    }

    private static SemanticModel getSemanticModelWithDel(SemanticModel sm, ColumnNode columnNode, SemanticType semanticType) throws IOException {
        SemanticModel cloneSemanticModel = sm.clone();
        List<Node> delInternalNodes = new ArrayList<Node>();

//        ServletContextParameterMap contextParameters = ContextParametersRegistry.getInstance().getDefault();
//        OntologyManager ontologyManager = new OntologyManager(contextParameters.getId());
//        File oFile = new File(Params.ROOT_DIR + "ecrm_update(20190521).owl");
//
//        ontologyManager.doImport(oFile, "UTF-8");
//        ontologyManager.updateCache();
//
//        System.out.println("import ontology-objectproperties.size："+ontologyManager.getObjectProperties().size());
//        System.out.println("import ontology-dataproperties.size："+ontologyManager.getDataProperties().size());
//        GraphBuilder gb = ModelLearningGraph.getInstance(ontologyManager, ModelLearningGraphType.Compact).getGraphBuilder();
//        NodeIdFactory nodeIdFactory = gb.getNodeIdFactory();

        /**delete phase**/
        for(DefaultLink link: sm.getGraph().edgeSet()){
            cloneSemanticModel.getGraph().removeEdge((LabeledLink) link);
            if(!(delInternalNodes.contains(link.getSource()))){
                delInternalNodes.add(link.getSource());
                cloneSemanticModel.getGraph().removeVertex(link.getSource());
            }
            if((link.getTarget() instanceof InternalNode) && (!(delInternalNodes.contains(link.getTarget())))){
                delInternalNodes.add(link.getTarget());
                cloneSemanticModel.getGraph().removeVertex(link.getTarget());
            }
            else{
                if((link.getTarget() instanceof ColumnNode) && (!(((ColumnNode) link.getTarget()).getColumnName().equals(columnNode.getColumnName())))){
                    cloneSemanticModel.getGraph().removeVertex(link.getTarget());
                }
            }
        }
        assert (cloneSemanticModel.getGraph().vertexSet().size() == 1) && (cloneSemanticModel.getGraph().edgeSet().size() == 0): "semantic model in first step is invalid";

        /**add phase**/
        // add internal source node
//        String nodeId = nodeIdFactory.getNodeId(semanticType.getDomain().getUri());
        String nodeId = semanticType.getDomain().getUri() + "1";
        Node addInternalNode = new InternalNode(nodeId, new Label(semanticType.getDomain().getUri()));
        cloneSemanticModel.getGraph().addVertex(addInternalNode);
        // add link between internal source node and column node
        String linkId = LinkIdFactory.getLinkId(semanticType.getType().getUri(),addInternalNode.getId(),columnNode.getId());
        LabeledLink addLink = new DataPropertyLink(linkId, new Label(semanticType.getType().getUri()));
        cloneSemanticModel.getGraph().addEdge(addInternalNode, columnNode, addLink);

        assert cloneSemanticModel.getGraph().vertexSet().size() == 2: "semantic model doesn't have 2 nodes";
        assert cloneSemanticModel.getGraph().edgeSet().size() == 1: "semantic model doesn't have 1 link";

        return cloneSemanticModel;
    }

    private static String getBestSemanticModelIndex(String regionTriplesFile, String dataSourceFile, String infoName, String modelName){
        String predictIndex = null;
        try{
            String[] args = new String[]{"python", "F:/SMCMR/inference.py", regionTriplesFile, dataSourceFile, infoName, modelName};
            Process proc = Runtime.getRuntime().exec(args);
            BufferedReader in = new BufferedReader(new InputStreamReader(proc.getInputStream()));
            String line = null;

//            while((line = in.readLine()) != null){
//                System.out.println("输出line: " + line);
//            }

            if((line = in.readLine()) != null){
                predictIndex = line;
            }

            in.close();
            proc.waitFor();
        } catch (IOException e) {
            e.printStackTrace();
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
        return predictIndex;
    }

    private static List<SemanticModel> getStartSearchStatesWithCandidateTypes(SemanticModel sm, String savePath, String dataSetName) throws Exception {
        List<SemanticModel> startSemanticModels = new ArrayList<SemanticModel>();
        List<ColumnNode> columnNodes = sm.getColumnNodes();
        SemanticModel cloneSemanticModel = null;
        Boolean notFlushFlag = null;
//        Map<String,Set<String>> regionTriplesInfo = new HashMap<String,Set<String>>();
        String regionTriplesForOneSubSemanticModel;
        File candidate_semantic_models_txt_file = null;
        String sub_data_source_emb_file = null;
        int best_sm_index = 0;
        List<SemanticModel> startCandidateSemanticModels = new ArrayList<SemanticModel>();

        // obtain all candidate start semantic models with semantic types
        for(ColumnNode columnNode: columnNodes){
            //obtain all candidate semantic types containing correct and incorrect types
            Set<SemanticType> candidateSemanticTypes = getSemanticTypes(columnNode,true,true,4);
            if(candidateSemanticTypes.size() == 1){
                cloneSemanticModel = getSemanticModelWithDel(sm, columnNode, new ArrayList<SemanticType>(candidateSemanticTypes).get(0));
                startSemanticModels.add(cloneSemanticModel);
            }
            else{
                notFlushFlag = false;
                List<SemanticModel> candidateStartSemanticModels = new ArrayList<SemanticModel>();
                Map<String,Integer> columnNodesMap = new HashMap<String,Integer>();//save the column nodes info for obtaining the attributes name in order
                columnNodesMap.put(columnNode.getColumnName(),attribute_index_dict.get(columnNode.getColumnName()));//save the column nodes info
                
                sub_data_source_emb_file = dataSourceName + "_" + "Sub1_" + getSubDataSourceTxtName(columnNodesMap) + ".emb";
                System.out.println("StartSearchStates sub_data_source_emb_file: " + sub_data_source_emb_file);

                for(SemanticType semanticType: candidateSemanticTypes){
                    cloneSemanticModel = getSemanticModelWithDel(sm, columnNode, semanticType);
                    /**obtain region triples for one candidate semantic model**/
                    regionTriplesForOneSubSemanticModel = (String) getPartitionRegionTriplesStringForOneSemanticModel(cloneSemanticModel, partitionModelsPath, true, dataSetName).keySet().toArray()[0]; //obtain the region triples for one candidate semantic model ("head1,edge1,tail1;head2,edge2,tail2||head3,edge3,tail3;head4,edge4,tail4;head5,edge5,tail5")

                    if(!notFlushFlag) {
                        //create semantic_models.txt
                        candidate_semantic_models_txt_file = new File(regionDataSourceSavePath + "semantic_model/semantic_models.txt");
                        try{
                            FileWriter fileWriter = new FileWriter(candidate_semantic_models_txt_file);
                            //write regionTriplesForOneSubSemanticModel into .txt file
                            fileWriter.write(regionTriplesForOneSubSemanticModel);
                            fileWriter.write("\n");
                            fileWriter.close();
                        } catch (Exception e) {
                            e.printStackTrace();
                        }

                        notFlushFlag = true;
                    }
                    else{
                        try{
                            FileWriter fileWriter = new FileWriter(candidate_semantic_models_txt_file,true);
                            //write regionTriplesForOneSubSemanticModel into .txt file
                            fileWriter.write(regionTriplesForOneSubSemanticModel);
                            fileWriter.write("\n");
                            fileWriter.close();
                        } catch (Exception e) {
                            e.printStackTrace();
                        }
                    }

                    candidateStartSemanticModels.add(cloneSemanticModel);
                    System.out.println("cloneSemanticModel.name: " + cloneSemanticModel.getName());
                }
                assert candidateStartSemanticModels.size() == candidateSemanticTypes.size(): "invalid candidateStartSemanticModels";
                //invoke model to select the best start semantic model
                best_sm_index = Integer.parseInt(getBestSemanticModelIndex("semantic_models.txt", dataSourceName + "/" + sub_data_source_emb_file, "info3.pt", "model24"));
                System.out.println("best_sm_index: " + best_sm_index);
                startCandidateSemanticModels.add(candidateStartSemanticModels.get(best_sm_index));
            }

            System.out.println("candidateSemanticTypes.size: " + candidateSemanticTypes.size());

        }
        assert startSemanticModels.size() + startCandidateSemanticModels.size() == columnNodes.size(): "invalid startSemanticModels and startCandidateSemanticModels";
        if(startSemanticModels.size() + startCandidateSemanticModels.size() <= 10)
            startSemanticModels.addAll(startCandidateSemanticModels);
        else
            startSemanticModels.addAll(startCandidateSemanticModels.subList(0,10-startSemanticModels.size()));
        assert startSemanticModels.size() <= 10: "invalid startSemanticModels";
        return startSemanticModels;
    }

    public static SemanticModel getPredictedSemanticModels(int predictSourceIndex, SemanticModel predictSemanticModel, DirectedWeightedMultigraph<Node, DefaultLink> integrationGraph, Set<InternalNode> internalNodesWithUseOntPaths, String dataSetName) throws Exception{
//        List<SemanticModel> predictedSemanticModels = new ArrayList<SemanticModel>();
        SemanticModel bestPredictedSemanticModel = null;

        String predictedSemanticModelGraphvizFilePath = semanticModelsPath + "predicted-models/predicted-models-graphviz";
        String predictedSemanticModelJsonFilePath = semanticModelsPath + "predicted-models/predicted-models-json";

        CreateFile(predictedSemanticModelGraphvizFilePath);
        CreateFile(predictedSemanticModelJsonFilePath);

        // judge whether the integration graph contains all column nodes in predictSemanticModel
        assert integrationGraph.vertexSet().contains(predictSemanticModel.getColumnNodes()): "some column nodes of predict semantic model are not in the integration graph";

        List<SemanticModel> startSemanticModels = new ArrayList<SemanticModel>();
//        startSemanticModels = getStartSearchStates(predictSemanticModel, semanticModelsPath + "positive-models/");
        startSemanticModels = getStartSearchStatesWithCandidateTypes(predictSemanticModel, semanticModelsPath + "positive-models/", dataSetName);
//        System.out.println(predictSemanticModel.getName() + " start semantic models size:" + startSemanticModels.size());

//        int index = 0;
//        for(SemanticModel startSemanticModel: startSemanticModels) {
//            if (++index > 1)
//                break;
//            predictedSemanticModels = beamSearchForPredict(predictSemanticModel, startSemanticModel, integrationGraph, predictSemanticModel.getColumnNodes(),"", internalNodesWithUseOntPaths);
//
//            if(predictedSemanticModels.size() > 0){
//                SemanticModel resultSemanticModel = predictedSemanticModels.get(0);
//            }
//            else{
//                System.out.println("cannot predict correct semantic model");
//            }
//        }
        bestPredictedSemanticModel = beamSearchForPredict(predictSemanticModel, startSemanticModels, integrationGraph, predictSemanticModel.getColumnNodes(),"", internalNodesWithUseOntPaths, dataSetName);
        return bestPredictedSemanticModel;
    }

    public static void main(String[] args) throws Exception {

        String dataSetName = "CRM";
        SemanticModel bestPredictedSemanticModel = null;

        List<SemanticModel> trainSemanticModels = new ArrayList<SemanticModel>();
        SemanticModel predictSemanticModel = null;

        DirectedWeightedMultigraph<Node, DefaultLink> integrationGraph = null;

        // obtain semantic models without semanticTyper and with semanticTyper
        if(semanticModels == null)
            semanticModels = ModelReader.importSemanticModelsFromJsonFiles(semanticModelsPath + "models-json-20230313", Params.MODEL_MAIN_FILE_EXT);
        if(semanticModelsWithCandidateSemanticTypes == null)
            semanticModelsWithCandidateSemanticTypes = ModelReader.importSemanticModelsFromJsonFiles(semanticModelsPath + "labeled-models-json-20230402", Params.MODEL_MAIN_FILE_EXT);

        for(int j=0; j<29; j++){
            if(j<23)
                continue;
            else if(j>23)
                break;

            if(j<9)
                dataSourceName = "s0" + (j+1);
            else
                dataSourceName = "s" + (j+1);

            predictSemanticModel = semanticModelsWithCandidateSemanticTypes.get(j);

            // get train semantic models index array
            trainSemanticModels = new ArrayList<SemanticModel>(semanticModels);
            trainSemanticModels.remove(j);

            integrationGraph = getIntegrationGraphWithCandidateSemanticTypesForTraining(predictSemanticModel, trainSemanticModels);

            //obtain the source nodes set and target nodes set for any node in the integration graph
            Set<InternalNode> internalNodesWithUseOntPaths = new HashSet<InternalNode>();
            for(DefaultLink integrationLink: integrationGraph.edgeSet()){
                integrationLink.getSource().addTargetNode(integrationLink.getTarget());
                integrationLink.getTarget().addSourceNode(integrationLink.getSource());

                //test for the internal nodes with useOntPaths = true
                if(((InternalNode) integrationLink.getSource()).getUseOntPaths()){
                    internalNodesWithUseOntPaths.add((InternalNode) integrationLink.getSource());
                }
                //test for the internal nodes with useOntPaths = true and the column nodes with useOntInternalNodes = true
                if((integrationLink.getTarget() instanceof InternalNode) && (((InternalNode) integrationLink.getTarget()).getUseOntPaths())){
                    internalNodesWithUseOntPaths.add((InternalNode) integrationLink.getTarget());
                }
            }

            System.out.println("internalNodesWithUseOntPaths:" + internalNodesWithUseOntPaths.size());

            System.out.println(predictSemanticModel.getName() + " integrationGraph links size:" + integrationGraph.edgeSet().size());
            System.out.println(predictSemanticModel.getName() + " integrationGraph nodes size:" + integrationGraph.vertexSet().size());

            /**read attributes in order from the original data source**/
            InputStreamReader reader = new InputStreamReader(new FileInputStream("D:/ASM/CRM/sources20230313/"+dataSourceName+".csv"), StandardCharsets.UTF_8);
//            InputStreamReader reader = new InputStreamReader(new FileInputStream("D:/ASM/CRM/sources20230313/"+dataSourceName+".csv"), StandardCharsets.UTF_8);

            CSVReader csvReader = new CSVReaderBuilder(reader).build();
            List<String[]> list = csvReader.readAll();
            String[] attributes = list.get(0);
            System.out.println("attributes:" + attributes);
            attribute_index_dict = new HashMap<String,Integer>();
            int attribute_index = 0;
            for(String attribute: attributes){
                System.out.println("attribute:" + attribute);
                attribute_index_dict.put(attribute,attribute_index++);
            }

            /**obtain all negative semantic models using original method (test for predicting correct semantic models)**/
            long start = System.currentTimeMillis();
            bestPredictedSemanticModel = getPredictedSemanticModels(j, predictSemanticModel, integrationGraph, internalNodesWithUseOntPaths, dataSetName);
            long elapsedTimeMillis = System.currentTimeMillis() - start;
            float elapsedTimeSec = elapsedTimeMillis/1000F;
            System.out.println("Predicted time: " + elapsedTimeSec);

            GraphVizUtil.exportSemanticModelToGraphviz(bestPredictedSemanticModel, GraphVizLabelType.LocalId,
                    GraphVizLabelType.LocalUri, true, true, predictedSemanticModelSavePath + dataSourceName + ".dot");

        }

    }
}
