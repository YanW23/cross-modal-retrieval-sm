package edu.isi.karma.research.modeling;

import com.alibaba.fastjson.JSONObject;
import com.google.common.collect.Sets;
import com.hp.hpl.jena.ontology.OntModel;
import com.hp.hpl.jena.ontology.OntModelSpec;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import com.hp.hpl.jena.tdb.store.Hash;
import edu.isi.karma.modeling.ModelingParams;
import edu.isi.karma.modeling.alignment.*;
import edu.isi.karma.modeling.alignment.learner.*;
import edu.isi.karma.modeling.ontology.OntologyManager;
import edu.isi.karma.modeling.research.Params;
import edu.isi.karma.modeling.steiner.topk.LabeledEdge;
import edu.isi.karma.rep.alignment.*;
import edu.isi.karma.util.RandomGUID;
import edu.isi.karma.webserver.ContextParametersRegistry;
import edu.isi.karma.webserver.ServletContextParameterMap;
import org.apache.commons.collections.CollectionUtils;
import org.apache.poi.ss.formula.functions.T;
import org.jgrapht.graph.DirectedWeightedMultigraph;
import org.mortbay.xml.XmlParser;
import org.python.antlr.op.In;
import org.python.google.common.collect.Lists;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.math.BigDecimal;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static edu.isi.karma.modeling.alignment.learner.ModelReader.importSemanticModelFromJsonFile;
import static edu.isi.karma.research.modeling.EliminateNodes.getNewStartStatesSemanticModelForEmbedding;
import static edu.isi.karma.research.modeling.EliminateNodes.getSubSemanticModels;
import static edu.isi.karma.research.modeling.FindPaths.*;
import static edu.isi.karma.research.modeling.FindPaths.connectedPathsLink;
import static edu.isi.karma.research.modeling.GenerateSamples.getAllPositiveSemanticModels;
import static edu.isi.karma.research.modeling.GenerateSamples.getSubSets;
import static edu.isi.karma.research.modeling.ModelLearner_KnownModels4.*;
import static edu.isi.karma.research.modeling.PartitionSamples.getLabelName;
import static edu.isi.karma.research.modeling.SearchForSemanticModels.*;

public class GenerateNegativeSamples {
    private static List<SemanticModel> semanticModels = null;
    private static List<SemanticModel> semanticModelsWithCandidateSemanticTypes = null;

    private static OntologyManager ontologyManager = null;
    private static OntModel ontModel = ModelFactory.createOntologyModel(OntModelSpec.OWL_MEM);

    private static int beamSearchNum = 0;
    private static int transitionFunctionNum = 0;

    private static int negativeSemanticModelForTrainIndexForOnePositiveSemanticModel = 0;

    public static void setOntologyManagerAndOntModel() throws IOException {
        ontologyManager = new OntologyManager((ContextParametersRegistry.getInstance().getDefault()).getId());
        File oFile = new File(Params.ROOT_DIR+"ecrm_update(20190521).owl");
        ontologyManager.doImport(oFile, "UTF-8");
        ontologyManager.updateCache();
        ontModel.read("file:E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\ecrm_update(20190521).owl");
    }

    public static ModelLearningGraph getIntegrationGraphForEmbedding(ModelLearningGraph modelLearningGraphForEmbedding, List<LabeledLink> labeledLinks, List<CompactLink> compactLinks, PatternWeightSystem weightSystem, SemanticModel model) throws Exception {

        System.out.println("modelLearningGraphForEmbedding links size:" + modelLearningGraphForEmbedding.getGraphBuilder().getGraph().edgeSet().size());
        System.out.println("modelLearningGraphForEmbedding nodes size:" + modelLearningGraphForEmbedding.getGraphBuilder().getGraph().vertexSet().size());


        String modelId = model.getId();

        if(labeledLinks.size()>0) {
            for (LabeledLink e : labeledLinks) {
                String id = LinkIdFactory.getLinkId(e.getUri(), e.getSource().getId(), e.getTarget().getId());
                LabeledLink l = modelLearningGraphForEmbedding.getGraphBuilder().getIdToLinkMap().get(id);

                if (l != null) {
                    int numOfPatterns = l.getModelIds().size();
                    if (weightSystem == PatternWeightSystem.OriginalWeights) {
                        double currentW = l.getWeight();
                        double newW = model.getGraph().getEdgeWeight((LabeledLink) e);
                        if (newW < currentW)
                            modelLearningGraphForEmbedding.getGraphBuilder().changeLinkWeight(l, newW);
                    } else if (weightSystem == PatternWeightSystem.JWSPaperFormula) {
                        if (e.getTarget() instanceof InternalNode) {
                            // wl - x/(n+1)
                            // wl = 1
                            // x = (numOfPatterns + 1)
                            // n = totalNumberOfPatterns
                            modelLearningGraphForEmbedding.getGraphBuilder().changeLinkWeight(l, ModelingParams.PATTERN_LINK_WEIGHT -
                                    ((double) (numOfPatterns + 1) / (double) (29 + 1)));
//						this.graphBuilder.changeLinkWeight(l, ModelingParams.PATTERN_LINK_WEIGHT - (0.00001 * numOfPatterns) );
                        } else {
                            modelLearningGraphForEmbedding.getGraphBuilder().changeLinkWeight(l, ModelingParams.PATTERN_LINK_WEIGHT);
                        }
                    } else {
                        modelLearningGraphForEmbedding.getGraphBuilder().changeLinkWeight(l, ModelingParams.PATTERN_LINK_WEIGHT);
                    }
                    l.getModelIds().add(modelId);
                    e.getSource().getModelIds().add(modelId);
                    e.getTarget().getModelIds().add(modelId);
                } else {
                    LabeledLink link = e.copy(id);

                    if (link != null) {
                        link.setStatus(LinkStatus.Normal); // all the links in learning graph are normal

                        if (link.getModelIds() != null)
                            link.getModelIds().clear();
                        link.getModelIds().add(modelId);

                        if (weightSystem == PatternWeightSystem.OriginalWeights) {
                            modelLearningGraphForEmbedding.getGraphBuilder().addLink(e.getSource(), e.getTarget(), link, model.getGraph().getEdgeWeight(e));
                        } else {
                            modelLearningGraphForEmbedding.getGraphBuilder().addLink(e.getSource(), e.getTarget(), link, ModelingParams.PATTERN_LINK_WEIGHT);
                        }

                        e.getSource().getModelIds().add(modelId);
                        e.getTarget().getModelIds().add(modelId);
                    }

                }
            }
        }

        if(compactLinks.size()>0){
            modelLearningGraphForEmbedding.getGraphBuilder().updateLinksForIntegration(compactLinks);
        }

        return modelLearningGraphForEmbedding;
    }

    public static Set<SemanticType> getSemanticTypes(ColumnNode steinerNode, boolean useCorrectTypes, boolean useCandidateTypes, int numberOfCandidates) {

        if (steinerNode == null)
            return null;

        Set<SemanticType> semanticTypes = new HashSet<SemanticType>();
        Set<String> semanticTypesString = new HashSet<String>();

        List<SemanticType> candidateSemanticTypes = null;

        //only obtain the correct semantic types
        if(useCorrectTypes && (!useCandidateTypes)){
            candidateSemanticTypes = steinerNode.getUserSemanticTypes();
            if(candidateSemanticTypes != null) {
                for(SemanticType correct_semantic_type: candidateSemanticTypes) {
                    if(semanticTypesString.contains(correct_semantic_type.getDomain().toString()+correct_semantic_type.getType().toString())){
                        continue;
                    }
                    semanticTypesString.add(correct_semantic_type.getDomain().toString()+correct_semantic_type.getType().toString());
                    semanticTypes.add(correct_semantic_type);
                }
            }
        }
        //only obtain the candidate semantic types
        else if((!useCorrectTypes) && useCandidateTypes){
            candidateSemanticTypes = steinerNode.getTopKLearnedSemanticTypes(numberOfCandidates);
            if(candidateSemanticTypes != null) {
                for(SemanticType candidate_semantic_type: candidateSemanticTypes) {
                    if(semanticTypesString.contains(candidate_semantic_type.getDomain().toString()+candidate_semantic_type.getType().toString())){
                        continue;
                    }
                    semanticTypesString.add(candidate_semantic_type.getDomain().toString()+candidate_semantic_type.getType().toString());
                    semanticTypes.add(candidate_semantic_type);
                }
            }
        }
        //obtain the correct and candidate semantic types
        else if(useCorrectTypes && useCandidateTypes){
            candidateSemanticTypes = steinerNode.getUserSemanticTypes();
            if(candidateSemanticTypes != null) {
                for(SemanticType correct_semantic_type: candidateSemanticTypes) {
                    if(semanticTypesString.contains(correct_semantic_type.getDomain().toString()+correct_semantic_type.getType().toString())){
                        continue;
                    }
                    semanticTypesString.add(correct_semantic_type.getDomain().toString()+correct_semantic_type.getType().toString());
                    semanticTypes.add(correct_semantic_type);
                }
            }
            candidateSemanticTypes = steinerNode.getTopKLearnedSemanticTypes(numberOfCandidates);
            if(candidateSemanticTypes != null) {
                for(SemanticType candidate_semantic_type: candidateSemanticTypes) {
                    if(semanticTypesString.contains(candidate_semantic_type.getDomain().toString()+candidate_semantic_type.getType().toString())){
                        continue;
                    }
                    semanticTypesString.add(candidate_semantic_type.getDomain().toString()+candidate_semantic_type.getType().toString());
                    semanticTypes.add(candidate_semantic_type);
                }
            }
        }
        else{
            return null;
        }

        return semanticTypes;
    }

    private static <T> List<List<T>> descartesRecursiveForDoubleList(List<List<List<T>>> originalList){
        List<List<List<T>>> data = new ArrayList<>();
        List<List<T>> result = new ArrayList<>();
        for (List<List<T>> list : originalList) {
            List<List<List<T>>> temp = new ArrayList<>();
            if(CollectionUtils.isEmpty(data)){
                for(List<T> t : list){
                    temp.add(Stream.of(t).collect(Collectors.toList()));
                }
                data = temp;
                continue;
            }
            for(List<T> t : list){
                for (List<List<T>> re : data) {
                    temp.add(Stream.concat(re.stream(), Stream.of(t)).collect(Collectors.toList()));
                }
            }
            data = temp;
        }
        for(List<List<T>> elem: data){
            List<T> temp_elem = new ArrayList<>();
            for(List<T> elem1: elem){
                temp_elem.addAll(elem1);
            }
            result.add(temp_elem);
        }
//        System.out.println("data:" + data.size());
//        System.out.println("result:" + result);

        return result;
    }

    private static <T> List<List<T>> descartesRecursiveUnique(List<List<T>> originalList) {
        List<List<T>> data = new ArrayList<>();
        for (List<T> list : originalList) {
            List<List<T>> temp = new ArrayList<>();
            if(CollectionUtils.isEmpty(data)){
                for(T t : list){
                    temp.add(Stream.of(t).collect(Collectors.toList()));
                }
                data = temp;
                continue;
            }
            for(T t : list){
                for (List<T> re : data) {
                    if(re.contains(t))
                        continue;
                    temp.add(Stream.concat(re.stream(), Stream.of(t)).collect(Collectors.toList()));
                }
            }
            data = temp;
        }
        return data;
    }

    private static <T> List<List<T>> descartesRecursive(List<List<T>> originalList) {
        List<List<T>> data = new ArrayList<>();
        for (List<T> list : originalList) {
            List<List<T>> temp = new ArrayList<>();
            if(CollectionUtils.isEmpty(data)){
                for(T t : list){
                    temp.add(Stream.of(t).collect(Collectors.toList()));
                }
                data = temp;
                continue;
            }
            for(T t : list){
                for (List<T> re : data) {
                    temp.add(Stream.concat(re.stream(), Stream.of(t)).collect(Collectors.toList()));
                }
            }
            data = temp;
        }
        return data;
    }

    public static Set<Node> getCommonAncestorNodes(Node node1, Node node2, int depth, Boolean hasOntPaths){
        assert node1 instanceof InternalNode: "node1 is not the internal node";
        assert node2 instanceof InternalNode: "node2 is not the internal node";

        int loopNum = 1;
        Set<Node> commonAncestorNodes = new HashSet<Node>();
        Set<Node> ancestorNodesForNode1 = new HashSet<Node>();
        Set<Node> ancestorNodesForNode2 = new HashSet<Node>();

        Set<Node> tempAncestorNodesForNode1 = new HashSet<Node>();
        Set<Node> tempAncestorNodesForNode2 = new HashSet<Node>();

        while(loopNum<=depth){
            if((ancestorNodesForNode1.size()==0) && (ancestorNodesForNode2.size()==0)){
                ancestorNodesForNode1.addAll(node1.getSourceNodes());
                ancestorNodesForNode2.addAll(node2.getSourceNodes());
            }
            else{
//                assert AncestorNodesForNode1.size() > 0: "AncestorNodesForNode1.size <= 0";
//                assert AncestorNodesForNode2.size() > 0: "AncestorNodesForNode2.size <= 0";
                for(Node sourceNode1: ancestorNodesForNode1){
                    tempAncestorNodesForNode1.addAll(sourceNode1.getSourceNodes());
                }
                for(Node sourceNode2: ancestorNodesForNode2){
                    tempAncestorNodesForNode2.addAll(sourceNode2.getSourceNodes());
                }
                ancestorNodesForNode1.addAll(tempAncestorNodesForNode1);
                ancestorNodesForNode2.addAll(tempAncestorNodesForNode2);
            }

//            System.out.println(loopNum + " 层source nodes");
            ++loopNum;
        }

        if((ancestorNodesForNode1.size()!=0) && (ancestorNodesForNode2.size()!=0)){
            commonAncestorNodes.addAll(ancestorNodesForNode1);
            commonAncestorNodes.retainAll(ancestorNodesForNode2);
        }

        if(hasOntPaths){
            Set<Node> newCommonAncestorNodes = new HashSet<Node>();
            for(Node ancestorNode: commonAncestorNodes){
                if(!(((InternalNode) ancestorNode).getUseOntPaths()))
                    newCommonAncestorNodes.add(ancestorNode);
            }
            return newCommonAncestorNodes;
        }


        return commonAncestorNodes;
    }

//    public static Set<Node> getCommonAncestorNodes(Node node1, Node node2, int depth, ColumnNode attributeNode){
//        assert node1 instanceof InternalNode: "node1 is not the internal node";
//        assert node2 instanceof InternalNode: "node2 is not the internal node";
//
//        int loopNum = 1;
//        Set<Node> commonAncestorNodes = new HashSet<Node>();
//        Set<Node> ancestorNodesForNode1 = new HashSet<Node>();
//        Set<Node> ancestorNodesForNode2 = new HashSet<Node>();
//
//        Set<Node> tempAncestorNodesForNode1 = new HashSet<Node>();
//        Set<Node> tempAncestorNodesForNode2 = new HashSet<Node>();
//
//        while(loopNum<=depth){
//            if((ancestorNodesForNode1.size()==0) && (ancestorNodesForNode2.size()==0)){
//                ancestorNodesForNode1.addAll(node1.getSourceNodes());
//                ancestorNodesForNode2.addAll(node2.getSourceNodes());
//            }
//            else{
////                assert AncestorNodesForNode1.size() > 0: "AncestorNodesForNode1.size <= 0";
////                assert AncestorNodesForNode2.size() > 0: "AncestorNodesForNode2.size <= 0";
//                for(Node sourceNode1: ancestorNodesForNode1){
//                    tempAncestorNodesForNode1.addAll(sourceNode1.getSourceNodes());
//                }
//                for(Node sourceNode2: ancestorNodesForNode2){
//                    tempAncestorNodesForNode2.addAll(sourceNode2.getSourceNodes());
//                }
//                ancestorNodesForNode1.addAll(tempAncestorNodesForNode1);
//                ancestorNodesForNode2.addAll(tempAncestorNodesForNode2);
//            }
//
////            System.out.println(loopNum + " 层source nodes");
//            ++loopNum;
//        }
//
//        if((ancestorNodesForNode1.size()!=0) && (ancestorNodesForNode2.size()!=0)){
//            commonAncestorNodes.addAll(ancestorNodesForNode1);
//            commonAncestorNodes.retainAll(ancestorNodesForNode2);
//        }
//
//        if((attributeNode != null) && (attributeNode.getUseOntInternalNodes())){
//            Set<Node> newCommonAncestorNodes = new HashSet<Node>();
//            for(Node ancestorNode: commonAncestorNodes){
//                if(!(((InternalNode) ancestorNode).getUseOntPaths()))
//                    newCommonAncestorNodes.add(ancestorNode);
//            }
//            return newCommonAncestorNodes;
//        }
//
//
//        return commonAncestorNodes;
//    }

    public static SemanticModel getNextSearchSemanticModel(SemanticModel searchSemanticModelState,DefaultLink mntPtLink,Node mntPtSourceNode,Node attributeNode,List<DefaultLink> pathLinks){
        DirectedWeightedMultigraph<Node, LabeledLink> emptyGraph = new DirectedWeightedMultigraph<Node, LabeledLink>(LabeledLink.class);
        Map<ColumnNode, ColumnNode> mappingToSourceColumns = new HashMap<ColumnNode, ColumnNode>();
        List<ColumnNode> columnNodes = new LinkedList<ColumnNode>();

        for(DefaultLink linkInSearchSemanticModel: searchSemanticModelState.getGraph().edgeSet()){
            if(linkInSearchSemanticModel.getTarget() instanceof InternalNode) {
                String objectLinkId = LinkIdFactory.getLinkId(linkInSearchSemanticModel.getUri(), linkInSearchSemanticModel.getSource().getId(), linkInSearchSemanticModel.getTarget().getId());
                LabeledLink objectLink = new ObjectPropertyLink(objectLinkId, new Label(linkInSearchSemanticModel.getUri()), ObjectPropertyType.Direct);
                emptyGraph.addVertex(linkInSearchSemanticModel.getSource());
                emptyGraph.addVertex(linkInSearchSemanticModel.getTarget());
                emptyGraph.addEdge(linkInSearchSemanticModel.getSource(), linkInSearchSemanticModel.getTarget(), objectLink);
            }
            else{
                columnNodes.add((ColumnNode) linkInSearchSemanticModel.getTarget());
                mappingToSourceColumns.put((ColumnNode) linkInSearchSemanticModel.getTarget(),(ColumnNode) linkInSearchSemanticModel.getTarget());
                String dataLinkId = LinkIdFactory.getLinkId(linkInSearchSemanticModel.getUri(), linkInSearchSemanticModel.getSource().getId(), linkInSearchSemanticModel.getTarget().getId());
                LabeledLink dataLink = new DataPropertyLink(dataLinkId, new Label(linkInSearchSemanticModel.getUri()));
                emptyGraph.addVertex(linkInSearchSemanticModel.getSource());
                emptyGraph.addVertex(linkInSearchSemanticModel.getTarget());
                emptyGraph.addEdge(linkInSearchSemanticModel.getSource(), linkInSearchSemanticModel.getTarget(), dataLink);
            }
        }

        //initial the mntPt link
        String mntPtLinkId = LinkIdFactory.getLinkId(mntPtLink.getUri(), mntPtSourceNode.getId(), attributeNode.getId());
        LabeledLink mntPtDataLink = new DataPropertyLink(mntPtLinkId, new Label(mntPtLink.getUri()));
        columnNodes.add((ColumnNode) attributeNode);
        mappingToSourceColumns.put((ColumnNode) attributeNode,(ColumnNode) attributeNode);

        //add mntPtSourceNode and attributeNode
        emptyGraph.addVertex(mntPtSourceNode);
        emptyGraph.addVertex(attributeNode);
        emptyGraph.addEdge(mntPtSourceNode, attributeNode, mntPtDataLink);


        for (DefaultLink defaultLink : pathLinks) {
            String defaultLinkId = LinkIdFactory.getLinkId(defaultLink.getUri(), defaultLink.getSource().getId(), defaultLink.getTarget().getId());
            LabeledLink defaultObjectLink = new ObjectPropertyLink(defaultLinkId, new Label(defaultLink.getUri()), ObjectPropertyType.Direct);
            emptyGraph.addVertex(defaultLink.getSource());
            emptyGraph.addVertex(defaultLink.getTarget());
            emptyGraph.addEdge(defaultLink.getSource(), defaultLink.getTarget(), defaultObjectLink);
        }

        SemanticModel nextSearchSemanticModelState = new SemanticModel(new RandomGUID().toString(),emptyGraph,columnNodes,mappingToSourceColumns);
        return nextSearchSemanticModelState;
    }

    public static List<SemanticModel> mergeIntoTreeEDM(SemanticModel searchSemanticModelState,DirectedWeightedMultigraph<Node, DefaultLink> Gint,ColumnNode attributeNode,Boolean noDefaultLink,Set<InternalNode> internalNodesWithUseOntPaths, Boolean hasOntPaths) throws Exception {
        System.out.println("enter mergeIntoTree for adding only one column node to the current search semantic model state");
        System.out.println("enter mergeIntoTree and add "+attributeNode.getColumnName());
        int count = 0;

        Set<InternalNode> internalNodesOfSearchSemanticModelState = new HashSet<InternalNode>();
        Set<String> internalNodeIdsOfSearchSemanticModelState = new HashSet<String>();
        Map<String,Node> internalNodeIdWithInternalNode = new HashMap<String,Node>();
        List<DefaultLink> linksOfIntegrationGraph = new ArrayList<DefaultLink>();
        List<DefaultLink> linksOfSearchSemanticModelState = new ArrayList<DefaultLink>();
        Map<Node, Set<Node>> internalNodeInSearchStateWithNodeMappingsInIntegration = new HashMap<Node, Set<Node>>();
        SemanticModel initialSearchSemanticModelState = null;
        SemanticModel mergeInitialSearchSemanticModelState = null;
        SemanticModel nextSearchState = null;
        List<SemanticModel> newTrees = new LinkedList<SemanticModel>();

        //obtain all internal nodes of the current search semantic model state
        internalNodesOfSearchSemanticModelState = searchSemanticModelState.getInternalNodes();
        //obtain all internal node ids of the current search semantic model state
        for(InternalNode internalNode: internalNodesOfSearchSemanticModelState){
            internalNodeIdsOfSearchSemanticModelState.add(internalNode.getId());
            internalNodeIdWithInternalNode.put(internalNode.getId(),internalNode);
        }
        assert internalNodesOfSearchSemanticModelState.size() == searchSemanticModelState.getInternalNodes().size(): "internalNodesOfSearchSemanticModelState.size != internalNodeIdsOfSearchSemanticModelState.size";
        assert internalNodeIdWithInternalNode.size() == searchSemanticModelState.getInternalNodes().size(): "internalNodeIdWithInternalNode.size != internalNodeIdsOfSearchSemanticModelState.size";
        //obtain all links of the integration graph(Gint)
        linksOfIntegrationGraph = new ArrayList<DefaultLink>(Gint.edgeSet());

        //find all mapping internal nodes in the integration graph for all internal nodes in the current search semantic model
        for (InternalNode internal_node_search_state : internalNodesOfSearchSemanticModelState) {
            Set<Node> internalNodesMappingForEachInternalNodeOfSearchState = new HashSet<Node>();
            //obtain all internal nodes mappings in integration graph for each internal node in the initial search semantic model state
            for (Node internal_node_integration : Gint.vertexSet()) {
                if ((internal_node_integration instanceof InternalNode) && (internal_node_integration.getId().equals(internal_node_search_state.getId()))) {
                    internalNodesMappingForEachInternalNodeOfSearchState.add(internal_node_integration);
                }
            }
            //add all internal nodes mappings in integration graph into internalNodeInSearchStateWithNodeMappingsInIntegration
            internalNodeInSearchStateWithNodeMappingsInIntegration.put(internal_node_search_state, internalNodesMappingForEachInternalNodeOfSearchState);
        }
        assert internalNodeInSearchStateWithNodeMappingsInIntegration.size() == internalNodesOfSearchSemanticModelState.size(): "mapping nodes in integration graph is wrong";

        /**obtain root node or root nodes of the search semantic model state and obtain all mapping nodes for the root nodes**/
        List<Node> rootList = new ArrayList<Node>();
        Set<Node> rootMappingsList = new HashSet<Node>();
        rootList = getSemanticModelRootList(searchSemanticModelState);
        //obtain the mapping nodes set for the root nodes of the initial search semantic model state
        for(Node rootNode: rootList){
            if(internalNodeInSearchStateWithNodeMappingsInIntegration.get(rootNode).size()>0)
                rootMappingsList.addAll(internalNodeInSearchStateWithNodeMappingsInIntegration.get(rootNode));
        }
        if((searchSemanticModelState.getGraph().vertexSet().size()>0) && (searchSemanticModelState.getGraph().edgeSet().size()>0)) {
            assert rootMappingsList.size() > 0 : "rootMappingsList.size <= 0";
//        System.out.println("rootMappingsList.size:" + rootMappingsList.size());
        }


        /**initial all connected paths list**/
        List<List<Node>> allIntoMountConnectedPathsUsingNodes;//save all connected paths using nodes by connecting the current semantic model into class node with attribute node
        List<List<Node>> allIntoTreeConnectedPathsUsingNodes;//save all connected paths using nodes by connecting class node with attribute node into the current semantic model
        List<List<Node>> allTriangleTreeConnectedPathsUsingNodesForOneRoot;
        List<List<Node>> allTriangleMountConnectedPathsUsingNodesForOneRoot;
        List<List<Node>> allTriangleConnectedPathsUsingNodes;//save all connected paths using nodes by connecting class node with attribute node and the current semantic model with common ancestor class nodes



        /**loop all mntPts (that is, all class nodes with candidate semantic types for the added attribute node)
         * and find all connected paths to merge the mntPts and the current semantic model for generating all next
         * search semantic models**/

        /**obtain all semantic types (contains correct and candidate semantic types 2023/04/04, note that some correct semantic types are not in the integration graph) for the added attribute nodes**/
        Set<SemanticType> allSemanticTypesForAddedAttributeNode = new HashSet<SemanticType>();
        allSemanticTypesForAddedAttributeNode = getSemanticTypes(attributeNode,true,true,4);
        assert allSemanticTypesForAddedAttributeNode.size() > 0 && allSemanticTypesForAddedAttributeNode.size() < 6: "allSemanticTypesForAddedAttributeNode < 0 or allSemanticTypesForAddedAttributeNode > 5";

        /**mntPts save the links whose node has same semantic types with the added attribute node**/
        Set<DefaultLink> mntPts = new HashSet<DefaultLink>();
        Map<Node,Set<DefaultLink>> mntPtNodeWithMntPtLinks = new HashMap<Node,Set<DefaultLink>>();
        Set<String> mntPtsWithSourceNodeIdAndLinkUri = new HashSet<String>();//used to check the mntPt with same source node id and link uri
        //loop all semantic types in allSemanticTypesForAddedAttributeNode, and find all mntPts
        for (SemanticType semanticType : allSemanticTypesForAddedAttributeNode) {
            for (DefaultLink link : Gint.edgeSet()) {
                if ((link.getSource().getUri().equals(semanticType.getDomain().getUri())) && (link.getUri().equals(semanticType.getType().getUri())) && (!mntPtsWithSourceNodeIdAndLinkUri.contains(link.getSource().getId()+semanticType.getType().getUri().toString()))) {
                    mntPtsWithSourceNodeIdAndLinkUri.add(link.getSource().getId()+semanticType.getType().getUri().toString());
                    mntPts.add(link);
                }
            }
        }

        Set<DefaultLink> linksWithSameSourceNode = new HashSet<DefaultLink>();
        for(DefaultLink mntPtLink: mntPts){
            if(!mntPtNodeWithMntPtLinks.keySet().contains(mntPtLink.getSource())) {
                linksWithSameSourceNode = new HashSet<DefaultLink>();
                linksWithSameSourceNode.add(mntPtLink);
                mntPtNodeWithMntPtLinks.put(mntPtLink.getSource(), linksWithSameSourceNode);
            }
            else{
                linksWithSameSourceNode = mntPtNodeWithMntPtLinks.get(mntPtLink.getSource());
                linksWithSameSourceNode.add(mntPtLink);
                mntPtNodeWithMntPtLinks.put(mntPtLink.getSource(), linksWithSameSourceNode);
            }
        }

        int mntPtsNum = 0;
        for(Node mntPtNode: mntPtNodeWithMntPtLinks.keySet()){
            mntPtsNum = mntPtsNum + mntPtNodeWithMntPtLinks.get(mntPtNode).size();
        }
        assert mntPts.size() == mntPtsNum: "mntPts.size != mntPtsNum";

        Set<List<DefaultLink>> allThreeTypesPathsForMntPtSourceNode = new HashSet<List<DefaultLink>>();
        Set<List<DefaultLink>> allIntoMountPathsForMntPtSourceNode = new HashSet<List<DefaultLink>>();
        Set<List<DefaultLink>> allIntoTreePathsForMntPtSourceNode = new HashSet<List<DefaultLink>>();
        Set<List<DefaultLink>> allTrianglePathsForMntPtSourceNode = new HashSet<List<DefaultLink>>();

        /**find all paths (1.direct mapping; 2.intoMount, intoTree, triangle)**/
        int directMappingPaths = 0;
        int indirectMappingPaths = 1;
        Map<Integer,List<SemanticModel>> PathsTypeWithNextSemanticModels = new HashMap<Integer,List<SemanticModel>>();

        List<SemanticModel> nextSemanticModelsForDirectMappingPaths = new ArrayList<SemanticModel>();
        List<SemanticModel> nextSemanticModelsForInDirectMappingPaths = new ArrayList<SemanticModel>();
        Boolean pathWithDefaultLink = false;
        List<DefaultLink> neededConnectedPathUsingLinks = new ArrayList<DefaultLink>();
        Map<String,List<DefaultLink>> nodePairStringWithLinksInIntegrationGraph = new HashMap<String,List<DefaultLink>>();
        for(DefaultLink integrationLink: linksOfIntegrationGraph){
            if(!nodePairStringWithLinksInIntegrationGraph.keySet().contains(integrationLink.getSource().getId()+integrationLink.getTarget().getId())){
                nodePairStringWithLinksInIntegrationGraph.put(integrationLink.getSource().getId()+integrationLink.getTarget().getId(),new ArrayList<DefaultLink>(Arrays.asList(integrationLink)));
            }
            else{
                List<DefaultLink> tempLinksWithSameNodePair = new ArrayList<DefaultLink>(nodePairStringWithLinksInIntegrationGraph.get(integrationLink.getSource().getId()+integrationLink.getTarget().getId()));
                tempLinksWithSameNodePair.add(integrationLink);
                nodePairStringWithLinksInIntegrationGraph.put(integrationLink.getSource().getId()+integrationLink.getTarget().getId(),tempLinksWithSameNodePair);
            }
        }

        int linksNumInIntegrationGraph = 0;
        for(String nodePairString: nodePairStringWithLinksInIntegrationGraph.keySet()){
            linksNumInIntegrationGraph = linksNumInIntegrationGraph + nodePairStringWithLinksInIntegrationGraph.get(nodePairString).size();
        }
        assert linksOfIntegrationGraph.size() == linksNumInIntegrationGraph: "linksOfIntegrationGraph.size != linksNumInIntegrationGraph";

        Map<Node,Set<List<DefaultLink>>> mntPtSourceNodeWithThreeTypesPathsUsingLinks = new HashMap<Node,Set<List<DefaultLink>>>();
        Boolean isNeededConnectedPath = true;

        /**loop all mntPts in mntPts set**/
        for (Node mntPtSourceNode : mntPtNodeWithMntPtLinks.keySet()) {
            Boolean hasTrianglePathForSteinerNodeWithOntPaths = false;
            Set<InternalNode> temp_internalNodesWithUseOntPaths = new HashSet<InternalNode>(internalNodesWithUseOntPaths);
            if(!(((InternalNode) mntPtSourceNode).getUseOntPaths())){
                noDefaultLink = true;
            }
            else{
                temp_internalNodesWithUseOntPaths.remove(mntPtSourceNode);
                noDefaultLink = false;
            }
            /**save three types paths for a mntPtSourceNod, add nodes and links into the current semantic model using these paths**/
            allThreeTypesPathsForMntPtSourceNode = new HashSet<List<DefaultLink>>();
            allIntoMountPathsForMntPtSourceNode = new HashSet<List<DefaultLink>>();
            allIntoTreePathsForMntPtSourceNode = new HashSet<List<DefaultLink>>();
            allTrianglePathsForMntPtSourceNode = new HashSet<List<DefaultLink>>();


            /**一.direct mapping if mntPt source node in the search semantic model state**/
            //if the mntPt source node in the search semantic model state, we need to add the target nodes and links in mntPtNodeWithMntPtLinks.get(mntPtSourceNode)
            if (internalNodeIdsOfSearchSemanticModelState.contains(mntPtSourceNode.getId())) {
                //obtain the mapping node in initial search semantic model state for the mntPtSourceNode
                Node mntPtSourceNodeMapping = internalNodeIdWithInternalNode.get(mntPtSourceNode.getId());
//                loop all mntPt links in mntPtNodeWithMntPtLinks.get(mntPtSourceNode)
                for (DefaultLink mntPtLink : mntPtNodeWithMntPtLinks.get(mntPtSourceNode)) {
                    assert mntPtSourceNode.equals(mntPtLink.getSource()) : "mntPtSourceNode != mntPtLink.sourceNode";
                    String mntPtLinkId = LinkIdFactory.getLinkId(mntPtLink.getUri(), mntPtSourceNode.getId(), attributeNode.getId());
                    LabeledLink labeledMntPtLink = new DataPropertyLink(mntPtLinkId, new Label(mntPtLink.getUri()));
                    initialSearchSemanticModelState = searchSemanticModelState.clone();
                    //add the added attribute node
                    initialSearchSemanticModelState.getGraph().addVertex(attributeNode);
                    //add link
                    initialSearchSemanticModelState.getGraph().addEdge(mntPtSourceNodeMapping, attributeNode, labeledMntPtLink);
                    assert initialSearchSemanticModelState.getGraph().vertexSet().size() == (searchSemanticModelState.getGraph().vertexSet().size() + 1) : "not add the added attribute node based on direct paths";
                    assert initialSearchSemanticModelState.getGraph().edgeSet().size() == (searchSemanticModelState.getGraph().edgeSet().size() + 1) : "not add the added mntPt link based on direct paths";
                    nextSemanticModelsForDirectMappingPaths.add(initialSearchSemanticModelState);
                    newTrees.add(initialSearchSemanticModelState);
                    ++count;
                }
            }

            /**二.intoMount, intoTree, triangle**/
            //if mntPt source node is not in search semantic model state, we need to find all three types paths,
            //and obtain all next search semantic models based on these paths
            else {
                //initial these lists for each mntPtSourceNode that is not in the initial search semantic model
                allIntoMountConnectedPathsUsingNodes = new ArrayList<List<Node>>();//intoMount paths for each mntPt source node
                allIntoTreeConnectedPathsUsingNodes = new ArrayList<List<Node>>();//intoTree paths for each mntPt source node
                Set<DefaultLink> tempLinksBetweenSourceAndTarget = null;
                List<List<DefaultLink>> allNodePairLinksList = new ArrayList<List<DefaultLink>>();
                List<List<List<DefaultLink>>> allNodePairLinksListBetweenTreeAndMntPtWithCommonAncestorNode = new ArrayList<List<List<DefaultLink>>>();
                List<List<DefaultLink>> allNeededConnectedPathsUsingLinksForOnePathUsingNodes = new ArrayList<List<DefaultLink>>();
                List<List<DefaultLink>> allNeededConnectedPathsUsingLinksForOneTreePathUsingNodes = new ArrayList<List<DefaultLink>>();
                List<List<DefaultLink>> allNeededConnectedPathsUsingLinksForOneMountPathUsingNodes = new ArrayList<List<DefaultLink>>();


                /**1.find all intoMount paths by adding the initial search semantic model state tree into the mntPt source node**/

                /**① find all connected paths (using nodes) that view the mntPt source node as the source, the root node of the initial search semantic model state tree as target
                 * the largest path is 2: represents there is a maximum of one edge between source and target**/

                //obtain the mapping nodes for the root nodes in the initial search semantic model state
                for (Node rootMappingNode : rootMappingsList) {
                    //find all connected paths from mntPtSourceNode to the mapping root node
                    FindPaths.connectedPathsNode = new ArrayList<List<Node>>();
                    if(hasOntPaths) {
                        FindPaths.useInternalNodesWithOntPaths = 0;
                        findAllPathNode(linksOfIntegrationGraph, mntPtSourceNode.getId(), rootMappingNode.getId(), 2, mntPtSourceNode);
                    }
                    else
                        findAllPathNode(linksOfIntegrationGraph, mntPtSourceNode.getId(), rootMappingNode.getId(), 2);
                    allIntoMountConnectedPathsUsingNodes.addAll(FindPaths.connectedPathsNode);
                }
                System.out.println("allIntoMountConnectedPathsUsingNodes before:" + allIntoMountConnectedPathsUsingNodes.size());


                //loop all connected paths using nodes and obtain the needed connected paths using links
                for (List<Node> connected_path_intoMount : allIntoMountConnectedPathsUsingNodes) {
                    //if there are two same nodes in the path, we need to ignore this path because it appears a circle
                    Set<Node> judgeSet = new HashSet<Node>(connected_path_intoMount);
                    if(judgeSet.size()!=connected_path_intoMount.size())
                        continue;
                    allNeededConnectedPathsUsingLinksForOnePathUsingNodes = new ArrayList<List<DefaultLink>>();
                    isNeededConnectedPath = true;
                    allNodePairLinksList = new ArrayList<List<DefaultLink>>();

                    for (int i = 0; i < connected_path_intoMount.size() - 1; i++) {
                        /**avoid circle, we need to check whether the node (except tree-root node) in the connected_path_intoMount exists in initial search semantic model state (internal nodes)**/
                        if (internalNodeIdWithInternalNode.keySet().contains(connected_path_intoMount.get(i).getId())) {
                            isNeededConnectedPath = false;
                            break;
                        }
                        //the connected_path_intoMount doesn't have circles, we need to get the connected path using links
                        if(nodePairStringWithLinksInIntegrationGraph.containsKey(connected_path_intoMount.get(i).getId() + connected_path_intoMount.get(i + 1).getId()))
                            allNodePairLinksList.add(nodePairStringWithLinksInIntegrationGraph.get(connected_path_intoMount.get(i).getId() + connected_path_intoMount.get(i + 1).getId()));
                        else {
                            isNeededConnectedPath = false;
                            break;
                        }
                    }
                    if (!isNeededConnectedPath)
                        continue;
                    if (allNodePairLinksList.size() > 0) {
                        //obtain all needed connected paths for the current connected_path_intoMount
                        allNeededConnectedPathsUsingLinksForOnePathUsingNodes = descartesRecursive(allNodePairLinksList);
                    }
                    assert allNeededConnectedPathsUsingLinksForOnePathUsingNodes.size() > 0 : "allNeededConnectedPathsUsingLinksForOnePathUsingNodes.size <= 0";
                    for (List<DefaultLink> pathUsingLinks : allNeededConnectedPathsUsingLinksForOnePathUsingNodes) {
                        assert pathUsingLinks.size() == connected_path_intoMount.size() - 1 : "into mount pathUsingLinks size is wrong";
                        if (noDefaultLink) {
                            pathWithDefaultLink = false;//judge if the needed connected_path_intoMount has default link
                            for (DefaultLink link : pathUsingLinks) {
                                if (link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink")) {
                                    pathWithDefaultLink = true;
                                    break;
                                }
                            }
                            if (!pathWithDefaultLink) {
                                allIntoMountPathsForMntPtSourceNode.add(pathUsingLinks);
                            }
                        } else {
                            allIntoMountPathsForMntPtSourceNode.add(pathUsingLinks);
                        }
                    }
                }
                if((((InternalNode) mntPtSourceNode).getUseOntPaths()) && (allIntoMountPathsForMntPtSourceNode.size()>0))
                    allThreeTypesPathsForMntPtSourceNode.add(new ArrayList<List<DefaultLink>>(allIntoMountPathsForMntPtSourceNode).get(0));
                else
                    allThreeTypesPathsForMntPtSourceNode.addAll(allIntoMountPathsForMntPtSourceNode);//add all intoMountPaths for a mntPtSourceNode into allThreeTypesPathsForMntPtSourceNode, don't forget add it into mntPtSourceNodeWithThreeTypesPathsUsingLinks map when adding all three types paths
                System.out.println("add allIntoMountPathsForMntPtSourceNode, allThreeTypesPathsForMntPtSourceNode.size:" + allThreeTypesPathsForMntPtSourceNode.size());

                /**② find all connected paths (using nodes) that view the nodes of the initial search semantic model state tree as sources,
                 * the mntPt source node as the target, if mntPtSourceNode is not in the initial search semantic model state
                 * the largest path is 2: represents there is a maximum of one edge between source and target**/
                //check whether mntPtSourceNode exists in the initial search semantic model state
                if (internalNodeIdsOfSearchSemanticModelState.contains(mntPtSourceNode.getId())) {
                    continue;
                } else {
                    //loop all internal nodes in the initial search semantic model state
                    for (Node internalNode : internalNodesOfSearchSemanticModelState) {
                        //loop all internal node mappings in the integration graph for each internal node in the initial search semantic model state
                        for (Node internalMappingNodeForOneInternalNodeInSearchState : internalNodeInSearchStateWithNodeMappingsInIntegration.get(internalNode)) {
                            //find all connected paths from mapping nodes of the initial search semantic model state to the mntPt source node
                            FindPaths.connectedPathsNode = new ArrayList<List<Node>>();
                            if(hasOntPaths) {
                                FindPaths.useInternalNodesWithOntPaths = 0;
                                findAllPathNode(linksOfIntegrationGraph, internalMappingNodeForOneInternalNodeInSearchState.getId(), mntPtSourceNode.getId(), 2, mntPtSourceNode);
                            }
                            else
                                findAllPathNode(linksOfIntegrationGraph, internalMappingNodeForOneInternalNodeInSearchState.getId(), mntPtSourceNode.getId(), 2);
                            allIntoTreeConnectedPathsUsingNodes.addAll(FindPaths.connectedPathsNode);
                        }
                    }
                }
                System.out.println("allIntoTreeConnectedPathsUsingNodes before:" + allIntoTreeConnectedPathsUsingNodes.size());

                //save connected links between source and target into the temporary defaultLinks set
                for (List<Node> connected_path_intoTree : allIntoTreeConnectedPathsUsingNodes) {

                    //if there are two same nodes in the path, we need to ignore this path because it appears a circle
                    Set<Node> judgeSet = new HashSet<Node>(connected_path_intoTree);
                    if(judgeSet.size()!=connected_path_intoTree.size())
                        continue;
                    allNeededConnectedPathsUsingLinksForOnePathUsingNodes = new ArrayList<List<DefaultLink>>();
                    isNeededConnectedPath = true;
                    allNodePairLinksList = new ArrayList<List<DefaultLink>>();

                    //save all links for the connected_path_intoTree
                    for (int i = 0; i < connected_path_intoTree.size() - 1; i++) {;
                        /**"very important" 依次遍历path中的node pair(1-2,2-3,3-4...)
                         * 检查当前node pair是否在tree中有路径 如果有则不添加node pair之间对应到integration graph上的link信息
                         * 如果没有则添加对应到integration graph上的link信息**/

                        /**if the initial search semantic model state has the node i and i+1 (that represents there is a link
                         * between node i and i+1 in the initial search semantic model state), and there is only one link between the node i and i+1,
                         * we don't need to add this link; else we need to save all possible links between the node i and i+1 into the allNodePairLinksList**/

                        /**check if there is a circle while adding the links between node i and i+1**/
                        if ((internalNodeIdWithInternalNode.keySet().contains(connected_path_intoTree.get(i).getId())) && (internalNodeIdWithInternalNode.keySet().contains(connected_path_intoTree.get(i + 1).getId()))) {
                            if(nodePairStringWithLinksInIntegrationGraph.containsKey(connected_path_intoTree.get(i).getId() + connected_path_intoTree.get(i + 1).getId())){
                                if (nodePairStringWithLinksInIntegrationGraph.get(connected_path_intoTree.get(i).getId() + connected_path_intoTree.get(i + 1).getId()).size() == 1)
                                    continue;
                                else if (nodePairStringWithLinksInIntegrationGraph.get(connected_path_intoTree.get(i).getId() + connected_path_intoTree.get(i + 1).getId()).size() > 1)
                                    allNodePairLinksList.add(nodePairStringWithLinksInIntegrationGraph.get(connected_path_intoTree.get(i).getId() + connected_path_intoTree.get(i + 1).getId()));
                                else {
                                    isNeededConnectedPath = false;
                                    break;
                                }
                            }
                            else{
                                isNeededConnectedPath = false;
                                break;
                            }
                        }
                        //check if node i+1 exists in the initial search semantic model, avoid the circle
                        else if ((!(internalNodeIdWithInternalNode.keySet().contains(connected_path_intoTree.get(i).getId()))) && (internalNodeIdWithInternalNode.keySet().contains(connected_path_intoTree.get(i + 1).getId()))) {
                            isNeededConnectedPath = false;
                            break;
                        } else {
                            if(nodePairStringWithLinksInIntegrationGraph.containsKey(connected_path_intoTree.get(i).getId() + connected_path_intoTree.get(i + 1).getId())) {
                                allNodePairLinksList.add(nodePairStringWithLinksInIntegrationGraph.get(connected_path_intoTree.get(i).getId() + connected_path_intoTree.get(i + 1).getId()));
                            }
                            else{
                                isNeededConnectedPath = false;
                                break;
                            }
                        }

                        /**如果path.size()>2 检查当前pathnode的nodes(除第一个node外)是否存在于StartSearchState的InternalNodes中  避免出现环**/
                    }
                    if (!isNeededConnectedPath)
                        continue;
                    if (allNodePairLinksList.size() > 0) {
                        //obtain all needed connected paths for the current connected_path_intoTree
                        allNeededConnectedPathsUsingLinksForOnePathUsingNodes = descartesRecursive(allNodePairLinksList);
                    }
                    assert allNeededConnectedPathsUsingLinksForOnePathUsingNodes.size() > 0 : "allNeededConnectedPathsUsingLinksForOnePathUsingNodes.size <= 0";
                    for (List<DefaultLink> pathUsingLinks : allNeededConnectedPathsUsingLinksForOnePathUsingNodes) {
                        System.out.println("pathUsingLinks.size:" + pathUsingLinks.size());
                        System.out.println("connected_path_intoTree.size:" + connected_path_intoTree.size());

                        assert pathUsingLinks.size() > 0 : "into tree pathUsingLinks size is wrong";
                        if (noDefaultLink) {
                            pathWithDefaultLink = false;//judge if the needed connected_path_intoMount has default link
                            for (DefaultLink link : pathUsingLinks) {
                                if (link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink")) {
                                    pathWithDefaultLink = true;
                                    break;
                                }
                            }
                            if (!pathWithDefaultLink) {
                                allIntoTreePathsForMntPtSourceNode.add(pathUsingLinks);
                            }
                        } else {
                            allIntoTreePathsForMntPtSourceNode.add(pathUsingLinks);
                        }
                    }
                }
                if((((InternalNode) mntPtSourceNode).getUseOntPaths()) && (allIntoTreePathsForMntPtSourceNode.size()>0))
                    allThreeTypesPathsForMntPtSourceNode.add(new ArrayList<List<DefaultLink>>(allIntoTreePathsForMntPtSourceNode).get(0));
                else
                    allThreeTypesPathsForMntPtSourceNode.addAll(allIntoTreePathsForMntPtSourceNode);//add all intoMountPaths for a mntPtSourceNode into allThreeTypesPathsForMntPtSourceNode, don't forget add it into mntPtSourceNodeWithThreeTypesPathsUsingLinks map when adding all three types paths
                System.out.println("add allIntoTreePathsForMntPtSourceNode, allThreeTypesPathsForMntPtSourceNode.size:" + allThreeTypesPathsForMntPtSourceNode.size());

                /**③ find all connected paths (using nodes) that connect the mntPt source node and the root node of the initial
                 * search semantic model state using the ancestor nodes
                 * the largest path is 3: represents there is a maximum of one node between source and target**/
                //find the common ancestor nodes for the mntPt source node and the root node of the initial search
                //semantic model state, we only find the ancestor nodes with depth 1 currently
                Set<Node> commonAncestorNodes = new HashSet<Node>();
                for (Node rootMappingNode : rootMappingsList) {
                    commonAncestorNodes = getCommonAncestorNodes(mntPtSourceNode,rootMappingNode,1,hasOntPaths);
                    System.out.println(rootMappingNode.getId() + " commonAncestorNodes.size:" + commonAncestorNodes.size());
                    //loop the ancestor node in commonAncestorNodes, and find the paths from the ancestor node to the root of the initial search semantic model state and mntPtSourceNode
                    for (Node commonAncestorNode : commonAncestorNodes) {
                        allTriangleTreeConnectedPathsUsingNodesForOneRoot = new ArrayList<List<Node>>();
                        allTriangleMountConnectedPathsUsingNodesForOneRoot = new ArrayList<List<Node>>();
                        //view the common ancestor node as source node, one of the root in the initial search semantic model as the target node
                        FindPaths.connectedPathsNode = new ArrayList<List<Node>>();
                        if(hasOntPaths) {
                            FindPaths.useInternalNodesWithOntPaths = 0;
                            findAllPathNode(linksOfIntegrationGraph, commonAncestorNode.getId(), rootMappingNode.getId(), 2, mntPtSourceNode);
                        }
                        else
                            findAllPathNode(linksOfIntegrationGraph, commonAncestorNode.getId(), rootMappingNode.getId(), 2);
                        for(List<Node> tempPathNodes: FindPaths.connectedPathsNode){
                            Set<Node> intersection = new HashSet<Node>(temp_internalNodesWithUseOntPaths);
                            intersection.retainAll(tempPathNodes);
                            if(intersection.size()==0)
                                allTriangleTreeConnectedPathsUsingNodesForOneRoot.add(tempPathNodes);
                        }
                        if(allTriangleTreeConnectedPathsUsingNodesForOneRoot.size() == 0)
                            continue;

                        //view the common ancestor node as source node, mntPt source node as the target node
                        FindPaths.connectedPathsNode = new ArrayList<List<Node>>();
                        if(hasOntPaths) {
                            FindPaths.useInternalNodesWithOntPaths = 0;
                            findAllPathNode(linksOfIntegrationGraph, commonAncestorNode.getId(), mntPtSourceNode.getId(), 2, mntPtSourceNode);
                        }
                        else
                            findAllPathNode(linksOfIntegrationGraph, commonAncestorNode.getId(), mntPtSourceNode.getId(), 2);
                        for(List<Node> tempPathNodes: FindPaths.connectedPathsNode){
                            Set<Node> intersection = new HashSet<Node>(temp_internalNodesWithUseOntPaths);
                            intersection.retainAll(tempPathNodes);
                            if(intersection.size()==0)
                                allTriangleMountConnectedPathsUsingNodesForOneRoot.add(tempPathNodes);
                        }
                        if(allTriangleMountConnectedPathsUsingNodesForOneRoot.size() == 0)
                            continue;

                        //loop all connected_path_triangleTree
                        for (List<Node> connected_path_triangleTree : allTriangleTreeConnectedPathsUsingNodesForOneRoot) {
                            //if there are two same nodes in the path, we need to ignore this path because it appears a circle
                            Set<Node> judgeSet = new HashSet<Node>(connected_path_triangleTree);
                            if(judgeSet.size()!=connected_path_triangleTree.size())
                                continue;
                            allNeededConnectedPathsUsingLinksForOneTreePathUsingNodes = new ArrayList<List<DefaultLink>>();
                            isNeededConnectedPath = true;
                            allNodePairLinksList = new ArrayList<List<DefaultLink>>();
                            for (int i = 0; i < connected_path_triangleTree.size() - 1; i++) {
                                /**avoid circle, we need to check whether the node (except tree-root node) in the connected_path_triangleTree exists in initial search semantic model state (internal nodes)**/
                                if (internalNodeIdWithInternalNode.keySet().contains(connected_path_triangleTree.get(i).getId())) {
                                    isNeededConnectedPath = false;
                                    break;
                                }
                                //the connected_path_triangleTree doesn't have circles, we need to get the connected path using links
                                if(nodePairStringWithLinksInIntegrationGraph.containsKey(connected_path_triangleTree.get(i).getId() + connected_path_triangleTree.get(i + 1).getId())) {
                                    allNodePairLinksList.add(nodePairStringWithLinksInIntegrationGraph.get(connected_path_triangleTree.get(i).getId() + connected_path_triangleTree.get(i + 1).getId()));
                                }
                                else{
                                    isNeededConnectedPath = false;
                                    break;
                                }
                            }
                            if (!isNeededConnectedPath)
                                continue;
                            if (allNodePairLinksList.size() > 0) {
                                //obtain all needed connected paths for the current connected_path_triangleTree
                                allNeededConnectedPathsUsingLinksForOneTreePathUsingNodes = descartesRecursive(allNodePairLinksList);
                            }
                            assert allNeededConnectedPathsUsingLinksForOneTreePathUsingNodes.size() > 0 : "allNeededConnectedPathsUsingLinksForOneTreePathUsingNodes.size <= 0";

                            //loop all connected_path_triangleMount
                            for (List<Node> connected_path_triangleMount : allTriangleMountConnectedPathsUsingNodesForOneRoot) {
                                if(connected_path_triangleMount.size() > (4-connected_path_triangleTree.size()))
                                    continue;

                                //if there are two same nodes in the path, we need to ignore this path because it appears a circle
                                judgeSet = new HashSet<Node>(connected_path_triangleMount);
                                if(judgeSet.size()!=connected_path_triangleMount.size())
                                    continue;

                                List<Node> intersection = new ArrayList<Node>(connected_path_triangleTree);
                                intersection.retainAll(connected_path_triangleMount);
                                if (intersection.size() > 1)//there are two or more same nodes in the tree and the mntPt
                                    continue;

                                allNeededConnectedPathsUsingLinksForOneMountPathUsingNodes = new ArrayList<List<DefaultLink>>();
                                isNeededConnectedPath = true;
                                allNodePairLinksList = new ArrayList<List<DefaultLink>>();
                                allNodePairLinksListBetweenTreeAndMntPtWithCommonAncestorNode = new ArrayList<List<List<DefaultLink>>>();

                                for (int i = 0; i < connected_path_triangleMount.size() - 1; i++) {
                                    /**avoid circle, we need to check whether the node (except tree-root node) in the connected_path_triangleMount exists in initial search semantic model state (internal nodes)**/
                                    if (internalNodeIdWithInternalNode.keySet().contains(connected_path_triangleMount.get(i).getId())) {
                                        isNeededConnectedPath = false;
                                        break;
                                    }
                                    //the connected_path_triangleMount doesn't have circles, we need to get the connected path using links
                                    if(nodePairStringWithLinksInIntegrationGraph.containsKey(connected_path_triangleMount.get(i).getId() + connected_path_triangleMount.get(i + 1).getId())) {
                                        allNodePairLinksList.add(nodePairStringWithLinksInIntegrationGraph.get(connected_path_triangleMount.get(i).getId() + connected_path_triangleMount.get(i + 1).getId()));
                                    }
                                    else{
                                        isNeededConnectedPath = false;
                                        break;
                                    }
                                }
                                if (!isNeededConnectedPath)
                                    continue;
                                if (allNodePairLinksList.size() > 0) {
                                    //obtain all needed connected paths for the current connected_path_triangleMount
                                    allNeededConnectedPathsUsingLinksForOneMountPathUsingNodes = descartesRecursive(allNodePairLinksList);
                                }
                                assert allNeededConnectedPathsUsingLinksForOneMountPathUsingNodes.size() > 0 : "allNeededConnectedPathsUsingLinksForOneMountPathUsingNodes.size <= 0";

                                allNodePairLinksListBetweenTreeAndMntPtWithCommonAncestorNode.add(allNeededConnectedPathsUsingLinksForOneTreePathUsingNodes);
                                allNodePairLinksListBetweenTreeAndMntPtWithCommonAncestorNode.add(allNeededConnectedPathsUsingLinksForOneMountPathUsingNodes);
                                assert allNodePairLinksListBetweenTreeAndMntPtWithCommonAncestorNode.size() > 1 : "allNodePairLinksListBetweenTreeAndMntPtWithCommonAncestorNode.size <= 1";

                                allNeededConnectedPathsUsingLinksForOnePathUsingNodes = descartesRecursiveForDoubleList(allNodePairLinksListBetweenTreeAndMntPtWithCommonAncestorNode);

                                for (List<DefaultLink> pathUsingLinks : allNeededConnectedPathsUsingLinksForOnePathUsingNodes) {
                                    assert pathUsingLinks.size() == connected_path_triangleTree.size() + connected_path_triangleMount.size() - 2 : "triangle pathUsingLinks size is wrong";
                                    if (noDefaultLink) {
                                        pathWithDefaultLink = false;//judge if the needed connected_path_triangle has default link
                                        for (DefaultLink link : pathUsingLinks) {
                                            if (link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink")) {
                                                pathWithDefaultLink = true;
                                                break;
                                            }
                                        }
                                        if (!pathWithDefaultLink) {
                                            allTrianglePathsForMntPtSourceNode.add(pathUsingLinks);
                                        }
                                    } else {
                                        if(((InternalNode) mntPtSourceNode).getUseOntPaths()){
                                            allTrianglePathsForMntPtSourceNode.add(pathUsingLinks);
                                            hasTrianglePathForSteinerNodeWithOntPaths = true;
                                            break;
                                        }
                                        allTrianglePathsForMntPtSourceNode.add(pathUsingLinks);
                                    }
                                }
                                if((((InternalNode) mntPtSourceNode).getUseOntPaths()) && (hasTrianglePathForSteinerNodeWithOntPaths))
                                    break;
                            }
                            if((((InternalNode) mntPtSourceNode).getUseOntPaths()) && (hasTrianglePathForSteinerNodeWithOntPaths))
                                break;
                        }
                        if((((InternalNode) mntPtSourceNode).getUseOntPaths()) && (hasTrianglePathForSteinerNodeWithOntPaths))
                            break;
                    }
                    if((((InternalNode) mntPtSourceNode).getUseOntPaths()) && (hasTrianglePathForSteinerNodeWithOntPaths))
                        break;
                }
                allThreeTypesPathsForMntPtSourceNode.addAll(allTrianglePathsForMntPtSourceNode);//add all trianglePaths for a mntPtSourceNode into allThreeTypesPathsForMntPtSourceNode, don't forget add it into mntPtSourceNodeWithThreeTypesPathsUsingLinks map when adding all three types paths
                System.out.println("add allTrianglePathsForMntPtSourceNode, allThreeTypesPathsForMntPtSourceNode.size:" + allThreeTypesPathsForMntPtSourceNode.size());
                if(((InternalNode) mntPtSourceNode).getUseOntPaths())
                    assert allThreeTypesPathsForMntPtSourceNode.size() <= 3: "allThreeTypesPathsForMntPtSourceNode.size > 3";

            }
            /**二.intoMount, intoTree, triangle**/

            /**add one type of paths, and generate different types of next search semantic models**/

            if ((allIntoMountPathsForMntPtSourceNode.size() > 0) || (allIntoTreePathsForMntPtSourceNode.size() > 0) || (allTrianglePathsForMntPtSourceNode.size() > 0)){
                for (DefaultLink mntPtLink : mntPtNodeWithMntPtLinks.get(mntPtSourceNode)) {
                    /**loop and add different types of the paths**/
                    if (allIntoMountPathsForMntPtSourceNode.size() > 0) {
                        System.out.println("add into mount paths");

                        for (List<DefaultLink> intoMountPath : allIntoMountPathsForMntPtSourceNode) {
                            ++count;

                            nextSemanticModelsForInDirectMappingPaths.add(getNextSearchSemanticModel(searchSemanticModelState,mntPtLink,mntPtSourceNode,attributeNode,intoMountPath));
                            newTrees.add(getNextSearchSemanticModel(searchSemanticModelState,mntPtLink,mntPtSourceNode,attributeNode,intoMountPath));
                        }
                    }

                    if(allIntoTreePathsForMntPtSourceNode.size() > 0) {
                        System.out.println("add into tree paths");
                        for (List<DefaultLink> intoTreePath : allIntoTreePathsForMntPtSourceNode) {
                            ++count;
                            nextSemanticModelsForInDirectMappingPaths.add(getNextSearchSemanticModel(searchSemanticModelState,mntPtLink,mntPtSourceNode,attributeNode,intoTreePath));
                            newTrees.add(getNextSearchSemanticModel(searchSemanticModelState,mntPtLink,mntPtSourceNode,attributeNode,intoTreePath));
                        }
                    }

                    if(allTrianglePathsForMntPtSourceNode.size() > 0) {
                        System.out.println("add triangle paths");
                        for (List<DefaultLink> trianglePath : allTrianglePathsForMntPtSourceNode) {
                            ++count;
                            nextSemanticModelsForInDirectMappingPaths.add(getNextSearchSemanticModel(searchSemanticModelState,mntPtLink,mntPtSourceNode,attributeNode,trianglePath));
                            newTrees.add(getNextSearchSemanticModel(searchSemanticModelState,mntPtLink,mntPtSourceNode,attributeNode,trianglePath));
                        }
                    }
                }
            }
            /**add one type of paths, and generate different types of next search semantic models**/
        }
        System.out.println("count:" + count);
        return newTrees;
    }


    public static List<SemanticModel> mergeIntoTree(SemanticModel searchSemanticModelState,DirectedWeightedMultigraph<Node, DefaultLink> Gint,ColumnNode attributeNode,Boolean noDefaultLink,Set<InternalNode> internalNodesWithUseOntPaths, Boolean hasOntPaths) throws Exception {
        System.out.println("enter mergeIntoTree for adding only one column node to the current search semantic model state");
        System.out.println("enter mergeIntoTree and add "+attributeNode.getColumnName());
        int count = 0;

        Set<InternalNode> internalNodesOfSearchSemanticModelState = new HashSet<InternalNode>();
        Set<String> internalNodeIdsOfSearchSemanticModelState = new HashSet<String>();
        Map<String,Node> internalNodeIdWithInternalNode = new HashMap<String,Node>();
        List<DefaultLink> linksOfIntegrationGraph = new ArrayList<DefaultLink>();
        List<DefaultLink> linksOfSearchSemanticModelState = new ArrayList<DefaultLink>();
//        Map<Node, Set<Node>> SearchStateInternalnodesMappingIntegrationGraph = new HashMap<Node, Set<Node>>();
        Map<Node, Set<Node>> internalNodeInSearchStateWithNodeMappingsInIntegration = new HashMap<Node, Set<Node>>();
        SemanticModel initialSearchSemanticModelState = null;
//        SemanticModel MergeInitialStartSearchStateSM = null;
        SemanticModel mergeInitialSearchSemanticModelState = null;
        SemanticModel nextSearchState = null;
//        SemanticModel NextSearchStateSM = null;
        List<SemanticModel> newTrees = new LinkedList<SemanticModel>();

        //obtain all internal nodes of the current search semantic model state
        internalNodesOfSearchSemanticModelState = searchSemanticModelState.getInternalNodes();
        //obtain all internal node ids of the current search semantic model state
        for(InternalNode internalNode: internalNodesOfSearchSemanticModelState){
            internalNodeIdsOfSearchSemanticModelState.add(internalNode.getId());
            internalNodeIdWithInternalNode.put(internalNode.getId(),internalNode);
        }
        assert internalNodesOfSearchSemanticModelState.size() == searchSemanticModelState.getInternalNodes().size(): "internalNodesOfSearchSemanticModelState.size != internalNodeIdsOfSearchSemanticModelState.size";
        assert internalNodeIdWithInternalNode.size() == searchSemanticModelState.getInternalNodes().size(): "internalNodeIdWithInternalNode.size != internalNodeIdsOfSearchSemanticModelState.size";
        //obtain all links of the integration graph(Gint)
        linksOfIntegrationGraph = new ArrayList<DefaultLink>(Gint.edgeSet());
        //obtain all links of the current search semantic model state
        linksOfSearchSemanticModelState = new ArrayList<DefaultLink>(searchSemanticModelState.getGraph().edgeSet());

        //find all mapping internal nodes in the integration graph for all internal nodes in the current search semantic model
        for (InternalNode internal_node_search_state : internalNodesOfSearchSemanticModelState) {
            Set<Node> internalNodesMappingForEachInternalNodeOfSearchState = new HashSet<Node>();
            //obtain all internal nodes mappings in integration graph for each internal node in the initial search semantic model state
            for (Node internal_node_integration : Gint.vertexSet()) {
                if ((internal_node_integration instanceof InternalNode) && (internal_node_integration.getId().equals(internal_node_search_state.getId()))) {
                    internalNodesMappingForEachInternalNodeOfSearchState.add(internal_node_integration);
                }
            }
            //add all internal nodes mappings in integration graph into internalNodeInSearchStateWithNodeMappingsInIntegration
            internalNodeInSearchStateWithNodeMappingsInIntegration.put(internal_node_search_state, internalNodesMappingForEachInternalNodeOfSearchState);
        }
        assert internalNodeInSearchStateWithNodeMappingsInIntegration.size() == internalNodesOfSearchSemanticModelState.size(): "mapping nodes in integration graph is wrong";

        /**obtain root node or root nodes of the search semantic model state and obtain all mapping nodes for the root nodes**/
        Node root = null;
        List<Node> rootList = new ArrayList<Node>();
        Set<Node> rootMappingsList = new HashSet<Node>();
        root = getSemanticModelRoot(searchSemanticModelState);
        rootList = getSemanticModelRootList(searchSemanticModelState);
        //obtain the mapping nodes set for the root nodes of the initial search semantic model state
        for(Node rootNode: rootList){
            if(internalNodeInSearchStateWithNodeMappingsInIntegration.get(rootNode).size()>0)
                rootMappingsList.addAll(internalNodeInSearchStateWithNodeMappingsInIntegration.get(rootNode));
        }
        if((searchSemanticModelState.getGraph().vertexSet().size()>0) && (searchSemanticModelState.getGraph().edgeSet().size()>0)) {
            assert rootMappingsList.size() > 0 : "rootMappingsList.size <= 0";
//        System.out.println("rootMappingsList.size:" + rootMappingsList.size());
        }


        /**initial all connected paths list**/
        List<List<String>> allConnectedPathsUsingNodeIds;//save all connected paths using node ids
        List<List<Node>> allIntoMountConnectedPathsUsingNodes;//save all connected paths using nodes by connecting the current semantic model into class node with attribute node
        List<List<Node>> allIntoTreeConnectedPathsUsingNodes;//save all connected paths using nodes by connecting class node with attribute node into the current semantic model
        List<List<Node>> allTriangleTreeConnectedPathsUsingNodesForOneRoot;
        List<List<Node>> allTriangleMountConnectedPathsUsingNodesForOneRoot;
        List<List<Node>> allTriangleConnectedPathsUsingNodes;//save all connected paths using nodes by connecting class node with attribute node and the current semantic model with common ancestor class nodes



        /**loop all mntPts (that is, all class nodes with candidate semantic types for the added attribute node)
         * and find all connected paths to merge the mntPts and the current semantic model for generating all next
         * search semantic models**/

        /**obtain all semantic types (contains correct and candidate semantic types 2023/04/04, note that some correct semantic types are not in the integration graph) for the added attribute nodes**/
        Set<SemanticType> allSemanticTypesForAddedAttributeNode = new HashSet<SemanticType>();
//        if(getSemanticTypes(attributeNode,false,true,4).size()>0)
//            allSemanticTypesForAddedAttributeNode = getSemanticTypes(attributeNode,true,true,4);
        allSemanticTypesForAddedAttributeNode = getSemanticTypes(attributeNode,true,false,4);
        assert allSemanticTypesForAddedAttributeNode.size() > 0 && allSemanticTypesForAddedAttributeNode.size() < 6: "allSemanticTypesForAddedAttributeNode < 0 or allSemanticTypesForAddedAttributeNode > 5";

        /**mntPts save the links whose node has same semantic types with the added attribute node**/
        Set<DefaultLink> mntPts = new HashSet<DefaultLink>();
        Map<Node,Set<DefaultLink>> mntPtNodeWithMntPtLinks = new HashMap<Node,Set<DefaultLink>>();
        Set<String> mntPtsWithSourceNodeIdAndLinkUri = new HashSet<String>();//used to check the mntPt with same source node id and link uri
        //loop all semantic types in allSemanticTypesForAddedAttributeNode, and find all mntPts
        for (SemanticType semanticType : allSemanticTypesForAddedAttributeNode) {
            for (DefaultLink link : Gint.edgeSet()) {
                if ((link.getSource().getUri().equals(semanticType.getDomain().getUri())) && (link.getUri().equals(semanticType.getType().getUri())) && (!mntPtsWithSourceNodeIdAndLinkUri.contains(link.getSource().getId()+semanticType.getType().getUri().toString()))) {
                    mntPtsWithSourceNodeIdAndLinkUri.add(link.getSource().getId()+semanticType.getType().getUri().toString());
                    mntPts.add(link);
                }
            }
        }

        Set<DefaultLink> linksWithSameSourceNode = new HashSet<DefaultLink>();
        for(DefaultLink mntPtLink: mntPts){
            if(!mntPtNodeWithMntPtLinks.keySet().contains(mntPtLink.getSource())) {
                linksWithSameSourceNode = new HashSet<DefaultLink>();
                linksWithSameSourceNode.add(mntPtLink);
                mntPtNodeWithMntPtLinks.put(mntPtLink.getSource(), linksWithSameSourceNode);
            }
            else{
                linksWithSameSourceNode = mntPtNodeWithMntPtLinks.get(mntPtLink.getSource());
                linksWithSameSourceNode.add(mntPtLink);
                mntPtNodeWithMntPtLinks.put(mntPtLink.getSource(), linksWithSameSourceNode);
            }
        }

        int mntPtsNum = 0;
        for(Node mntPtNode: mntPtNodeWithMntPtLinks.keySet()){
            mntPtsNum = mntPtsNum + mntPtNodeWithMntPtLinks.get(mntPtNode).size();
        }
        assert mntPts.size() == mntPtsNum: "mntPts.size != mntPtsNum";


        Set<List<DefaultLink>> allThreeTypesPathsForMntPtSourceNode = new HashSet<List<DefaultLink>>();
        Set<List<DefaultLink>> allIntoMountPathsForMntPtSourceNode = new HashSet<List<DefaultLink>>();
        Set<List<DefaultLink>> allIntoTreePathsForMntPtSourceNode = new HashSet<List<DefaultLink>>();
        Set<List<DefaultLink>> allTrianglePathsForMntPtSourceNode = new HashSet<List<DefaultLink>>();

        /**find all paths (1.direct mapping; 2.intoMount, intoTree, triangle)**/
        int directMappingPaths = 0;
        int indirectMappingPaths = 1;
        Map<Integer,List<SemanticModel>> PathsTypeWithNextSemanticModels = new HashMap<Integer,List<SemanticModel>>();
//        PathsTypeWithNextSemanticModels.put(directMappingPaths,new ArrayList<SemanticModel>());
//        PathsTypeWithNextSemanticModels.put(indirectMappingPaths,new ArrayList<SemanticModel>());
        List<SemanticModel> nextSemanticModelsForDirectMappingPaths = new ArrayList<SemanticModel>();
        List<SemanticModel> nextSemanticModelsForInDirectMappingPaths = new ArrayList<SemanticModel>();
        Boolean pathWithDefaultLink = false;
        List<DefaultLink> neededConnectedPathUsingLinks = new ArrayList<DefaultLink>();
        Map<String,List<DefaultLink>> nodePairStringWithLinksInIntegrationGraph = new HashMap<String,List<DefaultLink>>();
        for(DefaultLink integrationLink: linksOfIntegrationGraph){
//            if(integrationLink.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink"))
//                continue;
            if(!nodePairStringWithLinksInIntegrationGraph.keySet().contains(integrationLink.getSource().getId()+integrationLink.getTarget().getId())){
                nodePairStringWithLinksInIntegrationGraph.put(integrationLink.getSource().getId()+integrationLink.getTarget().getId(),new ArrayList<DefaultLink>(Arrays.asList(integrationLink)));
            }
            else{
                List<DefaultLink> tempLinksWithSameNodePair = new ArrayList<DefaultLink>(nodePairStringWithLinksInIntegrationGraph.get(integrationLink.getSource().getId()+integrationLink.getTarget().getId()));
                tempLinksWithSameNodePair.add(integrationLink);
                nodePairStringWithLinksInIntegrationGraph.put(integrationLink.getSource().getId()+integrationLink.getTarget().getId(),tempLinksWithSameNodePair);
            }
        }
//        Map<String,List<DefaultLink>> nodePairStringWithLinksInSearchState = new HashMap<String,List<DefaultLink>>();
//        for(DefaultLink searchStateLink: linksOfSearchSemanticModelState){
//            if(!nodePairStringWithLinksInSearchState.keySet().contains(searchStateLink.getSource().getId()+searchStateLink.getTarget().getId())){
//                nodePairStringWithLinksInSearchState.put(searchStateLink.getSource().getId()+searchStateLink.getTarget().getId(),new ArrayList<DefaultLink>(Arrays.asList(searchStateLink)));
//            }
//            else{
//                List<DefaultLink> tempLinksWithSameNodePair = new ArrayList<DefaultLink>(nodePairStringWithLinksInSearchState.get(searchStateLink.getSource().getId()+searchStateLink.getTarget().getId()));
//                tempLinksWithSameNodePair.add(searchStateLink);
//                nodePairStringWithLinksInSearchState.put(searchStateLink.getSource().getId()+searchStateLink.getTarget().getId(),tempLinksWithSameNodePair);
//            }
//        }

        int linksNumInIntegrationGraph = 0;
        for(String nodePairString: nodePairStringWithLinksInIntegrationGraph.keySet()){
            linksNumInIntegrationGraph = linksNumInIntegrationGraph + nodePairStringWithLinksInIntegrationGraph.get(nodePairString).size();
        }
        assert linksOfIntegrationGraph.size() == linksNumInIntegrationGraph: "linksOfIntegrationGraph.size != linksNumInIntegrationGraph";
//        if(!hasOntPaths)
//            assert linksOfIntegrationGraph.size() == linksNumInIntegrationGraph: "linksOfIntegrationGraph.size != linksNumInIntegrationGraph";

        Map<Node,Set<List<DefaultLink>>> mntPtSourceNodeWithThreeTypesPathsUsingLinks = new HashMap<Node,Set<List<DefaultLink>>>();
        Boolean isNeededConnectedPath = true;
//        Map<String,List<Integer>> internalNodeIdWithDepthListInSearchState = new HashMap<String,List<Integer>>();//save the internal node ids in the search semantic model state with their corresponding depths
//        List<String> sourceTargetNodePairStringInSearchState = new ArrayList<String>();
//        List<Integer> internalNodeDepth = new ArrayList<Integer>();
//        for(int i = 0; i < internalNodesOfSearchSemanticModelState.size(); i++){
//            if(rootList.contains(internalNodesOfSearchSemanticModelState.toArray(new InternalNode[0])[i]))
//                internalNodeIdWithDepthListInSearchState.put(internalNodesOfSearchSemanticModelState.toArray(new InternalNode[0])[i].getId(),new ArrayList<Integer>(Arrays.asList(1)));
//            for(int j = 0; j < internalNodesOfSearchSemanticModelState.size(); j++){
//                if(j==i)
//                    continue;
//                FindPaths.connectedPathsNode = new ArrayList<List<Node>>();
//                findAllPathNode(linksOfSearchSemanticModelState,(internalNodesOfSearchSemanticModelState.toArray(new InternalNode[0])[i]).getId(),(internalNodesOfSearchSemanticModelState.toArray(new InternalNode[0])[j]).getId(),100);
//                if(FindPaths.connectedPathsNode.size()>0){
//                    if(rootList.contains(internalNodesOfSearchSemanticModelState.toArray(new InternalNode[0])[i])){
//                        internalNodeDepth = new ArrayList<Integer>();
//                        for(List<Node> pathUsingNode: FindPaths.connectedPathsNode){
//                            internalNodeDepth.add(pathUsingNode.size());
//                        }
//                        internalNodeIdWithDepthListInSearchState.put((internalNodesOfSearchSemanticModelState.toArray(new InternalNode[0])[j]).getId(),internalNodeDepth);
//                    }
//                    sourceTargetNodePairStringInSearchState.add((internalNodesOfSearchSemanticModelState.toArray(new InternalNode[0])[i]).getId()+(internalNodesOfSearchSemanticModelState.toArray(new InternalNode[0])[j]).getId());
//                }
//            }
//        }
//        System.out.println("internalNodeIdWithDepthListInSearchState:" + internalNodeIdWithDepthListInSearchState);
//        System.out.println("sourceTargetNodePairStringInSearchState:" + sourceTargetNodePairStringInSearchState);
//        System.out.println("internalNodesOfSearchSemanticModelState.size:" + internalNodesOfSearchSemanticModelState.size());


//        Boolean isSteinerNodeUsingOntInternalNodes;
//        if(attributeNode.getUseOntInternalNodes())
//            isSteinerNodeUsingOntInternalNodes = true;
//        else
//            isSteinerNodeUsingOntInternalNodes = false;

        /**loop all mntPts in mntPts set**/
        for (Node mntPtSourceNode : mntPtNodeWithMntPtLinks.keySet()) {
            Boolean hasTrianglePathForSteinerNodeWithOntPaths = false;
            Set<InternalNode> temp_internalNodesWithUseOntPaths = new HashSet<InternalNode>(internalNodesWithUseOntPaths);
            if(!(((InternalNode) mntPtSourceNode).getUseOntPaths())){
                noDefaultLink = true;
            }
            else{
                temp_internalNodesWithUseOntPaths.remove(mntPtSourceNode);
                noDefaultLink = false;
            }
            /**save three types paths for a mntPtSourceNod, add nodes and links into the current semantic model using these paths**/
            allThreeTypesPathsForMntPtSourceNode = new HashSet<List<DefaultLink>>();
            allIntoMountPathsForMntPtSourceNode = new HashSet<List<DefaultLink>>();
            allIntoTreePathsForMntPtSourceNode = new HashSet<List<DefaultLink>>();
            allTrianglePathsForMntPtSourceNode = new HashSet<List<DefaultLink>>();

            boolean isMntPtSourceNodeInSemanticModel = false;//judge the mntPt source node whether in the semantic model tree
            boolean isMntPtSourceNodeIsRootNode = false;//judge the mntPt source node whether is the root node of the semantic model tree

            /**一.direct mapping if mntPt source node in the search semantic model state**/
            //if the mntPt source node in the search semantic model state, we need to add the target nodes and links in mntPtNodeWithMntPtLinks.get(mntPtSourceNode)
            if (internalNodeIdsOfSearchSemanticModelState.contains(mntPtSourceNode.getId())) {
                //obtain the mapping node in initial search semantic model state for the mntPtSourceNode
                Node mntPtSourceNodeMapping = internalNodeIdWithInternalNode.get(mntPtSourceNode.getId());
//                loop all mntPt links in mntPtNodeWithMntPtLinks.get(mntPtSourceNode)
                for (DefaultLink mntPtLink : mntPtNodeWithMntPtLinks.get(mntPtSourceNode)) {
                    assert mntPtSourceNode.equals(mntPtLink.getSource()) : "mntPtSourceNode != mntPtLink.sourceNode";
                    String mntPtLinkId = LinkIdFactory.getLinkId(mntPtLink.getUri(), mntPtSourceNode.getId(), attributeNode.getId());
                    LabeledLink labeledMntPtLink = new DataPropertyLink(mntPtLinkId, new Label(mntPtLink.getUri()));
                    initialSearchSemanticModelState = searchSemanticModelState.clone();
                    //add the added attribute node
                    initialSearchSemanticModelState.getGraph().addVertex(attributeNode);
                    //add link
                    initialSearchSemanticModelState.getGraph().addEdge(mntPtSourceNodeMapping, attributeNode, labeledMntPtLink);
                    assert initialSearchSemanticModelState.getGraph().vertexSet().size() == (searchSemanticModelState.getGraph().vertexSet().size() + 1) : "not add the added attribute node based on direct paths";
                    assert initialSearchSemanticModelState.getGraph().edgeSet().size() == (searchSemanticModelState.getGraph().edgeSet().size() + 1) : "not add the added mntPt link based on direct paths";
                    nextSemanticModelsForDirectMappingPaths.add(initialSearchSemanticModelState);
                    newTrees.add(initialSearchSemanticModelState);
                    ++count;
                }

//                MergeIntoTreenumber++;
//
//                GraphVizUtil.exportSemanticModelToGraphviz(InitialStartSearchStateSM, GraphVizLabelType.LocalId,
//                        GraphVizLabelType.LocalUri, true, true, Params.ROOT_DIR + "next-state-graph/" + "next_state_Direct" + MergeIntoTreenumber + ".graph.json" + ".dot");
//
//                tempSemanticModelList = new ArrayList<SemanticModel>(WithOrWithoutDefaultlink.get(WithDefaultlink));
//                tempSemanticModelList.add(InitialStartSearchStateSM);
//                WithOrWithoutDefaultlink.put(WithDefaultlink,tempSemanticModelList);
//
            }

            /**二.intoMount, intoTree, triangle**/
            //if mntPt source node is not in search semantic model state, we need to find all three types paths,
            //and obtain all next search semantic models based on these paths
            else {
                //initial these lists for each mntPtSourceNode that is not in the initial search semantic model
                allIntoMountConnectedPathsUsingNodes = new ArrayList<List<Node>>();//intoMount paths for each mntPt source node
                allIntoTreeConnectedPathsUsingNodes = new ArrayList<List<Node>>();//intoTree paths for each mntPt source node
                allTriangleTreeConnectedPathsUsingNodesForOneRoot = new ArrayList<List<Node>>();
                allTriangleMountConnectedPathsUsingNodesForOneRoot = new ArrayList<List<Node>>();
                allTriangleConnectedPathsUsingNodes = new ArrayList<List<Node>>();//triangle paths for each mntPt source node
                Set<DefaultLink> tempLinksBetweenSourceAndTarget = null;
                List<DefaultLink> connectedPathUsingLinksWithoutDefaultLink = new ArrayList<DefaultLink>();
                List<List<DefaultLink>> allNodePairLinksList = new ArrayList<List<DefaultLink>>();
                List<List<List<DefaultLink>>> allNodePairLinksListBetweenTreeAndMntPtWithCommonAncestorNode = new ArrayList<List<List<DefaultLink>>>();
                List<List<DefaultLink>> allNeededConnectedPathsUsingLinksForOnePathUsingNodes = new ArrayList<List<DefaultLink>>();
                List<List<DefaultLink>> allNeededConnectedPathsUsingLinksForOneTreePathUsingNodes = new ArrayList<List<DefaultLink>>();
                List<List<DefaultLink>> allNeededConnectedPathsUsingLinksForOneMountPathUsingNodes = new ArrayList<List<DefaultLink>>();


                /**1.find all intoMount paths by adding the initial search semantic model state tree into the mntPt source node**/

                /**① find all connected paths (using nodes) that view the mntPt source node as the source, the root node of the initial search semantic model state tree as target
                 * the largest path is 3: represents there is a maximum of one node between source and target**/

                //obtain the mapping nodes for the root nodes in the initial search semantic model state
                for (Node rootMappingNode : rootMappingsList) {
                    //find all connected paths from mntPtSourceNode to the mapping root node
                    FindPaths.connectedPathsNode = new ArrayList<List<Node>>();
                    if(hasOntPaths) {
                        FindPaths.useInternalNodesWithOntPaths = 0;
                        findAllPathNode(linksOfIntegrationGraph, mntPtSourceNode.getId(), rootMappingNode.getId(), 3, mntPtSourceNode);
                    }
                    else
                        findAllPathNode(linksOfIntegrationGraph, mntPtSourceNode.getId(), rootMappingNode.getId(), 3);
                    allIntoMountConnectedPathsUsingNodes.addAll(FindPaths.connectedPathsNode);
                }
                System.out.println("allIntoMountConnectedPathsUsingNodes before:" + allIntoMountConnectedPathsUsingNodes.size());



                //loop all connected paths using nodes and obtain the needed connected paths using links
                for (List<Node> connected_path_intoMount : allIntoMountConnectedPathsUsingNodes) {
                    //if there are two same nodes in the path, we need to ignore this path because it appears a circle
                    Set<Node> judgeSet = new HashSet<Node>(connected_path_intoMount);
                    if(judgeSet.size()!=connected_path_intoMount.size())
                        continue;
                    allNeededConnectedPathsUsingLinksForOnePathUsingNodes = new ArrayList<List<DefaultLink>>();
                    isNeededConnectedPath = true;
                    neededConnectedPathUsingLinks = new ArrayList<DefaultLink>();
                    tempLinksBetweenSourceAndTarget = new HashSet<DefaultLink>();
                    allNodePairLinksList = new ArrayList<List<DefaultLink>>();
//                    eachPathAddedLinks = new ArrayList<DefaultLink>();
//                    eachPathAddedLinksWithoutDefaultlink = new ArrayList<DefaultLink>();
                    //save all links for the connected_path_intoMount
                    for (int i = 0; i < connected_path_intoMount.size() - 1; i++) {
                        /**avoid circle, we need to check whether the node (except tree-root node) in the connected_path_intoMount exists in initial search semantic model state (internal nodes)**/
                        if (internalNodeIdWithInternalNode.keySet().contains(connected_path_intoMount.get(i).getId())) {
//                            allNodePairLinksList = new ArrayList<List<DefaultLink>>();
                            isNeededConnectedPath = false;
                            break;
                        }
                        //the connected_path_intoMount doesn't have circles, we need to get the connected path using links
                        if(nodePairStringWithLinksInIntegrationGraph.containsKey(connected_path_intoMount.get(i).getId() + connected_path_intoMount.get(i + 1).getId()))
                            allNodePairLinksList.add(nodePairStringWithLinksInIntegrationGraph.get(connected_path_intoMount.get(i).getId() + connected_path_intoMount.get(i + 1).getId()));
                        else {
                            isNeededConnectedPath = false;
                            break;
                        }
                    }
                    if (!isNeededConnectedPath)
                        continue;
                    if (allNodePairLinksList.size() > 0) {
                        //obtain all needed connected paths for the current connected_path_intoMount
                        allNeededConnectedPathsUsingLinksForOnePathUsingNodes = descartesRecursive(allNodePairLinksList);
                    }
                    assert allNeededConnectedPathsUsingLinksForOnePathUsingNodes.size() > 0 : "allNeededConnectedPathsUsingLinksForOnePathUsingNodes.size <= 0";
                    for (List<DefaultLink> pathUsingLinks : allNeededConnectedPathsUsingLinksForOnePathUsingNodes) {
                        assert pathUsingLinks.size() == connected_path_intoMount.size() - 1 : "into mount pathUsingLinks size is wrong";
                        if (noDefaultLink) {
                            pathWithDefaultLink = false;//judge if the needed connected_path_intoMount has default link
                            for (DefaultLink link : pathUsingLinks) {
                                if (link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink")) {
                                    pathWithDefaultLink = true;
                                    break;
                                }
                            }
                            if (!pathWithDefaultLink) {
                                allIntoMountPathsForMntPtSourceNode.add(pathUsingLinks);
                            }
                        } else {
                            allIntoMountPathsForMntPtSourceNode.add(pathUsingLinks);
                        }
                    }
                }
                if((((InternalNode) mntPtSourceNode).getUseOntPaths()) && (allIntoMountPathsForMntPtSourceNode.size()>0))
                    allThreeTypesPathsForMntPtSourceNode.add(new ArrayList<List<DefaultLink>>(allIntoMountPathsForMntPtSourceNode).get(0));
                else
                    allThreeTypesPathsForMntPtSourceNode.addAll(allIntoMountPathsForMntPtSourceNode);//add all intoMountPaths for a mntPtSourceNode into allThreeTypesPathsForMntPtSourceNode, don't forget add it into mntPtSourceNodeWithThreeTypesPathsUsingLinks map when adding all three types paths
                System.out.println("add allIntoMountPathsForMntPtSourceNode, allThreeTypesPathsForMntPtSourceNode.size:" + allThreeTypesPathsForMntPtSourceNode.size());

                /**② find all connected paths (using nodes) that view the nodes of the initial search semantic model state tree as sources,
                 * the mntPt source node as the target, if mntPtSourceNode is not in the initial search semantic model state
                 * the largest path is 3: represents there is a maximum of one node between source and target**/
                //check whether mntPtSourceNode exists in the initial search semantic model state
                if (internalNodeIdsOfSearchSemanticModelState.contains(mntPtSourceNode.getId())) {
                    continue;
                } else {
                    //loop all internal nodes in the initial search semantic model state
                    for (Node internalNode : internalNodesOfSearchSemanticModelState) {
                        //loop all internal node mappings in the integration graph for each internal node in the initial search semantic model state
                        for (Node internalMappingNodeForOneInternalNodeInSearchState : internalNodeInSearchStateWithNodeMappingsInIntegration.get(internalNode)) {
                            //find all connected paths from mapping nodes of the initial search semantic model state to the mntPt source node
                            FindPaths.connectedPathsNode = new ArrayList<List<Node>>();
                            if(hasOntPaths) {
                                FindPaths.useInternalNodesWithOntPaths = 0;
                                findAllPathNode(linksOfIntegrationGraph, internalMappingNodeForOneInternalNodeInSearchState.getId(), mntPtSourceNode.getId(), 3, mntPtSourceNode);
                            }
                            else
                                findAllPathNode(linksOfIntegrationGraph, internalMappingNodeForOneInternalNodeInSearchState.getId(), mntPtSourceNode.getId(), 3);
                            allIntoTreeConnectedPathsUsingNodes.addAll(FindPaths.connectedPathsNode);
                        }
                    }
                }
                System.out.println("allIntoTreeConnectedPathsUsingNodes before:" + allIntoTreeConnectedPathsUsingNodes.size());

                //save connected links between source and target into the temporary defaultLinks set
//                Set<DefaultLink> temp_nodepair_links_intotree = null;//tempLinksBetweenSourceAndTarget
                for (List<Node> connected_path_intoTree : allIntoTreeConnectedPathsUsingNodes) {

                    //if there are two same nodes in the path, we need to ignore this path because it appears a circle
                    Set<Node> judgeSet = new HashSet<Node>(connected_path_intoTree);
                    if(judgeSet.size()!=connected_path_intoTree.size())
                        continue;
                    allNeededConnectedPathsUsingLinksForOnePathUsingNodes = new ArrayList<List<DefaultLink>>();
                    isNeededConnectedPath = true;
                    neededConnectedPathUsingLinks = new ArrayList<DefaultLink>();
                    tempLinksBetweenSourceAndTarget = new HashSet<DefaultLink>();
                    allNodePairLinksList = new ArrayList<List<DefaultLink>>();

                    //save all links for the connected_path_intoTree
                    for (int i = 0; i < connected_path_intoTree.size() - 1; i++) {
//                        temp_nodepair_links_intotree = new HashSet<DefaultLink>();
                        /**"very important" 依次遍历path中的node pair(1-2,2-3,3-4...)
                         * 检查当前node pair是否在tree中有路径 如果有则不添加node pair之间对应到integration graph上的link信息
                         * 如果没有则添加对应到integration graph上的link信息**/

                        /**if the initial search semantic model state has the node i and i+1 (that represents there is a link
                         * between node i and i+1 in the initial search semantic model state), and there is only one link between the node i and i+1,
                         * we don't need to add this link; else we need to save all possible links between the node i and i+1 into the allNodePairLinksList**/

                        /**check if there is a circle while adding the links between node i and i+1**/
                        if ((internalNodeIdWithInternalNode.keySet().contains(connected_path_intoTree.get(i).getId())) && (internalNodeIdWithInternalNode.keySet().contains(connected_path_intoTree.get(i + 1).getId()))) {
                            if(nodePairStringWithLinksInIntegrationGraph.containsKey(connected_path_intoTree.get(i).getId() + connected_path_intoTree.get(i + 1).getId())){
                                if (nodePairStringWithLinksInIntegrationGraph.get(connected_path_intoTree.get(i).getId() + connected_path_intoTree.get(i + 1).getId()).size() == 1)
                                    continue;
                                else if (nodePairStringWithLinksInIntegrationGraph.get(connected_path_intoTree.get(i).getId() + connected_path_intoTree.get(i + 1).getId()).size() > 1)
                                    allNodePairLinksList.add(nodePairStringWithLinksInIntegrationGraph.get(connected_path_intoTree.get(i).getId() + connected_path_intoTree.get(i + 1).getId()));
                                else {
                                    isNeededConnectedPath = false;
                                    break;
                                }
                            }
                            else{
                                isNeededConnectedPath = false;
                                break;
                            }
                        }
                        //check if node i+1 exists in the initial search semantic model, avoid the circle
                        else if ((!(internalNodeIdWithInternalNode.keySet().contains(connected_path_intoTree.get(i).getId()))) && (internalNodeIdWithInternalNode.keySet().contains(connected_path_intoTree.get(i + 1).getId()))) {
                            isNeededConnectedPath = false;
                            break;
                        } else {
                            if(nodePairStringWithLinksInIntegrationGraph.containsKey(connected_path_intoTree.get(i).getId() + connected_path_intoTree.get(i + 1).getId())) {
                                allNodePairLinksList.add(nodePairStringWithLinksInIntegrationGraph.get(connected_path_intoTree.get(i).getId() + connected_path_intoTree.get(i + 1).getId()));
                            }
                            else{
                                isNeededConnectedPath = false;
                                break;
                            }
                        }

                        /**如果path.size()>2 检查当前pathnode的nodes(除第一个node外)是否存在于StartSearchState的InternalNodes中  避免出现环**/
                    }
                    if (!isNeededConnectedPath)
                        continue;
                    if (allNodePairLinksList.size() > 0) {
                        //obtain all needed connected paths for the current connected_path_intoTree
                        allNeededConnectedPathsUsingLinksForOnePathUsingNodes = descartesRecursive(allNodePairLinksList);
                    }
                    assert allNeededConnectedPathsUsingLinksForOnePathUsingNodes.size() > 0 : "allNeededConnectedPathsUsingLinksForOnePathUsingNodes.size <= 0";
                    for (List<DefaultLink> pathUsingLinks : allNeededConnectedPathsUsingLinksForOnePathUsingNodes) {
                        System.out.println("pathUsingLinks.size:" + pathUsingLinks.size());
                        System.out.println("connected_path_intoTree.size:" + connected_path_intoTree.size());

                        assert pathUsingLinks.size() > 0 : "into tree pathUsingLinks size is wrong";
                        if (noDefaultLink) {
                            pathWithDefaultLink = false;//judge if the needed connected_path_intoMount has default link
                            for (DefaultLink link : pathUsingLinks) {
                                if (link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink")) {
                                    pathWithDefaultLink = true;
                                    break;
                                }
                            }
                            if (!pathWithDefaultLink) {
                                allIntoTreePathsForMntPtSourceNode.add(pathUsingLinks);
                            }
                        } else {
                            allIntoTreePathsForMntPtSourceNode.add(pathUsingLinks);
                        }
                    }
                }
                if((((InternalNode) mntPtSourceNode).getUseOntPaths()) && (allIntoTreePathsForMntPtSourceNode.size()>0))
                    allThreeTypesPathsForMntPtSourceNode.add(new ArrayList<List<DefaultLink>>(allIntoTreePathsForMntPtSourceNode).get(0));
                else
                    allThreeTypesPathsForMntPtSourceNode.addAll(allIntoTreePathsForMntPtSourceNode);//add all intoMountPaths for a mntPtSourceNode into allThreeTypesPathsForMntPtSourceNode, don't forget add it into mntPtSourceNodeWithThreeTypesPathsUsingLinks map when adding all three types paths
                System.out.println("add allIntoTreePathsForMntPtSourceNode, allThreeTypesPathsForMntPtSourceNode.size:" + allThreeTypesPathsForMntPtSourceNode.size());

                /**③ find all connected paths (using nodes) that connect the mntPt source node and the root node of the initial
                 * search semantic model state using the ancestor nodes
                 * the largest path is 3: represents there is a maximum of one node between source and target**/
                //find the common ancestor nodes for the mntPt source node and the root node of the initial search
                //semantic model state, we only find the ancestor nodes with depth 1 currently
                Set<Node> commonAncestorNodes = new HashSet<Node>();
                for (Node rootMappingNode : rootMappingsList) {
//                    allTriangleTreeConnectedPathsUsingNodesForOneRoot = new ArrayList<List<Node>>();
//                    allTriangleMountConnectedPathsUsingNodesForOneRoot = new ArrayList<List<Node>>();

//                    commonAncestorNodes = getCommonAncestorNodes(mntPtSourceNode,rootMappingNode,3,attributeNode);
                    commonAncestorNodes = getCommonAncestorNodes(mntPtSourceNode,rootMappingNode,3,hasOntPaths);

//                    commonAncestorNodes = new HashSet<Node>();
//                    for (Node mntPtAncestorNode : mntPtSourceNode.getSourceNodes()) {
//                        if (internalNodeIdsOfSearchSemanticModelState.contains(mntPtAncestorNode.getId()))
//                            continue;
//                        if (rootMappingNode.getSourceNodes().contains(mntPtAncestorNode)) {
//                            commonAncestorNodes.add(mntPtAncestorNode);
//                        }
//                    }
                    System.out.println(rootMappingNode.getId() + " commonAncestorNodes.size:" + commonAncestorNodes.size());
                    //loop the ancestor node in commonAncestorNodes, and find the paths from the ancestor node to the root of the initial search semantic model state and mntPtSourceNode
                    for (Node commonAncestorNode : commonAncestorNodes) {
                        allTriangleTreeConnectedPathsUsingNodesForOneRoot = new ArrayList<List<Node>>();
                        allTriangleMountConnectedPathsUsingNodesForOneRoot = new ArrayList<List<Node>>();
                        //view the common ancestor node as source node, one of the root in the initial search semantic model as the target node
                        FindPaths.connectedPathsNode = new ArrayList<List<Node>>();
                        if(hasOntPaths) {
                            FindPaths.useInternalNodesWithOntPaths = 0;
                            findAllPathNode(linksOfIntegrationGraph, commonAncestorNode.getId(), rootMappingNode.getId(), 4, mntPtSourceNode);
                        }
                        else
                            findAllPathNode(linksOfIntegrationGraph, commonAncestorNode.getId(), rootMappingNode.getId(), 4);
                        for(List<Node> tempPathNodes: FindPaths.connectedPathsNode){
                            Set<Node> intersection = new HashSet<Node>(temp_internalNodesWithUseOntPaths);
                            intersection.retainAll(tempPathNodes);
                            if(intersection.size()==0)
                                allTriangleTreeConnectedPathsUsingNodesForOneRoot.add(tempPathNodes);
                        }
//                        allTriangleTreeConnectedPathsUsingNodesForOneRoot.addAll(FindPaths.connectedPathsNode);
                        if(allTriangleTreeConnectedPathsUsingNodesForOneRoot.size() == 0)
                            continue;

                        //view the common ancestor node as source node, mntPt source node as the target node
                        FindPaths.connectedPathsNode = new ArrayList<List<Node>>();
                        if(hasOntPaths) {
                            FindPaths.useInternalNodesWithOntPaths = 0;
                            findAllPathNode(linksOfIntegrationGraph, commonAncestorNode.getId(), mntPtSourceNode.getId(), 4, mntPtSourceNode);
                        }
                        else
                            findAllPathNode(linksOfIntegrationGraph, commonAncestorNode.getId(), mntPtSourceNode.getId(), 4);
                        for(List<Node> tempPathNodes: FindPaths.connectedPathsNode){
                            Set<Node> intersection = new HashSet<Node>(temp_internalNodesWithUseOntPaths);
                            intersection.retainAll(tempPathNodes);
                            if(intersection.size()==0)
                                allTriangleMountConnectedPathsUsingNodesForOneRoot.add(tempPathNodes);
                        }
//                        allTriangleMountConnectedPathsUsingNodesForOneRoot.addAll(FindPaths.connectedPathsNode);
                        if(allTriangleMountConnectedPathsUsingNodesForOneRoot.size() == 0)
                            continue;

                        //loop all connected_path_triangleTree
                        for (List<Node> connected_path_triangleTree : allTriangleTreeConnectedPathsUsingNodesForOneRoot) {
                            //if there are two same nodes in the path, we need to ignore this path because it appears a circle
                            Set<Node> judgeSet = new HashSet<Node>(connected_path_triangleTree);
                            if(judgeSet.size()!=connected_path_triangleTree.size())
                                continue;
                            allNeededConnectedPathsUsingLinksForOneTreePathUsingNodes = new ArrayList<List<DefaultLink>>();
                            isNeededConnectedPath = true;
                            allNodePairLinksList = new ArrayList<List<DefaultLink>>();
                            for (int i = 0; i < connected_path_triangleTree.size() - 1; i++) {
                                /**avoid circle, we need to check whether the node (except tree-root node) in the connected_path_triangleTree exists in initial search semantic model state (internal nodes)**/
                                if (internalNodeIdWithInternalNode.keySet().contains(connected_path_triangleTree.get(i).getId())) {
                                    // allNodePairLinksList = new ArrayList<List<DefaultLink>>();
                                    isNeededConnectedPath = false;
                                    break;
                                }
                                //the connected_path_triangleTree doesn't have circles, we need to get the connected path using links
                                if(nodePairStringWithLinksInIntegrationGraph.containsKey(connected_path_triangleTree.get(i).getId() + connected_path_triangleTree.get(i + 1).getId())) {
                                    allNodePairLinksList.add(nodePairStringWithLinksInIntegrationGraph.get(connected_path_triangleTree.get(i).getId() + connected_path_triangleTree.get(i + 1).getId()));
                                }
                                else{
                                    isNeededConnectedPath = false;
                                    break;
                                }
                            }
                            if (!isNeededConnectedPath)
                                continue;
                            if (allNodePairLinksList.size() > 0) {
                                //obtain all needed connected paths for the current connected_path_triangleTree
                                allNeededConnectedPathsUsingLinksForOneTreePathUsingNodes = descartesRecursive(allNodePairLinksList);
                            }
                            assert allNeededConnectedPathsUsingLinksForOneTreePathUsingNodes.size() > 0 : "allNeededConnectedPathsUsingLinksForOneTreePathUsingNodes.size <= 0";

                            //loop all connected_path_triangleMount
                            for (List<Node> connected_path_triangleMount : allTriangleMountConnectedPathsUsingNodesForOneRoot) {
                                if(connected_path_triangleMount.size() > (6-connected_path_triangleTree.size()))
                                    continue;

                                //if there are two same nodes in the path, we need to ignore this path because it appears a circle
                                judgeSet = new HashSet<Node>(connected_path_triangleMount);
                                if(judgeSet.size()!=connected_path_triangleMount.size())
                                    continue;

                                List<Node> intersection = new ArrayList<Node>(connected_path_triangleTree);
                                intersection.retainAll(connected_path_triangleMount);
                                if (intersection.size() > 1)//there are two or more same nodes in the tree and the mntPt
                                    continue;

                                allNeededConnectedPathsUsingLinksForOnePathUsingNodes = new ArrayList<List<DefaultLink>>();
                                allNeededConnectedPathsUsingLinksForOneMountPathUsingNodes = new ArrayList<List<DefaultLink>>();
                                isNeededConnectedPath = true;
                                allNodePairLinksList = new ArrayList<List<DefaultLink>>();
                                allNodePairLinksListBetweenTreeAndMntPtWithCommonAncestorNode = new ArrayList<List<List<DefaultLink>>>();

                                for (int i = 0; i < connected_path_triangleMount.size() - 1; i++) {
                                    /**avoid circle, we need to check whether the node (except tree-root node) in the connected_path_triangleMount exists in initial search semantic model state (internal nodes)**/
                                    if (internalNodeIdWithInternalNode.keySet().contains(connected_path_triangleMount.get(i).getId())) {
                                        // allNodePairLinksList = new ArrayList<List<DefaultLink>>();
                                        isNeededConnectedPath = false;
                                        break;
                                    }
                                    //the connected_path_triangleMount doesn't have circles, we need to get the connected path using links
                                    if(nodePairStringWithLinksInIntegrationGraph.containsKey(connected_path_triangleMount.get(i).getId() + connected_path_triangleMount.get(i + 1).getId())) {
                                        allNodePairLinksList.add(nodePairStringWithLinksInIntegrationGraph.get(connected_path_triangleMount.get(i).getId() + connected_path_triangleMount.get(i + 1).getId()));
                                    }
                                    else{
                                        isNeededConnectedPath = false;
                                        break;
                                    }
                                }
                                if (!isNeededConnectedPath)
                                    continue;
                                if (allNodePairLinksList.size() > 0) {
                                    //obtain all needed connected paths for the current connected_path_triangleMount
                                    allNeededConnectedPathsUsingLinksForOneMountPathUsingNodes = descartesRecursive(allNodePairLinksList);
                                }
                                assert allNeededConnectedPathsUsingLinksForOneMountPathUsingNodes.size() > 0 : "allNeededConnectedPathsUsingLinksForOneMountPathUsingNodes.size <= 0";

                                allNodePairLinksListBetweenTreeAndMntPtWithCommonAncestorNode.add(allNeededConnectedPathsUsingLinksForOneTreePathUsingNodes);
                                allNodePairLinksListBetweenTreeAndMntPtWithCommonAncestorNode.add(allNeededConnectedPathsUsingLinksForOneMountPathUsingNodes);
                                assert allNodePairLinksListBetweenTreeAndMntPtWithCommonAncestorNode.size() > 1 : "allNodePairLinksListBetweenTreeAndMntPtWithCommonAncestorNode.size <= 1";

                                allNeededConnectedPathsUsingLinksForOnePathUsingNodes = descartesRecursiveForDoubleList(allNodePairLinksListBetweenTreeAndMntPtWithCommonAncestorNode);

                                for (List<DefaultLink> pathUsingLinks : allNeededConnectedPathsUsingLinksForOnePathUsingNodes) {
                                    assert pathUsingLinks.size() == connected_path_triangleTree.size() + connected_path_triangleMount.size() - 2 : "triangle pathUsingLinks size is wrong";
                                    if (noDefaultLink) {
                                        pathWithDefaultLink = false;//judge if the needed connected_path_triangle has default link
                                        for (DefaultLink link : pathUsingLinks) {
                                            if (link.getUri().toString().equals("http://isi.edu/integration/karma/dev#defaultLink")) {
                                                pathWithDefaultLink = true;
                                                break;
                                            }
                                        }
                                        if (!pathWithDefaultLink) {
                                            allTrianglePathsForMntPtSourceNode.add(pathUsingLinks);
                                        }
                                    } else {
                                        if(((InternalNode) mntPtSourceNode).getUseOntPaths()){
                                            allTrianglePathsForMntPtSourceNode.add(pathUsingLinks);
                                            hasTrianglePathForSteinerNodeWithOntPaths = true;
                                            break;
                                        }
                                        allTrianglePathsForMntPtSourceNode.add(pathUsingLinks);
                                    }
                                }
                                if((((InternalNode) mntPtSourceNode).getUseOntPaths()) && (hasTrianglePathForSteinerNodeWithOntPaths))
                                    break;
                            }
                            if((((InternalNode) mntPtSourceNode).getUseOntPaths()) && (hasTrianglePathForSteinerNodeWithOntPaths))
                                break;
                        }
                        if((((InternalNode) mntPtSourceNode).getUseOntPaths()) && (hasTrianglePathForSteinerNodeWithOntPaths))
                            break;
                    }
                    if((((InternalNode) mntPtSourceNode).getUseOntPaths()) && (hasTrianglePathForSteinerNodeWithOntPaths))
                        break;
                }
                allThreeTypesPathsForMntPtSourceNode.addAll(allTrianglePathsForMntPtSourceNode);//add all trianglePaths for a mntPtSourceNode into allThreeTypesPathsForMntPtSourceNode, don't forget add it into mntPtSourceNodeWithThreeTypesPathsUsingLinks map when adding all three types paths
                System.out.println("add allTrianglePathsForMntPtSourceNode, allThreeTypesPathsForMntPtSourceNode.size:" + allThreeTypesPathsForMntPtSourceNode.size());
                if(((InternalNode) mntPtSourceNode).getUseOntPaths())
                    assert allThreeTypesPathsForMntPtSourceNode.size() <= 3: "allThreeTypesPathsForMntPtSourceNode.size > 3";

            }
            /**二.intoMount, intoTree, triangle**/

            /**add one type of paths, and generate different types of next search semantic models**/
            //loop and add the mntPt links for the mntPt source node
//            if ((allIntoMountPathsForMntPtSourceNode.size() > 0) || (allIntoTreePathsForMntPtSourceNode.size() > 0) || (allTrianglePathsForMntPtSourceNode.size() > 0)){
//                for (DefaultLink mntPtLink : mntPtNodeWithMntPtLinks.get(mntPtSourceNode)) {
//                    //initial the mntPt link
//                    String mntPtLinkId = LinkIdFactory.getLinkId(mntPtLink.getUri(), mntPtSourceNode.getId(), attributeNode.getId());
//                    LabeledLink mntPtDataLink = new DataPropertyLink(mntPtLinkId, new Label(mntPtLink.getUri()));
//
//                    //add mntPtSourceNode and attributeNode
//                    mergeInitialSearchSemanticModelState = searchSemanticModelState.clone();
//                    mergeInitialSearchSemanticModelState.getGraph().addVertex(mntPtSourceNode);
//                    mergeInitialSearchSemanticModelState.getGraph().addVertex(attributeNode);
//                    mergeInitialSearchSemanticModelState.getGraph().addEdge(mntPtSourceNode, attributeNode, mntPtDataLink);
//
//                    /**loop and add different types of the paths**/
//                    if (allIntoMountPathsForMntPtSourceNode.size() > 0) {
//                        System.out.println("add into mount paths");
//                        for (List<DefaultLink> intoMountPath : allIntoMountPathsForMntPtSourceNode) {
//                            ++count;
//                            nextSearchState = mergeInitialSearchSemanticModelState.clone();
//                            for (DefaultLink intoMountDefaultLink : intoMountPath) {
//                                String intoMountLinkId = LinkIdFactory.getLinkId(intoMountDefaultLink.getUri(), intoMountDefaultLink.getSource().getId(), intoMountDefaultLink.getTarget().getId());
//                                LabeledLink intoMountLink = new ObjectPropertyLink(intoMountLinkId, new Label(intoMountDefaultLink.getUri()), ObjectPropertyType.Direct);
//                                nextSearchState.getGraph().addVertex(intoMountDefaultLink.getSource());
//                                nextSearchState.getGraph().addVertex(intoMountDefaultLink.getTarget());
//                                nextSearchState.getGraph().addEdge(intoMountDefaultLink.getSource(), intoMountDefaultLink.getTarget(), intoMountLink);
//                            }
//                            nextSemanticModelsForInDirectMappingPaths.add(nextSearchState);
//                            newTrees.add(nextSearchState);
////                            nextSemanticModelsForInDirectMappingPaths.add(getNextSearchSemanticModel(mergeInitialSearchSemanticModelState,intoMountPath));
////                            newTrees.add(getNextSearchSemanticModel(mergeInitialSearchSemanticModelState,intoMountPath));
//                        }
//                    }
//
//                    if(allIntoTreePathsForMntPtSourceNode.size() > 0) {
//                        System.out.println("add into tree paths");
//                        for (List<DefaultLink> intoTreePath : allIntoTreePathsForMntPtSourceNode) {
//                            ++count;
//                            nextSearchState = mergeInitialSearchSemanticModelState.clone();
//                            for (DefaultLink intoTreeDefaultLink : intoTreePath) {
//                                String intoTreeLinkId = LinkIdFactory.getLinkId(intoTreeDefaultLink.getUri(), intoTreeDefaultLink.getSource().getId(), intoTreeDefaultLink.getTarget().getId());
//                                LabeledLink intoTreeLink = new ObjectPropertyLink(intoTreeLinkId, new Label(intoTreeDefaultLink.getUri()), ObjectPropertyType.Direct);
//                                nextSearchState.getGraph().addVertex(intoTreeDefaultLink.getSource());
//                                nextSearchState.getGraph().addVertex(intoTreeDefaultLink.getTarget());
//                                nextSearchState.getGraph().addEdge(intoTreeDefaultLink.getSource(), intoTreeDefaultLink.getTarget(), intoTreeLink);
//                            }
//                            nextSemanticModelsForInDirectMappingPaths.add(nextSearchState);
//                            newTrees.add(nextSearchState);
////                            nextSemanticModelsForInDirectMappingPaths.add(getNextSearchSemanticModel(mergeInitialSearchSemanticModelState,intoTreePath));
////                            newTrees.add(getNextSearchSemanticModel(mergeInitialSearchSemanticModelState,intoTreePath));
//                        }
//                    }
//
//                    if(allTrianglePathsForMntPtSourceNode.size() > 0) {
//                        System.out.println("add triangle paths");
//                        for (List<DefaultLink> trianglePath : allTrianglePathsForMntPtSourceNode) {
//                            ++count;
//                            nextSearchState = mergeInitialSearchSemanticModelState.clone();
//                            for (DefaultLink triangleDefaultLink : trianglePath) {
//                                String triangleLinkId = LinkIdFactory.getLinkId(triangleDefaultLink.getUri(), triangleDefaultLink.getSource().getId(), triangleDefaultLink.getTarget().getId());
//                                LabeledLink triangleLink = new ObjectPropertyLink(triangleLinkId, new Label(triangleDefaultLink.getUri()), ObjectPropertyType.Direct);
//                                nextSearchState.getGraph().addVertex(triangleDefaultLink.getSource());
//                                nextSearchState.getGraph().addVertex(triangleDefaultLink.getTarget());
//                                nextSearchState.getGraph().addEdge(triangleDefaultLink.getSource(), triangleDefaultLink.getTarget(), triangleLink);
//                            }
//                            nextSemanticModelsForInDirectMappingPaths.add(nextSearchState);
//                            newTrees.add(nextSearchState);
////                            nextSemanticModelsForInDirectMappingPaths.add(getNextSearchSemanticModel(mergeInitialSearchSemanticModelState,trianglePath));
////                            newTrees.add(getNextSearchSemanticModel(mergeInitialSearchSemanticModelState,trianglePath));
//                        }
//                    }
//                }
//        }

            if ((allIntoMountPathsForMntPtSourceNode.size() > 0) || (allIntoTreePathsForMntPtSourceNode.size() > 0) || (allTrianglePathsForMntPtSourceNode.size() > 0)){
                for (DefaultLink mntPtLink : mntPtNodeWithMntPtLinks.get(mntPtSourceNode)) {
                    /**loop and add different types of the paths**/
                    if (allIntoMountPathsForMntPtSourceNode.size() > 0) {
                        System.out.println("add into mount paths");

//                        nextSearchState = new SemanticModel(new RandomGUID().toString(), emptyGraph, emptygraph_addedcolumnNodes, mappingToSourceColumns)
                        for (List<DefaultLink> intoMountPath : allIntoMountPathsForMntPtSourceNode) {
                            ++count;

                            nextSemanticModelsForInDirectMappingPaths.add(getNextSearchSemanticModel(searchSemanticModelState,mntPtLink,mntPtSourceNode,attributeNode,intoMountPath));
                            newTrees.add(getNextSearchSemanticModel(searchSemanticModelState,mntPtLink,mntPtSourceNode,attributeNode,intoMountPath));
//                            nextSemanticModelsForInDirectMappingPaths.add(getNextSearchSemanticModel(mergeInitialSearchSemanticModelState,intoMountPath));
//                            newTrees.add(getNextSearchSemanticModel(mergeInitialSearchSemanticModelState,intoMountPath));
                        }
                    }

                    if(allIntoTreePathsForMntPtSourceNode.size() > 0) {
                        System.out.println("add into tree paths");
                        for (List<DefaultLink> intoTreePath : allIntoTreePathsForMntPtSourceNode) {
                            ++count;
                            nextSemanticModelsForInDirectMappingPaths.add(getNextSearchSemanticModel(searchSemanticModelState,mntPtLink,mntPtSourceNode,attributeNode,intoTreePath));
                            newTrees.add(getNextSearchSemanticModel(searchSemanticModelState,mntPtLink,mntPtSourceNode,attributeNode,intoTreePath));
//                            nextSemanticModelsForInDirectMappingPaths.add(getNextSearchSemanticModel(mergeInitialSearchSemanticModelState,intoTreePath));
//                            newTrees.add(getNextSearchSemanticModel(mergeInitialSearchSemanticModelState,intoTreePath));
                        }
                    }

                    if(allTrianglePathsForMntPtSourceNode.size() > 0) {
                        System.out.println("add triangle paths");
                        for (List<DefaultLink> trianglePath : allTrianglePathsForMntPtSourceNode) {
                            ++count;
                            nextSemanticModelsForInDirectMappingPaths.add(getNextSearchSemanticModel(searchSemanticModelState,mntPtLink,mntPtSourceNode,attributeNode,trianglePath));
                            newTrees.add(getNextSearchSemanticModel(searchSemanticModelState,mntPtLink,mntPtSourceNode,attributeNode,trianglePath));
//                            nextSemanticModelsForInDirectMappingPaths.add(getNextSearchSemanticModel(mergeInitialSearchSemanticModelState,trianglePath));
//                            newTrees.add(getNextSearchSemanticModel(mergeInitialSearchSemanticModelState,trianglePath));
                        }
                    }
                }
            }
            /**add one type of paths, and generate different types of next search semantic models**/

//            for(List<DefaultLink> addpath: AllPaths_1){
//                if(addpath.size()>0) {
////                    tempSemanticModelList = new ArrayList<SemanticModel>();
//                    WithDefaultlink = 0;
//                    NextSearchStateSM = MergeInitialStartSearchStateSM.clone();
////            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().vertexSet().size());
////            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().edgeSet().size());
//                    for (int i = 0; i < addpath.size(); i++) {
//                        if(addpath.get(i).getUri().equals("http://isi.edu/integration/karma/dev#defaultLink")){
//                            WithDefaultlink = 1;
//                        }
//                        LabeledLink addedlink = new DataPropertyLink(addpath.get(i).getId(), new Label(addpath.get(i).getUri()));
//                        NextSearchStateSM.getGraph().addVertex(addpath.get(i).getSource());
//                        NextSearchStateSM.getGraph().addVertex(addpath.get(i).getTarget());
//                        NextSearchStateSM.getGraph().addEdge(addpath.get(i).getSource(), addpath.get(i).getTarget(), addedlink);
//                    }
//                    MergeIntoTreenumber++;
//
//                    /**保存Json文件**/
//
//                    /**保存dot文件**/
//                    GraphVizUtil.exportSemanticModelToGraphviz(NextSearchStateSM, GraphVizLabelType.LocalId,
//                            GraphVizLabelType.LocalUri, true, true, Params.ROOT_DIR +"next-state-graph/" + "next_state_IntoMount" + Beam_Search + "_" + MergeIntoTreenumber + ".graph.json" + ".dot");
//
//                    if(WithDefaultlink==0){
//                        System.out.println("AllPaths_1中有不包含Defaultlink的path");
//                    }
//                    tempSemanticModelList = new ArrayList<SemanticModel>(WithOrWithoutDefaultlink.get(WithDefaultlink));
//                    tempSemanticModelList.add(NextSearchStateSM);
//                    WithOrWithoutDefaultlink.put(WithDefaultlink,tempSemanticModelList);
//
////                    newTrees.add(NextSearchStateSM);
//
////                    System.out.println("NextSearchStateSM的nodes:" + NextSearchStateSM.getGraph().vertexSet().size());
////                    System.out.println("NextSearchStateSM的links:" + NextSearchStateSM.getGraph().edgeSet().size());
//                }
//            }
//            /**添加其中任意一种类型(如AllPaths_1)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/
//
//            /**添加其中任意一种类型(如AllPaths_2)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/
//            for(List<DefaultLink> addpath: AllPaths_2){
//                if(addpath.size()>0) {
////                    tempSemanticModelList = new ArrayList<SemanticModel>();
//                    WithDefaultlink = 0;
//                    NextSearchStateSM = MergeInitialStartSearchStateSM.clone();
////            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().vertexSet().size());
////            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().edgeSet().size());
//                    for (int i = 0; i < addpath.size(); i++) {
//                        if(addpath.get(i).getUri().equals("http://isi.edu/integration/karma/dev#defaultLink")){
//                            WithDefaultlink = 1;
//                        }
//                        LabeledLink addedlink = new DataPropertyLink(addpath.get(i).getId(), new Label(addpath.get(i).getUri()));
//                        NextSearchStateSM.getGraph().addVertex(addpath.get(i).getSource());
//                        NextSearchStateSM.getGraph().addVertex(addpath.get(i).getTarget());
//                        NextSearchStateSM.getGraph().addEdge(addpath.get(i).getSource(), addpath.get(i).getTarget(), addedlink);
//                    }
//                    MergeIntoTreenumber++;
//
//                    GraphVizUtil.exportSemanticModelToGraphviz(NextSearchStateSM, GraphVizLabelType.LocalId,
//                            GraphVizLabelType.LocalUri, true, true, Params.ROOT_DIR +"next-state-graph/" + "next_state_IntoTree" + Beam_Search + "_" + MergeIntoTreenumber + ".graph.json" + ".dot");
//
//
//                    if(WithDefaultlink==0){
//                        System.out.println("AllPaths_2中有不包含Defaultlink的path");
//                    }
//                    tempSemanticModelList = new ArrayList<SemanticModel>(WithOrWithoutDefaultlink.get(WithDefaultlink));
//                    tempSemanticModelList.add(NextSearchStateSM);
//                    WithOrWithoutDefaultlink.put(WithDefaultlink,tempSemanticModelList);
//
////                    newTrees.add(NextSearchStateSM);
//
////                    System.out.println("NextSearchStateSM的nodes:" + NextSearchStateSM.getGraph().vertexSet().size());
////                    System.out.println("NextSearchStateSM的links:" + NextSearchStateSM.getGraph().edgeSet().size());
//                }
//            }
//            /**添加其中任意一种类型(如AllPaths_2)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/
//
//            /**添加其中任意一种类型(如AllPaths_3)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/
//            for(List<DefaultLink> addpath: AllPaths_3){
////                System.out.println("AllPaths_3:" + addpath.size());
//                if(addpath.size()>0) {
////                    tempSemanticModelList = new ArrayList<SemanticModel>();
//                    WithDefaultlink = 0;
//                    NextSearchStateSM = MergeInitialStartSearchStateSM.clone();
////            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().vertexSet().size());
////            System.out.println("NextSearchStateSM:"+NextSearchStateSM.getGraph().edgeSet().size());
//                    for (int i = 0; i < addpath.size(); i++) {
//                        if(addpath.get(i).getUri().equals("http://isi.edu/integration/karma/dev#defaultLink")){
//                            WithDefaultlink = 1;
//                        }
//                        LabeledLink addedlink = new DataPropertyLink(addpath.get(i).getId(), new Label(addpath.get(i).getUri()));
//                        NextSearchStateSM.getGraph().addVertex(addpath.get(i).getSource());
//                        NextSearchStateSM.getGraph().addVertex(addpath.get(i).getTarget());
//                        NextSearchStateSM.getGraph().addEdge(addpath.get(i).getSource(), addpath.get(i).getTarget(), addedlink);
//                    }
//                    MergeIntoTreenumber++;
//
//                    GraphVizUtil.exportSemanticModelToGraphviz(NextSearchStateSM, GraphVizLabelType.LocalId,
//                            GraphVizLabelType.LocalUri, true, true, Params.ROOT_DIR +"next-state-graph/" + "next_state_triangle" + Beam_Search + "_" + MergeIntoTreenumber + ".graph.json" + ".dot");
//
//
//                    if(WithDefaultlink==0){
//                        System.out.println("AllPaths_3中有不包含Defaultlink的path");
//                    }
//                    tempSemanticModelList = new ArrayList<SemanticModel>(WithOrWithoutDefaultlink.get(WithDefaultlink));
//                    tempSemanticModelList.add(NextSearchStateSM);
//                    WithOrWithoutDefaultlink.put(WithDefaultlink,tempSemanticModelList);
//
////                    newTrees.add(NextSearchStateSM);
//
////                    System.out.println("NextSearchStateSM的nodes:" + NextSearchStateSM.getGraph().vertexSet().size());
////                    System.out.println("NextSearchStateSM的links:" + NextSearchStateSM.getGraph().edgeSet().size());
//                }
//            }
//            /**添加其中任意一种类型(如AllPaths_3)的paths 根据每个path添加信息  生成此种类的nextsearchstate**/
//
        }
//
//        System.out.println("输出InitialnewTreesNum.size:" + newTrees.size());
//        if(WithOrWithoutDefaultlink.get(0).size()>0) {
//            newTrees.addAll(WithOrWithoutDefaultlink.get(0));
//            System.out.println("输出WithOrWithoutDefaultlink.get(0).size:" + WithOrWithoutDefaultlink.get(0).size());
//        }
//        if(WithOrWithoutDefaultlink.get(1).size()>0) {
//            Collections.shuffle(WithOrWithoutDefaultlink.get(1));
//            newTrees.addAll(WithOrWithoutDefaultlink.get(1));
//            System.out.println("输出WithOrWithoutDefaultlink.get(1).size:" + WithOrWithoutDefaultlink.get(1).size());
//        }

        System.out.println("count:" + count);
        return newTrees;
    }

    public static SemanticModel getNextSearchSemanticModel(SemanticModel initialSearchSemanticModel, List<DefaultLink> pathLinks){
        SemanticModel nextSearchSemanticModel = new SemanticModel(initialSearchSemanticModel);
        for (DefaultLink addedLink : pathLinks) {
            String addedLinkId = LinkIdFactory.getLinkId(addedLink.getUri(), addedLink.getSource().getId(), addedLink.getTarget().getId());
            LabeledLink addedObjectLink = new ObjectPropertyLink(addedLinkId, new Label(addedLink.getUri()), ObjectPropertyType.Direct);
            nextSearchSemanticModel.getGraph().addVertex(addedLink.getSource());
            nextSearchSemanticModel.getGraph().addVertex(addedLink.getTarget());
            nextSearchSemanticModel.getGraph().addEdge(addedLink.getSource(), addedLink.getTarget(), addedObjectLink);
        }
        return nextSearchSemanticModel;
    }

    public static  List<SemanticModel> transitionFunction(SemanticModel searchSemanticModelState, DirectedWeightedMultigraph<Node, DefaultLink> Gint, List<ColumnNode> attributeNodes, Set<InternalNode> internalNodesWithUseOntPaths) throws Exception {

        System.out.println("enter transitionFunction");
        List<ColumnNode> columnNodesOfSearchSemanticModelState = new ArrayList<ColumnNode>();
        List<SemanticModel> semanticModelTrees = new ArrayList<SemanticModel>();
        List<SemanticModel> nextSearchSemanticModelStates = new ArrayList<SemanticModel>();
        Set<ColumnNode> needAddedColumnNodes= new HashSet<ColumnNode>();
        Boolean hasOntPaths = false;

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
//                semanticModelTrees = mergeIntoTree(searchSemanticModelState, Gint, added_column_node, false,internalNodesWithUseOntPaths,hasOntPaths);//add a missing node to the current search semantic model
                semanticModelTrees = mergeIntoTreeEDM(searchSemanticModelState, Gint, added_column_node, false,internalNodesWithUseOntPaths,hasOntPaths);
//                System.out.println("enter mergeIntoTree");
                //for st+1 <- trees do
                if(semanticModelTrees.size()>0)
                    nextSearchSemanticModelStates.addAll(semanticModelTrees);
            }
//            int index = 0;
//            for(SemanticModel next_search_semantic_model_state: nextSearchSemanticModelStates) {
//                index++;
//                GraphVizUtil.exportSemanticModelToGraphviz(next_search_semantic_model_state, GraphVizLabelType.LocalId,
//                        GraphVizLabelType.LocalUri, true, true, Params.ROOT_DIR +"next-search-states/" + Beam_Search + "_" + TransitionFunctionIndex + "_" + index + ".graph.json" + ".dot");
//            }
        }
        return nextSearchSemanticModelStates;
    }

    public static List<SemanticModel> beamSearchForTrain(SemanticModel positiveSemanticModel, SemanticModel startSemanticModelState, DirectedWeightedMultigraph<Node, DefaultLink> integrationGraph, List<ColumnNode> completeColumnNodes, JSONObject jsonObject, String saveSMGraphVizPath, String saveSMJsonPath, Set<InternalNode> internalNodesWithUseOntPaths) throws Exception{
        List<SemanticModel> searchStates = new ArrayList<SemanticModel>();
        List<SemanticModel> nextSemanticModelStates = new ArrayList<SemanticModel>();
        List<SemanticModel> totalSemanticModelStates = new ArrayList<SemanticModel>();
        List<SemanticModel> negativeSemanticModels = new ArrayList<SemanticModel>();
        int addedAttributesNum = 0;
        List<Double> similarityScores = new ArrayList<Double>();

//        //删除指定文件夹内容  这两个文件夹存储startsearchstate在beamsearch过程中产生的states
//        File dir1=new File(Params.ROOT_DIR +"next-state-graph");
//        RemoveDir(dir1);
//        File dir2=new File(Params.ROOT_DIR +"next-search-states");
//        RemoveDir(dir2);

        System.out.println("beamSearchForTrain integration graph links size:" + integrationGraph.edgeSet().size());
        System.out.println("beamSearchForTrain integration graph nodes size:" + integrationGraph.vertexSet().size());

        /**if searchStates is not empty**/
        searchStates.add(startSemanticModelState);
        /**obtain the num of attributes to be added for the start semantic model state**/
        for(ColumnNode node: completeColumnNodes){
            if(!startSemanticModelState.getColumnNodes().contains(node)){
                addedAttributesNum++;
            }
        }

        //stop beam search if searchStates is empty, else continue to obtain the complete semantic models
        while(addedAttributesNum > 0){
            beamSearchNum++;
            System.out.println("addedAttributesNum:" + addedAttributesNum);
            totalSemanticModelStates = new ArrayList<SemanticModel>();
            //loop all search semantic model states in searchStates and invoke transitionFunction for generating next search semantic model states by adding one node
            for(SemanticModel search_sm_state:searchStates){
                transitionFunctionNum++;
                nextSemanticModelStates = transitionFunction(search_sm_state,integrationGraph,completeColumnNodes,internalNodesWithUseOntPaths);
                if(nextSemanticModelStates.size()>0)
                    totalSemanticModelStates.addAll(nextSemanticModelStates);
                System.out.println("totalSemanticModelStates.size in loop:" + totalSemanticModelStates.size());
            }
            System.out.println("totalSemanticModelStates.size out of loop:" + totalSemanticModelStates.size());
            /**if addedAttributesNum == 1 (that is the last beam search for generating final negative semantic models),
             * we need to evaluate the score between the sm in totalSemanticModelStates and positive semantic model, and
             * add the negative semantic models with score less than 1 into the selectedSemanticModels;
             * else we need to add all negative semantic models in totalSemanticModelStates into the selectedSemanticModels.**/
            if((addedAttributesNum>1) && (totalSemanticModelStates.size()>0)){
                searchStates = new ArrayList<SemanticModel>();//complete once beam search by adding one attribute, and clear the searchStates
                if(totalSemanticModelStates.size()>0) {
                    searchStates.addAll(totalSemanticModelStates);//get beam size next search semantic model states
                }
            }
            else if((addedAttributesNum == 1) && (totalSemanticModelStates.size()>0)){
                //loop all negative semantic models in totalSemanticModelStates and compute the score between them and the positive semantic model
                for(SemanticModel negative_semantic_model: totalSemanticModelStates){
                    assert negative_semantic_model.getColumnNodes().size() == positiveSemanticModel.getColumnNodes().size(): "negative_semantic_model.columns.size != positiveSemanticModel.columns.size";
                    double score = evaluateWithInverse(positiveSemanticModel,negative_semantic_model);
                    if(score<1) {
                        //save the negative semantic models
                        ++negativeSemanticModelForTrainIndexForOnePositiveSemanticModel;
                        negative_semantic_model.setName(positiveSemanticModel.getName().replace(".csv","") + "_negative" + negativeSemanticModelForTrainIndexForOnePositiveSemanticModel);
                        negative_semantic_model.writeJson(saveSMJsonPath + "/" + negative_semantic_model.getName().replace(".csv", "") + Params.MODEL_MAIN_FILE_EXT);
                        GraphVizUtil.exportSemanticModelToGraphviz(negative_semantic_model, GraphVizLabelType.LocalId,
                                GraphVizLabelType.LocalUri, true, true, saveSMGraphVizPath + "/" + negative_semantic_model.getName().replace(".csv", "") + Params.GRAPHVIS_MAIN_FILE_EXT);

                        negativeSemanticModels.add(negative_semantic_model);//get all negative semantic models with scores less than 1
                        similarityScores.add(score);
                    }
                }
            }
            addedAttributesNum--;
        }
        assert negativeSemanticModels.size() == similarityScores.size(): "negativeSemanticModels.size != similarityScores.size";
        if(similarityScores.size()>0) {
            listToTxt(similarityScores,saveSMJsonPath + "/" + "similarity_scores.txt");
        }
        System.out.println("negativeSemanticModels size after beam search:"+negativeSemanticModels.size());

        return negativeSemanticModels;
    }

    public static List<SemanticModel> beamSearch(SemanticModel positiveSemanticModel, SemanticModel startSemanticModelState, DirectedWeightedMultigraph<Node, DefaultLink> integrationGraph, List<ColumnNode> completeColumnNodes, String Path, JSONObject jsonObject, Set<InternalNode> internalNodesWithUseOntPaths) throws Exception{
        List<SemanticModel> searchStates = new ArrayList<SemanticModel>();
        List<SemanticModel> nextSemanticModelStates = new ArrayList<SemanticModel>();
        List<SemanticModel> totalSemanticModelStates = new ArrayList<SemanticModel>();
        List<SemanticModel> negativeSemanticModels = new ArrayList<SemanticModel>();
        int addedAttributesNum = 0;
        List<Double> similarityScores = new ArrayList<Double>();

//        //删除指定文件夹内容  这两个文件夹存储startsearchstate在beamsearch过程中产生的states
//        File dir1=new File(Params.ROOT_DIR +"next-state-graph");
//        RemoveDir(dir1);
//        File dir2=new File(Params.ROOT_DIR +"next-search-states");
//        RemoveDir(dir2);

        System.out.println("beamSearch integration graph links size:" + integrationGraph.edgeSet().size());
        System.out.println("beamSearch integration graph nodes size:" + integrationGraph.vertexSet().size());

        /**if searchStates is not empty**/
        searchStates.add(startSemanticModelState);
        assert searchStates.size() == 1: "initial number of search semantic model state is not 1";
        /**obtain the num of attributes to be added for the start semantic model state**/
        for(ColumnNode node: completeColumnNodes){
            if(!startSemanticModelState.getColumnNodes().contains(node)){
                addedAttributesNum++;
            }
        }

        //stop beam search if searchStates is empty, else continue to obtain the complete semantic models
        while(addedAttributesNum > 0){
            beamSearchNum++;
            System.out.println("addedAttributesNum:" + addedAttributesNum);
            totalSemanticModelStates = new ArrayList<SemanticModel>();
            //loop all search semantic model states in searchStates and invoke transitionFunction for generating next search semantic model states by adding one node
            for(SemanticModel search_sm_state:searchStates){
                transitionFunctionNum++;
                nextSemanticModelStates = transitionFunction(search_sm_state,integrationGraph,completeColumnNodes,internalNodesWithUseOntPaths);
                if(nextSemanticModelStates.size()>0)
                    totalSemanticModelStates.addAll(nextSemanticModelStates);
                System.out.println("totalSemanticModelStates.size in loop:" + totalSemanticModelStates.size());
            }
            System.out.println("totalSemanticModelStates.size out of loop:" + totalSemanticModelStates.size());
            /**if addedAttributesNum == 1 (that is the last beam search for generating final negative semantic models),
             * we need to evaluate the score between the sm in totalSemanticModelStates and positive semantic model, and
             * add the negative semantic models with score less than 1 into the selectedSemanticModels;
             * else we need to add all negative semantic models in totalSemanticModelStates into the selectedSemanticModels.**/
            if((addedAttributesNum>1) && (totalSemanticModelStates.size()>0)){
                searchStates = new ArrayList<SemanticModel>();//complete once beam search by adding one attribute, and clear the searchStates
                if(totalSemanticModelStates.size()>0) {
                    searchStates.addAll(totalSemanticModelStates);//get beam size next search semantic model states
                }
            }
            else if((addedAttributesNum == 1) && (totalSemanticModelStates.size()>0)){
                //loop all negative semantic models in totalSemanticModelStates and compute the score between them and the positive semantic model
                for(SemanticModel negative_semantic_model: totalSemanticModelStates){
                    assert negative_semantic_model.getColumnNodes().size() == positiveSemanticModel.getColumnNodes().size(): "negative_semantic_model.columns.size != positiveSemanticModel.columns.size";
                    double score = evaluate(positiveSemanticModel,negative_semantic_model);
                    if(score<1) {
                        negativeSemanticModels.add(negative_semantic_model);//get all negative semantic models with scores less than 1
                        similarityScores.add(score);
                    }
                }
            }
            addedAttributesNum--;
        }
        assert negativeSemanticModels.size() == similarityScores.size(): "negativeSemanticModels.size != similarityScores.size";
        System.out.println("negativeSemanticModels size after beam search:"+negativeSemanticModels.size());

        return negativeSemanticModels;
    }

    public static List<SemanticModel> beamSearchForPredict(SemanticModel positiveSemanticModel, SemanticModel startSemanticModelState, DirectedWeightedMultigraph<Node, DefaultLink> integrationGraph, List<ColumnNode> completeColumnNodes, String Path, JSONObject jsonObject, Set<InternalNode> internalNodesWithUseOntPaths) throws Exception{
        List<SemanticModel> searchStates = new ArrayList<SemanticModel>();
        List<SemanticModel> nextSemanticModelStates = new ArrayList<SemanticModel>();
        List<SemanticModel> totalSemanticModelStates = new ArrayList<SemanticModel>();
        List<SemanticModel> negativeSemanticModels = new ArrayList<SemanticModel>();
        int addedAttributesNum = 0;
        List<Double> similarityScores = new ArrayList<Double>();

//        //删除指定文件夹内容  这两个文件夹存储startsearchstate在beamsearch过程中产生的states
//        File dir1=new File(Params.ROOT_DIR +"next-state-graph");
//        RemoveDir(dir1);
//        File dir2=new File(Params.ROOT_DIR +"next-search-states");
//        RemoveDir(dir2);

        System.out.println("beamSearch integration graph links size:" + integrationGraph.edgeSet().size());
        System.out.println("beamSearch integration graph nodes size:" + integrationGraph.vertexSet().size());

        /**if searchStates is not empty**/
        searchStates.add(startSemanticModelState);
        assert searchStates.size() == 1: "initial number of search semantic model state is not 1";
        /**obtain the num of attributes to be added for the start semantic model state**/
        for(ColumnNode node: completeColumnNodes){
            if(!startSemanticModelState.getColumnNodes().contains(node)){
                addedAttributesNum++;
            }
        }

        //stop beam search if searchStates is empty, else continue to obtain the complete semantic models
        while(addedAttributesNum > 0){
            double bestScore = 0.0;
            beamSearchNum++;
            System.out.println("addedAttributesNum:" + addedAttributesNum);
            totalSemanticModelStates = new ArrayList<SemanticModel>();
            //loop all search semantic model states in searchStates and invoke transitionFunction for generating next search semantic model states by adding one node
            for(SemanticModel search_sm_state:searchStates){
                transitionFunctionNum++;
                nextSemanticModelStates = transitionFunction(search_sm_state,integrationGraph,completeColumnNodes,internalNodesWithUseOntPaths);
                if(nextSemanticModelStates.size()>0)
                    for(SemanticModel nextSearchState: nextSemanticModelStates) {
                        /**comment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/
                        if(evaluateWithInversePrecision(positiveSemanticModel,nextSearchState) == 1) {
                            totalSemanticModelStates.add(nextSearchState);
                        }
                        /**comment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/

                        /**uncomment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/
//                        double similarityScore = evaluateWithInverse(positiveSemanticModel,nextSearchState);
//                        if(similarityScore>bestScore) {
//                            totalSemanticModelStates = new ArrayList<SemanticModel>();
//                            bestScore = similarityScore;
//                            totalSemanticModelStates.add(nextSearchState);
//                        }
                        /**uncomment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/
                    }
                System.out.println("totalSemanticModelStates.size in loop:" + totalSemanticModelStates.size());
            }
            /**uncomment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/
//            assert totalSemanticModelStates.size() == 1: "totalSemanticModelStates.size != 1";
            /**uncomment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/
            System.out.println("totalSemanticModelStates.size out of loop:" + totalSemanticModelStates.size());
            /**if addedAttributesNum == 1 (that is the last beam search for generating final negative semantic models),
             * we need to evaluate the score between the sm in totalSemanticModelStates and positive semantic model, and
             * add the negative semantic models with score less than 1 into the selectedSemanticModels;
             * else we need to add all negative semantic models in totalSemanticModelStates into the selectedSemanticModels.**/
            if((addedAttributesNum>1) && (totalSemanticModelStates.size()>0)){
                searchStates = new ArrayList<SemanticModel>();//complete once beam search by adding one attribute, and clear the searchStates
                if(totalSemanticModelStates.size()>10) {
                    searchStates.addAll(totalSemanticModelStates.subList(0,10));
                }
                else{
                    searchStates.addAll(totalSemanticModelStates);
                }
            }
            else if((addedAttributesNum == 1) && (totalSemanticModelStates.size()>0)){
                //loop all negative semantic models in totalSemanticModelStates and compute the score between them and the positive semantic model
                for(SemanticModel negative_semantic_model: totalSemanticModelStates){
                    assert negative_semantic_model.getColumnNodes().size() == positiveSemanticModel.getColumnNodes().size(): "negative_semantic_model.columns.size != positiveSemanticModel.columns.size";
                    double score = evaluateWithInverse(positiveSemanticModel,negative_semantic_model);
                    /**comment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/
                    if(score==1) {
                        negativeSemanticModels.add(negative_semantic_model);//get all negative semantic models with scores less than 1
                        similarityScores.add(score);
                    }
                    /**comment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/

                    /**uncomment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/
//                    negativeSemanticModels.add(negative_semantic_model);//get all negative semantic models with scores less than 1
//                    similarityScores.add(score);
                    /**uncomment this section while predicting s06 s23; s11 s20 s26; s02 s05 s08 s10**/
                }
            }
            addedAttributesNum--;
        }
        assert negativeSemanticModels.size() == similarityScores.size(): "negativeSemanticModels.size != similarityScores.size";
        System.out.println("negativeSemanticModels size after beam search:"+negativeSemanticModels.size());
        System.out.println("similarityScores.get(0):" + similarityScores.get(0));

        return negativeSemanticModels;
    }


    public static double evaluatePrecision(SemanticModel positiveSemanticModel,SemanticModel evaluatedSemanticModel){
        double score = 0.0;
        SortableSemanticModel sortableSemanticModel = new SortableSemanticModel(evaluatedSemanticModel,true);
        ModelEvaluation evaluateModel = sortableSemanticModel.evaluate(positiveSemanticModel);
        score = evaluateModel.getPrecision();
        return score;
    }

    public static double evaluate(SemanticModel positiveSemanticModel,SemanticModel evaluatedSemanticModel){
        double score = 0.0;
        SortableSemanticModel sortableSemanticModel = new SortableSemanticModel(evaluatedSemanticModel,true);
        ModelEvaluation evaluateModel = sortableSemanticModel.evaluate(positiveSemanticModel);
        score = 2*(evaluateModel.getPrecision()*evaluateModel.getRecall())/(evaluateModel.getPrecision()+evaluateModel.getRecall());
        return score;
    }

    public static double evaluateWithInversePrecision(SemanticModel positiveSemanticModel,SemanticModel evaluatedSemanticModel) throws IOException {
        double score = 0.0;
        ModelEvaluation evaluateModel = evaluatedSemanticModel.newEvaluateForSpecifiedUri(positiveSemanticModel);
        score = evaluateModel.getPrecision();
        return score;
    }

    public static double evaluateWithInverse(SemanticModel positiveSemanticModel,SemanticModel evaluatedSemanticModel) throws IOException {
        double score = 0.0;
        ModelEvaluation evaluateModel = evaluatedSemanticModel.newEvaluateForSpecifiedUri(positiveSemanticModel);
        if(evaluateModel.getPrecision()+evaluateModel.getRecall() == 0.0)
            return score;
        score = 2*(evaluateModel.getPrecision()*evaluateModel.getRecall())/(evaluateModel.getPrecision()+evaluateModel.getRecall());
        return score;
    }

    public static List<SemanticModel> getAllSubAndSamePositiveSemanticModels(SemanticModel sm, int sm_index, List<String> unique_columns, String savePath, Boolean useOriginalSemanticModel, Map<String,Set<InternalNode>> internalNodeUriWithInternalNodes) throws Exception {
        String SM_Graphviz_Path = savePath + "sub-same-positive-models-graphviz-all/" + sm.getName().replace(".csv","");
        String SM_Json_Path = savePath + "sub-same-positive-models-json-all/" + sm.getName().replace(".csv","");
        List<ColumnNode> columnNodes = new ArrayList<ColumnNode>();
        List<String> columnNames = new ArrayList<String>();
        List<String> temp_columnNames = new ArrayList<String>();
        List<String> uniqueColumns = new ArrayList<String>(unique_columns);
        List<String> addedColumns = new ArrayList<String>();
        List<List<String>> subSets = new ArrayList<List<String>>();
        SemanticModel cloneSM = null;
        SemanticModel positiveSemanticModel = null;
        List<SemanticModel> positiveSemanticModels = new ArrayList<SemanticModel>();

        deleteFile(SM_Graphviz_Path);
        deleteFile(SM_Json_Path);

        CreateFile(SM_Graphviz_Path);
        CreateFile(SM_Json_Path);


        columnNodes = sm.getColumnNodes();

        for(ColumnNode column_node: columnNodes) {
            columnNames.add(column_node.getColumnName());
            if(!uniqueColumns.contains(column_node.getColumnName())) {
                addedColumns.add(column_node.getColumnName());
            }
        }
        System.out.println("columnNames:" + columnNames);
        System.out.println("uniqueColumns:" + uniqueColumns);
        System.out.println("addedColumns:" + addedColumns);

        subSets = getSubSets(addedColumns);
        System.out.println("subSets.size:" + subSets.size());

        Map<Integer,Integer> indexTypeWithIndexNum = new HashMap<Integer,Integer>();
        for(int i = 0; i<sm.getColumnNodes().size(); i++)
            indexTypeWithIndexNum.put(i+1,0);

        int indexWithoutDel = 0;
        int indexWithDel = 0;
        int indexTypeNum = 0;
        String subPositiveSemanticModelName = null;

        for(List<String> subset: subSets){
            if((!useOriginalSemanticModel) && (subset.size()==addedColumns.size()))
                continue;
            if(subset.size()==1){
                ++indexWithoutDel;
                System.out.println("subset without deleting:" + subset);
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
                        break;
                    }
                }
                cloneSM.setName(sm.getName().replace(".csv","") + "_Sub1_" + indexWithoutDel + ".csv");
                positiveSemanticModels.add(cloneSM);
                String saveSMGraphvizPath = SM_Graphviz_Path + "/" + cloneSM.getName().replace(".csv", "") + "/";
                String saveSMJsonPath = SM_Json_Path + "/" + cloneSM.getName().replace(".csv", "") + "/";
                getSamePositiveSemanticModelsForOneSemanticModel(cloneSM,internalNodeUriWithInternalNodes,saveSMGraphvizPath,saveSMJsonPath);

            }
            else if(subset.size()>1) {
                indexWithDel++;
                System.out.println("subset for deleting:" + subset);
                temp_columnNames = new ArrayList<String>(columnNames);
                temp_columnNames.removeAll(subset);
                System.out.println("temp_columnNames:" + temp_columnNames);
                cloneSM = sm.clone();
                indexTypeNum = indexTypeWithIndexNum.get(subset.size())+1;
                indexTypeWithIndexNum.put(subset.size(),indexTypeNum);
                cloneSM.setName(sm.getName().replace(".csv","") + "_Sub" + subset.size() + "_" + indexTypeNum + ".csv");
                positiveSemanticModel = getSubSemanticModels(cloneSM, cloneSM.getName().replace(".csv",""), temp_columnNames, null, null);
                positiveSemanticModels.add(positiveSemanticModel);
                String saveSMGraphvizPath = SM_Graphviz_Path + "/" + positiveSemanticModel.getName().replace(".csv", "") + "/";
                String saveSMJsonPath = SM_Json_Path + "/" + positiveSemanticModel.getName().replace(".csv", "") + "/";
                getSamePositiveSemanticModelsForOneSemanticModel(positiveSemanticModel,internalNodeUriWithInternalNodes,saveSMGraphvizPath,saveSMJsonPath);

            }
        }
        assert indexWithoutDel == sm.getColumnNodes().size(): "sm.getColumnNodes.size != indexWithoutDel";
        int subSemanticModelsNum = indexWithoutDel;
        for(int i = 1; i < sm.getColumnNodes().size()+1; i++){
            subSemanticModelsNum += indexTypeWithIndexNum.get(i);
        }
        assert subSemanticModelsNum == positiveSemanticModels.size(): "positiveSemanticModels.size != subSemanticModelsNum";
        assert subSemanticModelsNum == subSets.size(): "subSemanticModelsNum != subSets.size";
//        System.out.println("positiveSemanticModels.size:" + positiveSemanticModels.size());
//        System.out.println("NumOfSpecificColumn:" + getNumOfSpecificColumn(subSets, "Title"));  check the number of subsets with specific column name
        return positiveSemanticModels;
    }


    public static List<SemanticModel> getAllSubPositiveSemanticModels(SemanticModel sm, int sm_index, List<String> unique_columns, String savePath, Boolean useOriginalSemanticModel) throws Exception {
        String SM_Graphviz_Path = savePath + "sub-positive-models-graphviz-all/" + sm.getName().replace(".csv","");
        String SM_Json_Path = savePath + "sub-positive-models-json-all/" + sm.getName().replace(".csv","");
        List<ColumnNode> columnNodes = new ArrayList<ColumnNode>();
        List<String> columnNames = new ArrayList<String>();
        List<String> temp_columnNames = new ArrayList<String>();
        List<String> uniqueColumns = new ArrayList<String>(unique_columns);
        List<String> addedColumns = new ArrayList<String>();
        List<List<String>> subSets = new ArrayList<List<String>>();
        SemanticModel cloneSM = null;
        SemanticModel positiveSemanticModel = null;
        List<SemanticModel> positiveSemanticModels = new ArrayList<SemanticModel>();

        deleteFile(SM_Graphviz_Path);
        deleteFile(SM_Json_Path);

        CreateFile(SM_Graphviz_Path);
        CreateFile(SM_Json_Path);


        columnNodes = sm.getColumnNodes();

        for(ColumnNode column_node: columnNodes) {
            columnNames.add(column_node.getColumnName());
            if(!uniqueColumns.contains(column_node.getColumnName())) {
                addedColumns.add(column_node.getColumnName());
            }
        }
        System.out.println("columnNames:" + columnNames);
        System.out.println("uniqueColumns:" + uniqueColumns);
        System.out.println("addedColumns:" + addedColumns);

        subSets = getSubSets(addedColumns);
        System.out.println("subSets.size:" + subSets.size());

        Map<Integer,Integer> indexTypeWithIndexNum = new HashMap<Integer,Integer>();
        for(int i = 0; i<sm.getColumnNodes().size(); i++)
            indexTypeWithIndexNum.put(i+1,0);

        int indexWithoutDel = 0;
        int indexWithDel = 0;
        int indexTypeNum = 0;
        String subPositiveSemanticModelName = null;

        for(List<String> subset: subSets){
            if((!useOriginalSemanticModel) && (subset.size()==addedColumns.size()))
                continue;
            if(subset.size()==1){
                ++indexWithoutDel;
                System.out.println("subset without deleting:" + subset);
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
                        positiveSemanticModels.add(cloneSM);
                    }
                }
                cloneSM.setName(sm.getName().replace(".csv","") + "_Sub1_" + indexWithoutDel + ".csv");

                //save the positive semantic models with only one attribute node
                cloneSM.writeJson(SM_Json_Path + "/" + cloneSM.getName().replace(".csv", "") + Params.MODEL_MAIN_FILE_EXT);
                GraphVizUtil.exportSemanticModelToGraphviz(cloneSM, GraphVizLabelType.LocalId,
                        GraphVizLabelType.LocalUri, true, true, SM_Graphviz_Path + "/" + cloneSM.getName().replace(".csv", "") + Params.GRAPHVIS_MAIN_FILE_EXT);

            }
            else if(subset.size()>1) {
                indexWithDel++;
//                if(index > 6) break; // test for partition samples, don't forget delete
                System.out.println("subset for deleting:" + subset);
                temp_columnNames = new ArrayList<String>(columnNames);
                temp_columnNames.removeAll(subset);
                System.out.println("temp_columnNames:" + temp_columnNames);
                cloneSM = sm.clone();
                indexTypeNum = indexTypeWithIndexNum.get(subset.size())+1;
                indexTypeWithIndexNum.put(subset.size(),indexTypeNum);
                cloneSM.setName(sm.getName().replace(".csv","") + "_Sub" + subset.size() + "_" + indexTypeNum + ".csv");
                positiveSemanticModel = getSubSemanticModels(cloneSM, cloneSM.getName().replace(".csv",""), temp_columnNames, SM_Graphviz_Path, SM_Json_Path);
                positiveSemanticModels.add(positiveSemanticModel);
            }
        }
        assert indexWithoutDel == sm.getColumnNodes().size(): "sm.getColumnNodes.size != indexWithoutDel";
        int subSemanticModelsNum = indexWithoutDel;
        for(int i = 1; i < sm.getColumnNodes().size()+1; i++){
            subSemanticModelsNum += indexTypeWithIndexNum.get(i);
        }
        assert subSemanticModelsNum == positiveSemanticModels.size(): "positiveSemanticModels.size != subSemanticModelsNum";
        if(!useOriginalSemanticModel)
            assert subSemanticModelsNum == subSets.size() - 1: "subSemanticModelsNum != subSets.size";
        else
            assert subSemanticModelsNum == subSets.size(): "subSemanticModelsNum != subSets.size";
//        System.out.println("positiveSemanticModels.size:" + positiveSemanticModels.size());
//        System.out.println("NumOfSpecificColumn:" + getNumOfSpecificColumn(subSets, "Title"));  check the number of subsets with specific column name
        return positiveSemanticModels;
    }

    public static void saveSubSemanticModelsAsModelAndJson(List<SemanticModel> semanticModels, String savePath){
        String graphName = null;
        String graphNameJson = null;
        int index = 0;
        for(SemanticModel sm: semanticModels) {
            ++index;
            graphName = savePath + "sub-positive-models-graphviz-test\\" + "Sub" + index + Params.GRAPHVIS_MAIN_FILE_EXT;
            graphNameJson = savePath + "sub-positive-models-json-test\\" + "Sub" + index + Params.MODEL_MAIN_FILE_EXT;

            if (graphName != null && graphNameJson != null) {
                try {
                    sm.writeJson(graphNameJson);
                    GraphVizUtil.exportSemanticModelToGraphviz(sm, GraphVizLabelType.LocalId,
                            GraphVizLabelType.LocalUri, true, true, graphName);
                } catch (Exception e) {
                    e.printStackTrace();
                }
            }
        }
    }

    public static List<SemanticModel> getNegativeSemanticModelsForEmbeddingStartFromOneAttributeNode(int predictSourceIndex, SemanticModel predictSemanticModel, DirectedWeightedMultigraph<Node, DefaultLink> integrationGraph, JSONObject jsonObject, Set<InternalNode> internalNodesWithUseOntPaths) throws Exception{
        List<SemanticModel> SemanticModelsWithOnlyOneAttributeNode = null;
        List<SemanticModel> negativeSemanticModels;
        List<SemanticModel> allNegativeSemanticModelsForPositiveSemanticModel = new ArrayList<SemanticModel>();
        SemanticModelsWithOnlyOneAttributeNode = ModelReader.importSemanticModelsFromJsonFiles("D:\\ASM\\CRM\\positive-models\\sub-positive-models-json-test", Params.MODEL_MAIN_FILE_EXT);
        System.out.println("SemanticModelsWithOnlyOneAttributeNode.size:" + SemanticModelsWithOnlyOneAttributeNode.size());

        int index = 0;
        for(SemanticModel subSM: SemanticModelsWithOnlyOneAttributeNode){
            if(++index>1)
                break;

            /**obtain partial negative semantic models based on the current start search sub semantic model**/
            negativeSemanticModels = beamSearch(predictSemanticModel, subSM, integrationGraph, predictSemanticModel.getColumnNodes(), "", jsonObject, internalNodesWithUseOntPaths);
            if(negativeSemanticModels.size()>0)
                allNegativeSemanticModelsForPositiveSemanticModel.addAll(negativeSemanticModels);

        }

        return allNegativeSemanticModelsForPositiveSemanticModel;
    }

    public static void getAllPositiveSemanticModelForOneGoldSemanticModel(int predictSourceIndex, SemanticModel predictSemanticModel, DirectedWeightedMultigraph<Node, DefaultLink> integrationGraph, JSONObject jsonObject) throws Exception {
        /**obtain  and save all sub positive semantic models (contains the semantic models with only one attribute node
         * and the semantic model with all attribute nodes)**/
        List<SemanticModel> allPositiveSemanticModels = new ArrayList<SemanticModel>();
        List<String> unique_columns = new ArrayList<String>();
//        String saveSemanticModelsPath = "D:\\ASM\\CRM\\";
//        String saveSemanticModelsPath = Params.ROOT_DIR_2023;
//        String saveSemanticModelsPath = Params.ROOT_DIR_2023_LINUX;
//        String saveSemanticModelsPath = Params.EDM_ROOT_DIR_2023;
        String saveSemanticModelsPath = Params.EDM_ROOT_DIR_2023_LINUX;

        Map<String,Set<InternalNode>> internalNodeUriWithInternalNodes = getInternalNodeUriWithInternalNodes(integrationGraph);
        /**only the original sub positive semantic models (contains the only one attribute node and all attribute nodes)**/
//        allPositiveSemanticModels = getAllSubPositiveSemanticModels(predictSemanticModel,predictSourceIndex,unique_columns,saveSemanticModelsPath + "positive-models/",true);
        allPositiveSemanticModels = getAllSubAndSamePositiveSemanticModels(predictSemanticModel,predictSourceIndex,unique_columns,saveSemanticModelsPath + "positive-models/",true,internalNodeUriWithInternalNodes);

        System.out.println("allPositiveSemanticModel:" + allPositiveSemanticModels.size());

    }

    public static List<SemanticModel> getSamePositiveSemanticModelsForOneSemanticModel(SemanticModel positiveSemanticModel, Map<String,Set<InternalNode>> internalNodeUriWithInternalNodes,String saveSMGraphVizPath,String saveSMJsonPath) throws IOException {
        //obtain map{key:internal_node_id,value:internal_node_uri} for the given positive semantic model
        List<List<InternalNode>> internalNodesToBeReplaced = new ArrayList<List<InternalNode>>();
        List<InternalNode> currentInternalNodesCombination = new ArrayList<InternalNode>();
        List<InternalNode> replacedInternalNodesCombination = new ArrayList<InternalNode>();
        SemanticModel cloneSM = null;
        List<SemanticModel> samePositiveSemanticModelsForOneSemanticModel = new ArrayList<SemanticModel>();
        int samePositiveSemanticModelIndex = 1;

        if((saveSMGraphVizPath != null) && (saveSMJsonPath != null)) {
            deleteFile(saveSMGraphVizPath);
            deleteFile(saveSMJsonPath);

            CreateFile(saveSMGraphVizPath);
            CreateFile(saveSMJsonPath);
        }

        for(DefaultLink link: positiveSemanticModel.getGraph().edgeSet()){
            link.getSource().addOutLink(link);
            link.getTarget().addInLink(link);
            if((link.getSource() instanceof InternalNode) && ((!currentInternalNodesCombination.contains((InternalNode) link.getSource()))) && (internalNodeUriWithInternalNodes.keySet().contains(link.getSource().getUri()))){
                if(internalNodeUriWithInternalNodes.get(link.getSource().getUri()).size()>1){
                    currentInternalNodesCombination.add((InternalNode) link.getSource());
                    internalNodesToBeReplaced.add(new ArrayList<InternalNode>(internalNodeUriWithInternalNodes.get(link.getSource().getUri())));
                }
            }
            if((link.getTarget() instanceof InternalNode) && ((!currentInternalNodesCombination.contains((InternalNode) link.getTarget()))) && (internalNodeUriWithInternalNodes.keySet().contains(link.getTarget().getUri()))){
                if(internalNodeUriWithInternalNodes.get(link.getTarget().getUri()).size()>1){
                    currentInternalNodesCombination.add((InternalNode) link.getTarget());
                    internalNodesToBeReplaced.add(new ArrayList<InternalNode>(internalNodeUriWithInternalNodes.get(link.getTarget().getUri())));
                }
            }
        }

        cloneSM = positiveSemanticModel.clone();
        cloneSM.setName(positiveSemanticModel.getName().replace(".csv","") + "_Same" + samePositiveSemanticModelIndex + ".csv");
        assert evaluateWithInverse(positiveSemanticModel,cloneSM) == 1: "the semantic model is not same as the positive semantic model";
        samePositiveSemanticModelsForOneSemanticModel.add(cloneSM);
        assert samePositiveSemanticModelsForOneSemanticModel.size() == 1: "samePositiveSemanticModelsForOneSemanticModel.size != 1";
        if((saveSMGraphVizPath != null) && (saveSMJsonPath != null)){
            //save the same positive semantic model
            cloneSM.writeJson(saveSMJsonPath + cloneSM.getName().replace(".csv", "") + Params.MODEL_MAIN_FILE_EXT);
            GraphVizUtil.exportSemanticModelToGraphviz(cloneSM, GraphVizLabelType.LocalId,
                    GraphVizLabelType.LocalUri, true, true, saveSMGraphVizPath + cloneSM.getName().replace(".csv", "") + Params.GRAPHVIS_MAIN_FILE_EXT);
        }
        System.out.println("cloneSM:" + cloneSM.getName());

        if(internalNodesToBeReplaced.size() == 0)
            return samePositiveSemanticModelsForOneSemanticModel;

        for(InternalNode internalNode1: currentInternalNodesCombination) {
            for (InternalNode internalNode2 : positiveSemanticModel.getInternalNodes()) {
                if(internalNode2.getId().equals(internalNode1.getId())){
                    replacedInternalNodesCombination.add(internalNode2);
                    break;
                }
            }
        }


//        for(InternalNode internalNode: positiveSemanticModel.getInternalNodes()){
//            if(internalNodeUriWithInternalNodes.keySet().contains(internalNode.getUri())){
//                if(internalNodeUriWithInternalNodes.get(internalNode.getUri()).size()>1){
//                    currentInternalNodesCombination.add(internalNode);
//                    internalNodesToBeReplaced.add(new ArrayList<InternalNode>(internalNodeUriWithInternalNodes.get(internalNode.getUri())));
//                }
//            }
//        }

        List<List<InternalNode>> otherInternalNodesCombinations = descartesRecursiveUnique(internalNodesToBeReplaced);
        int originalCombinationNum = otherInternalNodesCombinations.size();
        otherInternalNodesCombinations.remove(currentInternalNodesCombination);
        int currentCombinationNum = otherInternalNodesCombinations.size();
        assert currentCombinationNum == originalCombinationNum - 1: "currentCombinationNum != originalCombinationNum - 1";


        for(List<InternalNode> internalNodesCombination: otherInternalNodesCombinations){
            ++samePositiveSemanticModelIndex;
            cloneSM = positiveSemanticModel.clone();

            //remove the internal nodes and their corresponding links and obtain the map{replaced_internal_node:candidate_internal_node}
            Map<InternalNode,InternalNode> replacedInternalNodeWithCandidateInternalNode = new HashMap<InternalNode,InternalNode>();
            for(int i = 0; i < replacedInternalNodesCombination.size(); i++){
                if(replacedInternalNodesCombination.get(i).getId().equals(internalNodesCombination.get(i).getId()))
                    continue;
                replacedInternalNodeWithCandidateInternalNode.put(replacedInternalNodesCombination.get(i),internalNodesCombination.get(i));
                //remove the internal node
                cloneSM.getGraph().removeVertex(replacedInternalNodesCombination.get(i));
                //remove the corresponding inLinks
                for(DefaultLink inLink: replacedInternalNodesCombination.get(i).getInLinks()){
                    cloneSM.getGraph().removeEdge((LabeledLink) inLink);
                }
                //remove the corresponding outLinks
                for(DefaultLink outLink: replacedInternalNodesCombination.get(i).getOutLinks()){
                    cloneSM.getGraph().removeEdge((LabeledLink) outLink);
                }
            }
            assert replacedInternalNodesCombination.size() == internalNodesCombination.size(): "internalNodesCombination.size != replacedInternalNodesCombination.size";
//            int replacedInternalNodeIndex = 0;
//            for(InternalNode internalNode: positiveSemanticModel.getInternalNodes()){
//                if(internalNode.getUri().equals(internalNodesCombination.get(0).getUri())){
//                    if(internalNode.getId().equals(internalNodesCombination.get(0).getId())){
//                        ++replacedInternalNodeIndex;
//                        continue;
//                    }
//                    else{
//                        //replace the internal node and their corresponding links
//                    }
//                }
//            }
            //replace the internal node

            //add the needed internal nodes
            for(InternalNode internalNode: replacedInternalNodeWithCandidateInternalNode.values()){
                cloneSM.getGraph().addVertex(internalNode);
            }
            //add the needed links
            for(InternalNode replacedInternalNode: replacedInternalNodeWithCandidateInternalNode.keySet()){
                //add the inLinks
                if(replacedInternalNode.getInLinks().size()>0){
                    for(DefaultLink inLink: replacedInternalNode.getInLinks()){
                        String addedInLinkId = null;
                        LabeledLink addedInLink = null;
                        if(replacedInternalNodeWithCandidateInternalNode.keySet().contains(inLink.getSource())) {
                            addedInLinkId = LinkIdFactory.getLinkId(inLink.getUri(), replacedInternalNodeWithCandidateInternalNode.get(inLink.getSource()).getId(), replacedInternalNodeWithCandidateInternalNode.get(inLink.getTarget()).getId());
                            addedInLink = new ObjectPropertyLink(addedInLinkId,new Label(inLink.getUri()),((ObjectPropertyLink) inLink).getObjectPropertyType());
                            cloneSM.getGraph().addEdge(replacedInternalNodeWithCandidateInternalNode.get(inLink.getSource()),replacedInternalNodeWithCandidateInternalNode.get(inLink.getTarget()),addedInLink);
                        }
                        else {
                            addedInLinkId = LinkIdFactory.getLinkId(inLink.getUri(), inLink.getSource().getId(), replacedInternalNodeWithCandidateInternalNode.get(inLink.getTarget()).getId());
                            addedInLink = new ObjectPropertyLink(addedInLinkId,new Label(inLink.getUri()),((ObjectPropertyLink) inLink).getObjectPropertyType());
                            cloneSM.getGraph().addEdge(inLink.getSource(),replacedInternalNodeWithCandidateInternalNode.get(inLink.getTarget()),addedInLink);
                        }
                    }
                }

                //add the outLinks
                if(replacedInternalNode.getOutLinks().size()>0){
                    for(DefaultLink outLink: replacedInternalNode.getOutLinks()){
                        String addedOutLinkId = null;
                        LabeledLink addedOutLink = null;
                        if(outLink.getTarget() instanceof InternalNode) {
                            if(replacedInternalNodeWithCandidateInternalNode.keySet().contains(outLink.getTarget())) {
                                addedOutLinkId = LinkIdFactory.getLinkId(outLink.getUri(), replacedInternalNodeWithCandidateInternalNode.get(outLink.getSource()).getId(), replacedInternalNodeWithCandidateInternalNode.get(outLink.getTarget()).getId());
                                addedOutLink = new ObjectPropertyLink(addedOutLinkId,new Label(outLink.getUri()),((ObjectPropertyLink) outLink).getObjectPropertyType());
                                cloneSM.getGraph().addEdge(replacedInternalNodeWithCandidateInternalNode.get(outLink.getSource()),replacedInternalNodeWithCandidateInternalNode.get(outLink.getTarget()),addedOutLink);
                            }
                            else {
                                addedOutLinkId = LinkIdFactory.getLinkId(outLink.getUri(), replacedInternalNodeWithCandidateInternalNode.get(outLink.getSource()).getId(), outLink.getTarget().getId());
                                addedOutLink = new ObjectPropertyLink(addedOutLinkId,new Label(outLink.getUri()),((ObjectPropertyLink) outLink).getObjectPropertyType());
                                cloneSM.getGraph().addEdge(replacedInternalNodeWithCandidateInternalNode.get(outLink.getSource()), outLink.getTarget(), addedOutLink);
                            }
                        }
                        else{
                            addedOutLinkId = LinkIdFactory.getLinkId(outLink.getUri(), replacedInternalNodeWithCandidateInternalNode.get(outLink.getSource()).getId(), outLink.getTarget().getId());
                            addedOutLink = new DataPropertyLink(addedOutLinkId,new Label(outLink.getUri()));
                            cloneSM.getGraph().addEdge(replacedInternalNodeWithCandidateInternalNode.get(outLink.getSource()), outLink.getTarget(), addedOutLink);
                        }
                    }
                }
            }

//            for(int i = 0; i < internalNodesCombination.size(); i++){
//                System.out.println("internalNodesCombination.get(i).getUri():" + internalNodesCombination.get(i).getUri());
//                System.out.println("replacedInternalNodesCombination.get(i).getUri():" + replacedInternalNodesCombination.get(i).getUri());
//
//                assert internalNodesCombination.get(i).getUri().equals(replacedInternalNodesCombination.get(i).getUri()): "internalNodesCombination.get(i).getId != replacedInternalNodesCombination.get(i).getId";
//                if(internalNodesCombination.get(i).getId().equals(replacedInternalNodesCombination.get(i).getId()))
//                    continue;
//
////                //remove the internal node and their corresponding links
////                cloneSM.getGraph().removeVertex(replacedInternalNodesCombination.get(i));
//                //add the internal node
//                InternalNode addedInternalNode = new InternalNode(internalNodesCombination.get(i).getId(),internalNodesCombination.get(i).getLabel());
//                cloneSM.getGraph().addVertex(addedInternalNode);
//                //remove and add inLinks
//                if(replacedInternalNodesCombination.get(i).getInLinks().size()>0){
//                    for(DefaultLink inLink: replacedInternalNodesCombination.get(i).getInLinks()){
//                        String addedInLinkId = LinkIdFactory.getLinkId(inLink.getUri(),inLink.getSource().getId(),addedInternalNode.getId());
//                        LabeledLink addedInLink = new ObjectPropertyLink(addedInLinkId,new Label(inLink.getUri()),((ObjectPropertyLink) inLink).getObjectPropertyType());
////                        //remove the inLink
////                        cloneSM.getGraph().removeEdge((LabeledLink) inLink);
//                        //add the inLink
//                        cloneSM.getGraph().addEdge(inLink.getSource(),addedInternalNode,addedInLink);
//                    }
//                }
//                //remove and add outLinks
//                if(replacedInternalNodesCombination.get(i).getOutLinks().size()>0){
//                    for(DefaultLink outLink: replacedInternalNodesCombination.get(i).getOutLinks()){
//                        String addedOutLinkId = LinkIdFactory.getLinkId(outLink.getUri(),addedInternalNode.getId(),outLink.getTarget().getId());
//                        LabeledLink addedOutLink = null;
//                        if(outLink.getTarget() instanceof InternalNode) {
//                            addedOutLink = new ObjectPropertyLink(addedOutLinkId, new Label(outLink.getUri()), ((ObjectPropertyLink) outLink).getObjectPropertyType());
//                        }
//                        else{
//                            addedOutLink = new DataPropertyLink(addedOutLinkId,new Label(outLink.getUri()));
//                        }
////                        //remove the outLink
////                        cloneSM.getGraph().removeEdge((LabeledLink) outLink);
//                        //add the outLink
//                        System.out.println("addedInternalNode:" + addedInternalNode.getId());
//                        System.out.println("outLink.getTarget:" + outLink.getTarget().getId());
//
//                        cloneSM.getGraph().addEdge(addedInternalNode,outLink.getTarget(),addedOutLink);
//                    }
//                }
//
////                //add the internal node
//////                InternalNode addedInternalNode = new InternalNode(internalNodesCombination.get(i).getId(),internalNodesCombination.get(i).getLabel());
////                cloneSM.getGraph().addVertex(internalNodesCombination.get(i));
////                //remove the internal node
////                cloneSM.getGraph().removeVertex(replacedInternalNodesCombination.get(i));
////                //add the corresponding incoming links
////                if(replacedInternalNodesCombination.get(i).getInLinks().size()>0){
////                    for(DefaultLink inLink: replacedInternalNodesCombination.get(i).getInLinks()){
////                        //add labeled link
////                        String addedInLinkId = LinkIdFactory.getLinkId(inLink.getUri(),inLink.getId(),internalNodesCombination.get(i).getId());
////                        LabeledLink addedLink = new ObjectPropertyLink(addedInLinkId,new Label(inLink.getUri()),((ObjectPropertyLink) inLink).getObjectPropertyType());
////                        cloneSM.getGraph().addEdge(inLink.getSource(),internalNodesCombination.get(i),addedLink);
////                        //add inLink
////                        internalNodesCombination.get(i).addInLink(addedLink);
////                    }
////                }
//
//            }
            cloneSM.setName(positiveSemanticModel.getName().replace(".csv","") + "_Same" + samePositiveSemanticModelIndex + ".csv");
            System.out.println("cloneSM:" + cloneSM.getName());

            assert evaluateWithInverse(positiveSemanticModel,cloneSM) == 1: "the semantic model is not same as the positive semantic model";
            if((saveSMGraphVizPath != null) && (saveSMJsonPath != null)){
                //save the same positive semantic model
                cloneSM.writeJson(saveSMJsonPath + cloneSM.getName().replace(".csv", "") + Params.MODEL_MAIN_FILE_EXT);
                GraphVizUtil.exportSemanticModelToGraphviz(cloneSM, GraphVizLabelType.LocalId,
                        GraphVizLabelType.LocalUri, true, true, saveSMGraphVizPath + cloneSM.getName().replace(".csv", "") + Params.GRAPHVIS_MAIN_FILE_EXT);
            }
            samePositiveSemanticModelsForOneSemanticModel.add(cloneSM);
        }
        assert samePositiveSemanticModelsForOneSemanticModel.size() == originalCombinationNum: "samePositiveSemanticModelsForOneSemanticModel.size != originalCombinationNum";

        return samePositiveSemanticModelsForOneSemanticModel;
    }


//    public static List<SemanticModel> getSamePositiveSemanticModelsForOneSemanticModel(SemanticModel positiveSemanticModel, Map<String,Set<String>> internalNodeUriWithIds){
//        //obtain map{key:internal_node_id,value:internal_node_uri} for the given positive semantic model
//        List<List<String>> internalNodesToBeReplaced = new ArrayList<List<String>>();
//        List<String> currentInternalNodesIdsCombination = new ArrayList<String>();
//        for(InternalNode internalNode: positiveSemanticModel.getInternalNodes()){
//            if(internalNodeUriWithIds.keySet().contains(internalNode.getUri())){
//                if(internalNodeUriWithIds.get(internalNode.getUri()).size()>1){
//                    currentInternalNodesIdsCombination.add(internalNode.getId());
//                    internalNodesToBeReplaced.add(new ArrayList<String>(internalNodeUriWithIds.get(internalNode.getUri())));
//                }
//            }
////            internalNodeIdWithUri.put(internalNode.getId(),internalNode.getUri());
//        }
//        List<List<String>> otherInternalNodesIdsCombinations = descartesRecursiveUnique(internalNodesToBeReplaced);
//        otherInternalNodesIdsCombinations.remove(currentInternalNodesIdsCombination);
//
//        SemanticModel cloneSM = null;
//        for(List<String> internalNodesIdsCombination: otherInternalNodesIdsCombinations){
//            cloneSM = positiveSemanticModel.clone();
//            assert cloneSM.getInternalNodes().size() == internalNodesIdsCombination.size(): "cloneSM.getInternalNodes.size != internalNodesIdsCombination.size";
//
//        }
//
//
//        //judge whether the internal node needs to be replaced
//
//
//        return null;
//    }

    public static List<SemanticModel> getNegativeSemanticModelsForSemanticModelWithOneColumnNode(SemanticModel positiveSemanticModel, SemanticModel startSemanticModelState, DirectedWeightedMultigraph<Node, DefaultLink> integrationGraph, JSONObject jsonObject, String saveSMGraphVizPath, String saveSMJsonPath) throws IOException {
        assert positiveSemanticModel.getColumnNodes().size() == 1: "positiveSemanticModel.columnNodes.size != 1";
        assert positiveSemanticModel.getInternalNodes().size() == 1: "positiveSemanticModel.internalNodes.size != 1";
        assert positiveSemanticModel.getGraph().edgeSet().size() == 1: "positiveSemanticModel.edges.size != 1";
        assert startSemanticModelState.getGraph().vertexSet().size() == startSemanticModelState.getColumnNodes().size(): "startSemanticModelState has not only one column node";
        List<SemanticModel> negativeSemanticModels = new ArrayList<SemanticModel>();
        List<Double> similarityScores =  new ArrayList<Double>();
        DefaultLink knownLink = new ArrayList<DefaultLink>(positiveSemanticModel.getGraph().edgeSet()).get(0);
        String linkSourceUriWithLinkUri = knownLink.getSource().getUri()+knownLink.getUri();
        ColumnNode knownColumnNode = startSemanticModelState.getColumnNodes().get(0);

        deleteFile(saveSMGraphVizPath);
        deleteFile(saveSMJsonPath);

        CreateFile(saveSMGraphVizPath);
        CreateFile(saveSMJsonPath);

        /**obtain all semantic types (contains correct and candidate semantic types 2023/04/04, note that some correct semantic types are not in the integration graph) for the added attribute nodes**/
        Set<SemanticType> allSemanticTypesForAddedAttributeNode = new HashSet<SemanticType>();
        allSemanticTypesForAddedAttributeNode = getSemanticTypes(positiveSemanticModel.getColumnNodes().get(0),false,true,4);

        Set<SemanticType> correctSemanticTypes = new HashSet<SemanticType>();
        correctSemanticTypes = getSemanticTypes(positiveSemanticModel.getColumnNodes().get(0),true,false,4);
        assert correctSemanticTypes.size() == 1: "correctSemanticTypes.size != 1";

        assert allSemanticTypesForAddedAttributeNode.size() < 5: "allSemanticTypesForAddedAttributeNode > 4";

        /**mntPts save the links whose node has same semantic types with the added attribute node**/
        Set<DefaultLink> mntPts = new HashSet<DefaultLink>();
        Map<Node,Set<DefaultLink>> mntPtNodeWithMntPtLinks = new HashMap<Node,Set<DefaultLink>>();
        Set<String> mntPtsWithSourceNodeIdAndLinkUri = new HashSet<String>();//used to check the mntPt with same source node id and link uri
        //loop all semantic types in allSemanticTypesForAddedAttributeNode, and find all mntPts
        for (SemanticType semanticType : allSemanticTypesForAddedAttributeNode) {
            for (DefaultLink link : integrationGraph.edgeSet()) {
                if ((link.getSource().getUri().equals(semanticType.getDomain().getUri())) && (link.getUri().equals(semanticType.getType().getUri())) && (!mntPtsWithSourceNodeIdAndLinkUri.contains(link.getSource().getId()+semanticType.getType().getUri().toString()))) {
                    mntPtsWithSourceNodeIdAndLinkUri.add(link.getSource().getId()+semanticType.getType().getUri().toString());
                    mntPts.add(link);
                }
            }
        }


        SemanticModel cloneSM = null;
        int index = 0;
        for(DefaultLink link: mntPts){
            if((link.getSource().getUri()+link.getUri()).equals(linkSourceUriWithLinkUri))
                continue;
            ++index;
            cloneSM = startSemanticModelState.clone();
            //add the internal node
            cloneSM.getGraph().addVertex(link.getSource());
            //add the link
            String addedLinkId = LinkIdFactory.getLinkId(link.getUri(),link.getSource().getId(),knownColumnNode.getId());
            LabeledLink addedLink = new DataPropertyLink(addedLinkId, new Label(link.getUri()));
            cloneSM.getGraph().addEdge(link.getSource(),knownColumnNode,addedLink);
            cloneSM.setName(positiveSemanticModel.getName().replace(".csv","")+"_negative" + index);
            assert cloneSM.getGraph().vertexSet().size() == positiveSemanticModel.getGraph().vertexSet().size(): "cloneSM.getGraph.vertexSet.size != positiveSemanticModel.getGraph.vertexSet.size";
            assert cloneSM.getGraph().edgeSet().size() == positiveSemanticModel.getGraph().edgeSet().size(): "cloneSM.getGraph.edgeSet.size != positiveSemanticModel.getGraph.edgeSet.size";
            double score = evaluateWithInverse(positiveSemanticModel,cloneSM);
            assert score < 1: "score >= 1";
            //save negative semantic models
            cloneSM.writeJson(saveSMJsonPath + "/" + cloneSM.getName().replace(".csv", "") + Params.MODEL_MAIN_FILE_EXT);
            GraphVizUtil.exportSemanticModelToGraphviz(cloneSM, GraphVizLabelType.LocalId,
                    GraphVizLabelType.LocalUri, true, true, saveSMGraphVizPath + "/" + cloneSM.getName().replace(".csv", "") + Params.GRAPHVIS_MAIN_FILE_EXT);
            similarityScores.add(score);
            negativeSemanticModels.add(cloneSM);
        }
        assert negativeSemanticModels.size() == similarityScores.size(): "negativeSemanticModels.size != similarityScores.size";
        if(similarityScores.size() > 0) {
            listToTxt(similarityScores, saveSMJsonPath + "/" + "similarity_scores.txt" );
        }
        return null;
    }

    public static void listToTxt(List<?> list,String savePath){
        File saveFile = new File(savePath);
        BufferedWriter bw;
        try{
            if(saveFile.exists())
                bw = new BufferedWriter(new FileWriter(savePath,true));
            else
                bw = new BufferedWriter(new FileWriter(savePath));
            for(int j=0;j<list.size();j++){
                bw.write(list.get(j).toString());
                bw.newLine();
                bw.flush();
            }
            bw.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

//    public static void addListToTxt(List<?> list,String savePath){
//        BufferedWriter bw;
//        try{
//            bw = new BufferedWriter((new FileWriter(savePath,true)));
//            for(int i=0;i<list.size();i++){
//                bw.write(list.get(i).toString());
//                bw.newLine();
//                bw.flush();
//            }
//            bw.close();
//        } catch (IOException e) {
//            e.printStackTrace();
//        }
//    }

    public static List<SemanticModel> getNegativeSemanticModelsForOneSemanticModel(String[] fileNames, SemanticModel positiveSemanticModel, DirectedWeightedMultigraph<Node, DefaultLink> integrationGraph, JSONObject jsonObject, Set<InternalNode> internalNodesWithUseOntPaths) throws Exception{
        negativeSemanticModelForTrainIndexForOnePositiveSemanticModel = 0;
        String dataSourceFileName = fileNames[0];//s01
        String fileName1 = fileNames[0] + "_" + fileNames[1] + "_" +fileNames[2];//s01_Sub1_1
        String fileName2 = fileName1 + "_" + fileNames[3];//s01_Sub1_1_Same1
//        String saveSMGraphVizPath = "D:\\ASM\\CRM\\negative-models\\sub-same-negative-models-graphviz-all\\" + dataSourceFileName + "\\" + fileName1 + "\\" + fileName2 + "\\";
//        String saveSMJsonPath = "D:\\ASM\\CRM\\negative-models\\sub-same-negative-models-json-all\\" + dataSourceFileName + "\\" + fileName1 + "\\" + fileName2 + "\\";

//        String saveSMGraphVizPath = Params.ROOT_DIR_2023 + "negative-models\\sub-same-negative-models-graphviz-all\\" + dataSourceFileName + "\\" + fileName1 + "\\" + fileName2 + "\\";
//        String saveSMJsonPath = Params.ROOT_DIR_2023 + "negative-models\\sub-same-negative-models-json-all\\" + dataSourceFileName + "\\" + fileName1 + "\\" + fileName2 + "\\";

//        String saveSMGraphVizPath = Params.ROOT_DIR_2023_LINUX + "negative-models/sub-same-negative-models-graphviz-all/" + dataSourceFileName + "/" + fileName1 + "/" + fileName2 + "/";
//        String saveSMJsonPath = Params.ROOT_DIR_2023_LINUX + "negative-models/sub-same-negative-models-json-all/" + dataSourceFileName + "/" + fileName1 + "/" + fileName2 + "/";

//        String saveSMGraphVizPath = Params.EDM_ROOT_DIR_2023 + "negative-models/sub-same-negative-models-graphviz-all/" + dataSourceFileName + "/" + fileName1 + "/" + fileName2 + "/";
//        String saveSMJsonPath = Params.EDM_ROOT_DIR_2023 + "negative-models/sub-same-negative-models-json-all/" + dataSourceFileName + "/" + fileName1 + "/" + fileName2 + "/";

        String saveSMGraphVizPath = Params.EDM_ROOT_DIR_2023_LINUX + "negative-models/sub-same-negative-models-graphviz-all/" + dataSourceFileName + "/" + fileName1 + "/" + fileName2 + "/";
        String saveSMJsonPath = Params.EDM_ROOT_DIR_2023_LINUX + "negative-models/sub-same-negative-models-json-all/" + dataSourceFileName + "/" + fileName1 + "/" + fileName2 + "/";


        /**generate all negative semantic models for one positive semantic model**/
        List<ColumnNode> columnNodes = positiveSemanticModel.getColumnNodes();
        SemanticModel startSemanticModel = null;

        List<SemanticModel> negativeSemanticModels = new ArrayList<SemanticModel>();

        if(columnNodes.size()==1){
            startSemanticModel = positiveSemanticModel.clone();
            for(DefaultLink link: positiveSemanticModel.getGraph().edgeSet()){
                startSemanticModel.getGraph().removeVertex(link.getSource());
//                startSemanticModel.getGraph().removeVertex(link.getTarget());
                startSemanticModel.getGraph().removeEdge((LabeledLink) link);
            }
            assert startSemanticModel.getGraph().edgeSet().size() == 0: "startSemanticModel.edges.size != 0";
            assert startSemanticModel.getGraph().vertexSet().size() == startSemanticModel.getColumnNodes().size(): "startSemanticModel has not only the column node";

            getNegativeSemanticModelsForSemanticModelWithOneColumnNode(positiveSemanticModel,startSemanticModel,integrationGraph,jsonObject,saveSMGraphVizPath,saveSMJsonPath);

        }

        else{
            System.out.println("remove one attribute node each time as the new start semantic model");
            deleteFile(saveSMGraphVizPath);
            deleteFile(saveSMJsonPath);

            CreateFile(saveSMGraphVizPath);
            CreateFile(saveSMJsonPath);

            for(ColumnNode columnNode: columnNodes){
                startSemanticModel = positiveSemanticModel.clone();
                startSemanticModel = getSubSemanticModels(startSemanticModel,null,new ArrayList<String>(Arrays.asList(columnNode.getColumnName())),null,null);
                assert startSemanticModel.getColumnNodes().size() == columnNodes.size()-1: "startSemanticModel.columnNodes.size != initialSemanticModel.columnNodes.size - 1";
                //obtain and save all negative semantic models for this start semantic model
                beamSearchForTrain(positiveSemanticModel,startSemanticModel,integrationGraph,columnNodes,jsonObject,saveSMGraphVizPath,saveSMJsonPath,internalNodesWithUseOntPaths);
            }
        }

//        List<String> columnNames = new ArrayList<String>();
//        List<SemanticModel> startSemanticModels = new ArrayList<SemanticModel>();
////        List<List<String>> delColumnNamesList = new ArrayList<List<String>>();
//        for(ColumnNode columnNode: columnNodes){
////            delColumnNamesList.add(new ArrayList<String>(Arrays.asList(columnNode.getColumnName())));
//            startSemanticModel = predictSemanticModel.clone();
//            startSemanticModel = getSubSemanticModels(startSemanticModel,null,new ArrayList<String>(Arrays.asList(columnNode.getColumnName())),null,null);
//            assert startSemanticModel.getColumnNodes().size() == columnNodes.size()-1: "startSemanticModel.columnNodes.size != initialSemanticModel.columnNodes.size - 1";
//            startSemanticModels.add(startSemanticModel);
//            startSemanticModel = null;
//        }
//
//        assert startSemanticModels.size() == columnNodes.size(): "startSemanticModels.size != columnNodes.size";

//        List<SemanticModel> negativeSemanticModels = new ArrayList<SemanticModel>();
//        for(SemanticModel startSearchSemanticModel: startSemanticModels){
//            negativeSemanticModels = BeamSearch();
//        }


        return negativeSemanticModels;
    }

    public static Map<SemanticModel,List<SemanticModel>> getNegativeSemanticModelsForEmbedding(int predictSourceIndex, SemanticModel predictSemanticModel, DirectedWeightedMultigraph<Node, DefaultLink> integrationGraph, JSONObject jsonObject, Set<InternalNode> internalNodesWithUseOntPaths) throws Exception{
        //obtain all sub positive semantic models
        List<SemanticModel> positiveSemanticModels = new ArrayList<SemanticModel>();
        List<SemanticModel> subPositiveSemanticModels = new ArrayList<SemanticModel>();
        List<SemanticModel> subPositiveSemanticModelsWithOnlyColumnNode = new ArrayList<SemanticModel>();
        List<String> unique_columns = new ArrayList<String>();
//        String SemanticMoldes_Path = "D:\\ASM\\CRM\\";
//        String SemanticMoldes_Path = Params.ROOT_DIR_2023;
//        String SemanticMoldes_Path = Params.ROOT_DIR_2023_LINUX;
//        String SemanticMoldes_Path = Params.EDM_ROOT_DIR_2023;
        String SemanticMoldes_Path = Params.EDM_ROOT_DIR_2023_LINUX;

        String negativeSemanticModelGraphvizFilePath = SemanticMoldes_Path + "negative-models/negative-models-graphviz";
        String negativeSemanticModelJsonFilePath = SemanticMoldes_Path + "negative-models/negative-models-json";

        CreateFile(negativeSemanticModelGraphvizFilePath);
        CreateFile(negativeSemanticModelJsonFilePath);
        List<SemanticModel> negativeSemanticModels = new ArrayList<SemanticModel>();
        Map<SemanticModel,List<SemanticModel>> subPositiveSemanticModelWithSubNegativeSemanticModels = new HashMap<SemanticModel,List<SemanticModel>>();
        Map<List<String>,List<SemanticModel>> columnNamesCombinationWithNegativeSemanticModels = new HashMap<List<String>,List<SemanticModel>>();
        List<List<ColumnNode>> columnNodesCombinations = new ArrayList<List<ColumnNode>>();
        List<List<String>> columnNamesCombinations = new ArrayList<List<String>>();
        List<SemanticModel> allNegativeSemanticModelsForPositiveSemanticModel = new ArrayList<SemanticModel>();
        Map<SemanticModel,List<String>> subPositiveSemanticModelWithDelColumnNamesCombination = new HashMap<SemanticModel,List<String>>();
        SemanticModel cloneOriginNegativeSemanticModel = null;

//        //test for "assert"
//        int count = 0;
//        assert count == 1: "count != 1";

        //judge whether the integration graph contains all column nodes in predictSemanticModel
        assert integrationGraph.vertexSet().containsAll(predictSemanticModel.getColumnNodes()): "some column nodes of predict semantic model are not in the integration graph";

        subPositiveSemanticModels = getAllSubPositiveSemanticModels(predictSemanticModel,predictSourceIndex,unique_columns,SemanticMoldes_Path + "positive-models/",true);
        System.out.println(predictSemanticModel.getName() + " sub positive semantic models size:" + subPositiveSemanticModels.size());

        /**test for generating all negative semantic models for a given sub positive semantic model with only one attribute node**/
//        for(SemanticModel sub_semantic_model: subPositiveSemanticModels){
//            if(sub_semantic_model.getColumnNodes().size()==1){
//                subPositiveSemanticModelsWithOnlyColumnNode.add(sub_semantic_model);
//            }
//        }
//        assert subPositiveSemanticModelsWithOnlyColumnNode.size() == predictSemanticModel.getColumnNodes().size(): "subPositiveSemanticModelsWithOnlyColumnNode.size != predictSemanticModel.getColumnNodes().size";
//        System.out.println("subPositiveSemanticModelsWithOnlyColumnNode.size:" + subPositiveSemanticModelsWithOnlyColumnNode.size());
//
//        saveSubSemanticModelsAsModelAndJson(subPositiveSemanticModelsWithOnlyColumnNode,"D:\\ASM\\CRM\\positive-models\\");

        /**test for generating all negative semantic models for a given sub positive semantic model with only one attribute node**/


//        positiveSemanticModels = getAllPositiveSemanticModels(predictSemanticModel,predictSourceIndex,unique_columns,SemanticMoldes_Path + "positive-models/");
//        System.out.println(predictSemanticModel.getName() + " posotive semantic models size:" + positiveSemanticModels.size());

        allNegativeSemanticModelsForPositiveSemanticModel = new ArrayList<SemanticModel>();//save all negative semantic models for a certain positive semantic model
        int index = 0;
        for(SemanticModel subSM: subPositiveSemanticModels){
            if(++index>1)
                break;
            //obtain all column node combinations, and save them to columnNodesCombinations
            if(subSM.getColumnNodes().size()>1) {
                List<ColumnNode> columnNodesCombination = subSM.getColumnNodes();
                assert columnNodesCombination.size() > 1 && columnNodesCombination.size() <= predictSemanticModel.getColumnNodes().size() : "column nodes combination size is not correct";
                columnNodesCombinations.add(columnNodesCombination);
                //obtain map with key: column node combination, value: deleted column name combination
                List<String> delColumnNamesCombination = new ArrayList<String>();
                for(ColumnNode columnNode:predictSemanticModel.getColumnNodes()){
                    if(!columnNodesCombination.contains(columnNode))
                        delColumnNamesCombination.add(columnNode.getColumnName());
                }
                assert (columnNodesCombination.size()+delColumnNamesCombination.size()) == predictSemanticModel.getColumnNodes().size(): "columnNodesCombination and delColumnNamesCombination is not correct";
                subPositiveSemanticModelWithDelColumnNamesCombination.put(subSM,delColumnNamesCombination);
            }
            /**obtain partial negative semantic models based on the current start search sub semantic model**/
//            negativeSemanticModels = beamSearch(predictSemanticModel, subSM, integrationGraph, predictSemanticModel.getColumnNodes(), "", jsonObject);
//            if(negativeSemanticModels.size()>0)
//                allNegativeSemanticModelsForPositiveSemanticModel.addAll(negativeSemanticModels);

            /**test for predicting correct semantic model**/
            negativeSemanticModels = beamSearchForPredict(predictSemanticModel, subSM, integrationGraph, predictSemanticModel.getColumnNodes(), "", jsonObject, internalNodesWithUseOntPaths);
            if(negativeSemanticModels.size()>0) {
                SemanticModel resultSemanticModel = negativeSemanticModels.get(0);
            }
            else{
                System.out.println("cannot predict correct semantic model");
            }
        }
//        assert columnNodesCombinations.size() == (subPositiveSemanticModels.size()-predictSemanticModel.getColumnNodes().size()): "columnNodesCombinations.size != subPositiveSemanticModel.size without one column";
//        assert subPositiveSemanticModelWithDelColumnNamesCombination.size() == (subPositiveSemanticModels.size()-predictSemanticModel.getColumnNodes().size()): "subPositiveSemanticModelWithDelColumnNamesCombination.size != subPositiveSemanticModel.size without one column";
        //obtain all negative semantic models for the original positive semantic model
        subPositiveSemanticModelWithSubNegativeSemanticModels.put(predictSemanticModel,allNegativeSemanticModelsForPositiveSemanticModel);

//        //obtain all negative semantic models for each sub positive semantic model
//        //loop all columnNodesCombinationWithNegativeSemanticModels
//        for(Map.Entry<SemanticModel, List<String>> subPositiveSemanticModelWithDelColumnNamesCombinationEntry : subPositiveSemanticModelWithDelColumnNamesCombination.entrySet()){
//            //if the sub positive semantic model equals the original positive (predict) semantic model, we don't need to conduct these operations
//            if(subPositiveSemanticModelWithDelColumnNamesCombinationEntry.getKey().getColumnNodes().containsAll(predictSemanticModel.getColumnNodes())){
//                continue;
//            }
//            allNegativeSemanticModelsForPositiveSemanticModel = new ArrayList<SemanticModel>();//save all negative semantic models for a certain positive semantic model
//            //loop all negative semantic models for the original positive semantic model
//            for(SemanticModel negativeOriginSemanticModel: subPositiveSemanticModelWithSubNegativeSemanticModels.get(predictSemanticModel)){
//                cloneOriginNegativeSemanticModel = negativeOriginSemanticModel.clone();
//                SemanticModel subNegativeSemanticModel = getSubSemanticModels(cloneOriginNegativeSemanticModel, 0, subPositiveSemanticModelWithDelColumnNamesCombinationEntry.getValue(), null, null);
//                //if the score between subNegativeSemanticModel and subPositiveSemanticModel is less than 1, add it into the allNegativeSemanticModelsForPositiveSemanticModel, else ignore it
//                double score = evaluate(subPositiveSemanticModelWithDelColumnNamesCombinationEntry.getKey(),subNegativeSemanticModel);
//                if(score<1)
//                    allNegativeSemanticModelsForPositiveSemanticModel.add(subNegativeSemanticModel);
//            }
//            subPositiveSemanticModelWithSubNegativeSemanticModels.put(subPositiveSemanticModelWithDelColumnNamesCombinationEntry.getKey(),allNegativeSemanticModelsForPositiveSemanticModel);
//        }
//        assert subPositiveSemanticModelWithSubNegativeSemanticModels.size() == (subPositiveSemanticModels.size()-predictSemanticModel.getColumnNodes().size()+1): "subPositiveSemanticModelWithSubNegativeSemanticModels.size != positiveSemanticModels.size";

        return subPositiveSemanticModelWithSubNegativeSemanticModels;
    }

    public static void getSpecifiedSemanticModelForEvaluateTest(SemanticModel initialSemanticModel12) throws IOException {
        //focus on the semantic model 12
        //replace "Image -> Man-Made_Object1" -> "Man-Made_Object1 -> Image"
        int initialEdgeNum = initialSemanticModel12.getGraph().edgeSet().size();
        int initialNodeNum = initialSemanticModel12.getGraph().vertexSet().size();
        LabeledLink removedLink = null;
        Node type1 = null;
        Node removedLinkSourceNode = null;
        Node removedLinkTargetNode = null;
        List<LabeledLink> removedLinksList = new ArrayList<>();
        for(DefaultLink link: initialSemanticModel12.getGraph().edgeSet()){
            if(link.getUri().equals("http://erlangen-crm.org/current/P138_represents")) {
                removedLinkSourceNode = link.getSource();
                removedLink = (LabeledLink) link;
                removedLinkTargetNode = link.getTarget();
            }
            if((link.getTarget().getId().equals("http://erlangen-crm.org/current/E55_Type1")) || (link.getSource().getId().equals("http://erlangen-crm.org/current/E55_Type1"))){
                removedLinksList.add((LabeledLink) link);
            }
        }
        initialSemanticModel12.getGraph().removeEdge(removedLink);

        String addedLinkId = LinkIdFactory.getLinkId("http://erlangen-crm.org/current/P138i_has_representation",removedLinkTargetNode.getId(),removedLinkSourceNode.getId());
        LabeledLink addedLink = new ObjectPropertyLink(addedLinkId, new Label("http://erlangen-crm.org/current/P138i_has_representation"),ObjectPropertyType.Direct);
        initialSemanticModel12.getGraph().addEdge(removedLinkTargetNode,removedLinkSourceNode,addedLink);

        assert removedLinksList.size() == 2: "removedLinksList.size != 2";
        //replace "Type1 -> Type2"
        //add "Type2"
        InternalNode type2 = new InternalNode("http://erlangen-crm.org/current/E55_Type2",new Label("http://erlangen-crm.org/current/E55_Type"));
        initialSemanticModel12.getGraph().addVertex(type2);
        //add links and remove links
        for(LabeledLink link: removedLinksList){
            if(link.getSource().getUri().equals(type2.getUri())){
                type1 = link.getSource();
                String addedLink1Id = LinkIdFactory.getLinkId(link.getUri(),type2.getId(),link.getTarget().getId());
                LabeledLink addedLink1 = new DataPropertyLink(addedLink1Id,new Label(link.getUri()));
                initialSemanticModel12.getGraph().addEdge(type2,link.getTarget(),addedLink1);
                initialSemanticModel12.getGraph().removeEdge(link);
            }
            else if(link.getTarget().getUri().equals(type2.getUri())){
                String addedLink2Id = LinkIdFactory.getLinkId(link.getUri(),link.getSource().getId(),type2.getId());
                LabeledLink addedLink2 = new ObjectPropertyLink(addedLink2Id,new Label(link.getUri()),ObjectPropertyType.Direct);
                initialSemanticModel12.getGraph().addEdge(link.getSource(),type2,addedLink2);
                initialSemanticModel12.getGraph().removeEdge(link);
            }
        }
        //remove type1
        initialSemanticModel12.getGraph().removeVertex(type1);

        assert initialSemanticModel12.getGraph().edgeSet().size() == initialEdgeNum: "initialSemanticModel12.edge.size != initialEdgeNum";
        assert initialSemanticModel12.getGraph().vertexSet().size() == initialNodeNum: "initialSemanticModel12.node.size != initialNodeNum";

        initialSemanticModel12.writeJson("D:\\ASM\\CRM\\evaluate-test-models-json-20230412\\" + initialSemanticModel12.getName() + ".model.json");
        GraphVizUtil.exportSemanticModelToGraphviz(initialSemanticModel12, GraphVizLabelType.LocalId,
                GraphVizLabelType.LocalUri, true, true, "D:\\ASM\\CRM\\evaluate-test-models-graphviz-20230412\\" + initialSemanticModel12.getName() + Params.GRAPHVIS_MAIN_FILE_EXT);

    }

    public static Map<String,Set<InternalNode>> getInternalNodeUriWithInternalNodes(DirectedWeightedMultigraph<Node, DefaultLink> integrationGraph){
        Map<String,Set<InternalNode>> internalNodeUriWithInternalNodes = new HashMap<String,Set<InternalNode>>();
        int internalNodeNumInIntegrationGraph = 0;
        for(Node node: integrationGraph.vertexSet()){
            if(node instanceof InternalNode){
                ++internalNodeNumInIntegrationGraph;
                if(internalNodeUriWithInternalNodes.keySet().contains(node.getUri())){
                    Set<InternalNode> internalNodes = new HashSet<InternalNode>(internalNodeUriWithInternalNodes.get(node.getUri()));
                    internalNodes.add((InternalNode) node);
                    internalNodeUriWithInternalNodes.put(node.getUri(),internalNodes);
                }
                else{
                    internalNodeUriWithInternalNodes.put(node.getUri(),new HashSet<InternalNode>(Arrays.asList((InternalNode) node)));
                }
            }
        }
        int valuesNumInMap = 0;
        for(String internalNodeUri: internalNodeUriWithInternalNodes.keySet()){
            valuesNumInMap += internalNodeUriWithInternalNodes.get(internalNodeUri).size();
        }
        assert valuesNumInMap == internalNodeNumInIntegrationGraph: "valuesNumInMap != internalNodeNumInIntegrationGraph";

        return internalNodeUriWithInternalNodes;
    }


    public static Map<String,Set<String>> getInternalNodeUriWithIds(DirectedWeightedMultigraph<Node, DefaultLink> integrationGraph){
        Map<String,Set<String>> internalNodeUriWithIds = new HashMap<String,Set<String>>();
        int internalNodeNumInIntegrationGraph = 0;
        for(Node node: integrationGraph.vertexSet()){
            if(node instanceof InternalNode){
                ++internalNodeNumInIntegrationGraph;
                if(internalNodeUriWithIds.keySet().contains(node.getUri())){
                    Set<String> internalNodeIds = new HashSet<String>(internalNodeUriWithIds.get(node.getUri()));
                    internalNodeIds.add(node.getId());
                    internalNodeUriWithIds.put(node.getUri(),internalNodeIds);
                }
                else{
                    internalNodeUriWithIds.put(node.getUri(),new HashSet<String>(Arrays.asList(node.getId())));
                }
            }
        }
        int valuesNumInMap = 0;
        for(String internalNodeUri: internalNodeUriWithIds.keySet()){
            valuesNumInMap += internalNodeUriWithIds.get(internalNodeUri).size();
        }
        assert valuesNumInMap == internalNodeNumInIntegrationGraph: "valuesNumInMap != internalNodeNumInIntegrationGraph";

        return internalNodeUriWithIds;
    }

    /**test for obtaining the ancestor nodes for the given two nodes**/
    public static void testForGetCommonAncestorNodes(DirectedWeightedMultigraph<Node, DefaultLink> integrationGraph){
        Node node1 = null;
        Node node2 = null;
        for(Node node: integrationGraph.vertexSet()){
            if((node instanceof InternalNode) && (node.getId().equals("http://erlangen-crm.org/current/E82_Actor_Appellation1")))
                node1 = node;
            else if((node instanceof InternalNode) && (node.getId().equals("http://erlangen-crm.org/current/E35_Title1")))
                node2 = node;
            if((node1 != null) && (node2 != null)){
                break;
            }
        }
        getCommonAncestorNodes(node1,node2,3,null);
    }

    public static void testForDescartes(){
        List<String> l11 = Arrays.asList("1","2","3");
        List<String> l12 = Arrays.asList("4","5","6");
        List<String> l21 = Arrays.asList("7","8","9");
        List<String> l22 = Arrays.asList("10","11","12");

        List<List<String>> l1 = new ArrayList<List<String>>();
        l1.add(l11);
        l1.add(l12);
        List<List<String>> l2 = new ArrayList<List<String>>();
        l2.add(l21);
        l2.add(l22);

        System.out.println("l1:" + l1);
        System.out.println("l2:" + l2);

        List<List<List<String>>> originalList = new ArrayList<List<List<String>>>(Arrays.asList(l1,l2));
        List<List<String>> lists = descartesRecursiveForDoubleList(originalList);

        System.out.println("lists:" + lists);
    }

    public static void testForWriteJson() throws Exception {
        SemanticModel testSemanticModel = semanticModels.get(0);
        System.out.println("testSemanticModel links size:" + testSemanticModel.getGraph().edgeSet().size());
        System.out.println("testSemanticModel nodes size:" + testSemanticModel.getGraph().vertexSet().size());

        System.out.println("testSemanticModel.getId:"+testSemanticModel.getId()+"|testSemanticModel.getName:"+testSemanticModel.getName());
        testSemanticModel.setName("s01-test");
        System.out.println("testSemanticModel.getId:"+testSemanticModel.getId()+"|testSemanticModel.getName:"+testSemanticModel.getName());

        testSemanticModel.writeJson("D:\\ASM\\CRM\\model-json-20230411-test\\" + testSemanticModel.getName() + ".model.json");

        String testSemanticModelJsonPath = "D:\\ASM\\CRM\\model-json-20230411-test\\";
        System.out.println("testSemanticModelJsonPath:" + testSemanticModelJsonPath);
        List<SemanticModel> testSemanticModelList = ModelReader.importSemanticModelsFromJsonFiles(testSemanticModelJsonPath, Params.MODEL_MAIN_FILE_EXT);
        System.out.println("testSemanticModelList.size:" + testSemanticModelList.size());

        System.out.println("testSemanticModel2 links size:" + testSemanticModelList.get(0).getGraph().edgeSet().size());
        System.out.println("testSemanticModel2 nodes size:" + testSemanticModelList.get(0).getGraph().vertexSet().size());
    }

    public static void testForEvaluateModels() throws Exception {
//        getSpecifiedSemanticModelForEvaluateTest(semanticModels.get(11)); //get specified semantic model for evaluate test

        //evaluate the initial semantic model 12 and the changed semantic model 12
//        setOntologyManagerAndOntModel();
        SemanticModel positiveSemanticModel12 = semanticModels.get(11);
//        SemanticModel evaluateSemanticModel12 = semanticModels.get(11);
        SemanticModel evaluateSemanticModel12 = ModelReader.importSemanticModelsFromJsonFiles("D:\\ASM\\CRM\\evaluate-test-models-json-20230412", Params.MODEL_MAIN_FILE_EXT).get(0);
//        ModelEvaluation modelEvaluation = evaluateSemanticModel12.newEvaluate(positiveSemanticModel12,ontologyManager,ontModel);
        ModelEvaluation modelEvaluation = evaluateSemanticModel12.newEvaluateForSpecifiedUri(positiveSemanticModel12);


        System.out.println("precision:" + modelEvaluation.getPrecision());
        System.out.println("recall:" + modelEvaluation.getRecall());
        System.out.println("F1 score:" + (2 * (modelEvaluation.getPrecision() * modelEvaluation.getRecall()) / (modelEvaluation.getPrecision() + modelEvaluation.getRecall())));

    }

    public static void testForGetSamePositiveSemanticModelsForOneSemanticModel(DirectedWeightedMultigraph<Node,DefaultLink> integrationGraph) throws IOException {
        //obtain the map{key:internal_node_uri,values:[internal_node_id]}
//        Map<String,Set<String>> internalNodeUriWithIds = getInternalNodeUriWithIds(integrationGraph);
        //obtain the map{key:internal_node_uri,values:[internal_node]}
        Map<String,Set<InternalNode>> internalNodeUriWithInternalNodes = getInternalNodeUriWithInternalNodes(integrationGraph);

        SemanticModel positiveSemanticModel = importSemanticModelFromJsonFile("D:\\ASM\\CRM\\positive-models\\sub-positive-models-json-all\\s01\\s01_Sub7_1.model.json",Params.MODEL_MAIN_FILE_EXT);
        System.out.println("positiveSemanticModel:" + positiveSemanticModel.getName());

        //create save file

        List<SemanticModel> samePositiveSemanticModelsForOneSemanticModel = new ArrayList<SemanticModel>();
        samePositiveSemanticModelsForOneSemanticModel = getSamePositiveSemanticModelsForOneSemanticModel(positiveSemanticModel,internalNodeUriWithInternalNodes,null,null);
        System.out.println("samePositiveSemanticModelsForOneSemanticModel:"+samePositiveSemanticModelsForOneSemanticModel.size());
    }

    public static void testForSaveSimilarityScores(){
        String savePath = "D:\\ASM\\CRM\\similarity-scores-save-test\\similarity_scores.txt";
        List<Double> similarityScores1 = new ArrayList<Double>(Arrays.asList(0.0,1.1,2.2));
        List<Double> similarityScores2 = new ArrayList<Double>(Arrays.asList(5.5,6.6,7.7,8.8));
        File saveFilePath = new File(savePath);

        listToTxt(similarityScores1,savePath);
        listToTxt(similarityScores2,savePath);
    }

    private static int recursiveNum = 0;
    public static void testForRecursive(){
        ++recursiveNum;
        int tempNum = recursiveNum;
        System.out.println("进入到" + tempNum + "层循环");
        if(recursiveNum>5)
            return;
        testForRecursive();
        System.out.println("返回到" + tempNum + "层循环");
    }

    public static void testForObtainingSamplesNumForOneDataSource(String dataSourceName,String savePath) throws IOException {
        File subFilesPath = new File(savePath+"/"+dataSourceName);
        File[] subFiles = subFilesPath.listFiles();
        int samplesNumForOneSubFile = 0;
        Map<String,Integer> subFileWithSamplesNum = new HashMap<String,Integer>();
        File[] subSameFiles = new File[]{};
        int samplesNumForOneSubSame = 0;
        Map<String,Integer> subSameFileWithSamplesNum = new HashMap<String,Integer>();
        File[] subSameModelsJson = new File[]{};

        System.out.println("subSameFiles:" + subSameFiles.length);
        for(File subFile: subFiles){//s01_Sub1_1
            samplesNumForOneSubFile = 0;
            System.out.println("subFile:" + subFile);
            subSameFiles = subFile.listFiles();
            for(File subSameFile: subSameFiles){//s01_Sub1_1_Same_1
                System.out.println("subSameFile:" + subSameFile);
                samplesNumForOneSubSame = 0;
                subSameModelsJson = subSameFile.listFiles();
                for(File subSameModelJson: subSameModelsJson){//s01_Sub1_1_Same_1_negative1.model.json
                    if(subSameModelJson.getName().endsWith(Params.MODEL_MAIN_FILE_EXT)){
                        ++samplesNumForOneSubSame;
                    }
                }
                subSameFileWithSamplesNum.put(subSameFile.toString(),samplesNumForOneSubSame);
                System.out.println("samplesNumForOneSubSame:" + samplesNumForOneSubSame);
                samplesNumForOneSubFile += samplesNumForOneSubSame;
            }
            subFileWithSamplesNum.put(subFile.toString(),samplesNumForOneSubFile);
        }

        int sum1 = 0;
        int sum2 = 0;
        for(String key1: subFileWithSamplesNum.keySet()){
            sum1 += subFileWithSamplesNum.get(key1);
        }
        for(String key2: subSameFileWithSamplesNum.keySet()){
            sum2 += subSameFileWithSamplesNum.get(key2);
        }
        System.out.println("sum1:" + sum1);
        System.out.println("sum2:" + sum2);
        assert sum1 == sum2: "sum1 != sum2";
        System.out.println("subFiles.num:" + subFiles.length);
    }

    public static void getIntegrationGraphTriplesForModelTraining() throws Exception {
        String SemanticModelsPath = Params.ROOT_DIR_2023; // 这里是models-json-20230313文件夹的目录
        List<SemanticModel> allSemanticModels = null;
        List<SemanticModel> allSemanticModelsWithCandidateSemanticTypes = null;
        int predictSourceIndex = 0;
        SemanticModel predictSemanticModel = null;
        List<SemanticModel> trainSemanticModels = new ArrayList<SemanticModel>();
        int sourceNum = 29;
        DirectedWeightedMultigraph<Node, DefaultLink> integrationGraph = null;
        Set<String> allTriples = new HashSet<String>();
        Set<String> allPreNodes = new HashSet<String>();
        Set<String> allProNodes = new HashSet<String>();

        allSemanticModels = ModelReader.importSemanticModelsFromJsonFiles(SemanticModelsPath + "models-json-20230313", Params.MODEL_MAIN_FILE_EXT);
        allSemanticModelsWithCandidateSemanticTypes = ModelReader.importSemanticModelsFromJsonFiles(SemanticModelsPath + "labeled-models-json-20230402", Params.MODEL_MAIN_FILE_EXT);

        for(int j=0;j<29;j++) {

//            if(j<9)
//                continue;
//            else if(j>9)
//                break;

            predictSourceIndex = j;
            predictSemanticModel = allSemanticModelsWithCandidateSemanticTypes.get(predictSourceIndex);

            // get train semantic models index array
            trainSemanticModels = new ArrayList<SemanticModel>();
            for (int i = 0; i < sourceNum; i++) {
                if (i != predictSourceIndex) {
                    trainSemanticModels.add(allSemanticModels.get(i));
                }
            }

            //obtain the integration for generate negative semantic models
            integrationGraph = getIntegrationGraphWithCandidateSemanticTypesForTraining(predictSemanticModel, trainSemanticModels);

            System.out.println(predictSemanticModel.getName() + " integrationGraph links size:" + integrationGraph.edgeSet().size());
            System.out.println(predictSemanticModel.getName() + " integrationGraph nodes size:" + integrationGraph.vertexSet().size());
            System.out.println("---------------------------------integrationGraph nodes size---------------------------------");

            System.out.println("---------------------------------get " + predictSemanticModel.getName() + " triples---------------------------------");
            for(DefaultLink link: integrationGraph.edgeSet()){
                String triple = null;
                String pre_head = null;
                String pre_tail = null;
                String pro_head = null;
                String pro_tail = null;
                if((link.getSource() instanceof InternalNode) && (link.getTarget() instanceof InternalNode)){
                    triple = getLabelName(link.getSource().getId()) + "," + getLabelName(link.getUri()) + "," + getLabelName(link.getTarget().getId());
                    pre_head = link.getSource().getId();
                    pre_tail = link.getTarget().getId();
                    pro_head = getLabelName(link.getSource().getId());
                    pro_tail = getLabelName(link.getTarget().getId());
                }
                else{
                    triple = getLabelName(link.getSource().getId()) + "," + getLabelName(link.getUri()) + "," + ((ColumnNode) link.getTarget()).getColumnName();
                    pre_head = link.getSource().getId();
                    pre_tail = ((ColumnNode) link.getTarget()).getColumnName();
                    pro_head = getLabelName(link.getSource().getId());
                    pro_tail = ((ColumnNode) link.getTarget()).getColumnName();
                }

                // add node string into allNodes
                allPreNodes.add(pre_head);
                allPreNodes.add(pre_tail);
                allProNodes.add(pro_head);
                allProNodes.add(pro_tail);

                if(!(allTriples.contains(triple))){
                    allTriples.add(triple);
                }
            }
            System.out.println("allTriples.size:" + allTriples.size());
        }
        assert allPreNodes.size() == allProNodes.size(): "allPreNodes.size != allProNodes.size";

        //save triples to txt
        BufferedWriter bw;
        try{
            bw = new BufferedWriter(new FileWriter("D:/ASM/CRM/allTriples.txt"));
            for(String triple: allTriples) {
//                System.out.println("triplesForOneRegionSemanticModels:" + triplesForOneRegionSemanticModel);
                bw.write(triple);
                bw.newLine();
                bw.flush();
            }
            bw.close();
        } catch (IOException e) {
            e.printStackTrace();
        }

        //save preNodes to txt
        try{
            bw = new BufferedWriter(new FileWriter("D:/ASM/CRM/allPreNodes.txt"));
            for(String preNode: allPreNodes) {
//                System.out.println("triplesForOneRegionSemanticModels:" + triplesForOneRegionSemanticModel);
                bw.write(preNode);
                bw.newLine();
                bw.flush();
            }
            bw.close();
        } catch (IOException e) {
            e.printStackTrace();
        }

        //save proNodes to txt
        try{
            bw = new BufferedWriter(new FileWriter("D:/ASM/CRM/allProNodes.txt"));
            for(String proNode: allProNodes) {
//                System.out.println("triplesForOneRegionSemanticModels:" + triplesForOneRegionSemanticModel);
                bw.write(proNode);
                bw.newLine();
                bw.flush();
            }
            bw.close();
        } catch (IOException e) {
            e.printStackTrace();
        }

    }

    public static void main(String[] args) throws Exception {

        int sourceNum = 29;
        int predictSourceIndex = 0;

//        String SemanticMoldesPath = "D:\\ASM\\CRM\\"; // 这里是models-json-20230313文件夹的目录
//        String SemanticMoldesPath = Params.ROOT_DIR_2023; // 这里是models-json-20230313文件夹的目录
//        String SemanticMoldesPath = Params.ROOT_DIR_2023_LINUX; // 这里是models-json-20230313文件夹的目录
//        String SemanticMoldesPath = Params.EDM_ROOT_DIR_2023; // 这里是models-json-20230313文件夹的目录
        String SemanticMoldesPath = Params.EDM_ROOT_DIR_2023_LINUX; // 这里是models-json-20230313文件夹的目录

        List<SemanticModel> trainSemanticModels = new ArrayList<SemanticModel>();
        SemanticModel predictSemanticModel = null;
        List<SemanticModel> semanticModelsWithSteinerNodes = new ArrayList<SemanticModel>();
        DirectedWeightedMultigraph<Node, DefaultLink> integrationGraph = null;
//        DirectedWeightedMultigraph<Node, DefaultLink> integrationGraphForEmbedding = null;
        ModelLearningGraph modelLearningGraphForEmbedding = null;
        List<ColumnNode> columnNodes = new ArrayList<ColumnNode>();
//        DirectedWeightedMultigraph<Node, DefaultLink> finalIntegrationGraphForEmbedding = null;
        ModelLearningGraph finalModelLearningGraphForEmbedding = null;
        String dataSourceName = null;


        if(semanticModels == null) {
//            semanticModels = ModelReader.importSemanticModelsFromJsonFiles(SemanticMoldesPath + "models-json-20230313", Params.MODEL_MAIN_FILE_EXT);
//            semanticModels = ModelReader.importSemanticModelsFromJsonFiles(SemanticMoldesPath + "models-json-20230712-pgm", Params.MODEL_MAIN_FILE_EXT);
            semanticModels = ModelReader.importSemanticModelsFromJsonFiles(SemanticMoldesPath + "models-json-20230711", Params.MODEL_MAIN_FILE_EXT);
        }
        if(semanticModelsWithCandidateSemanticTypes == null){
//            semanticModelsWithCandidateSemanticTypes = ModelReader.importSemanticModelsFromJsonFiles(SemanticMoldesPath + "labeled-models-json-20230402", Params.MODEL_MAIN_FILE_EXT);
//            semanticModelsWithCandidateSemanticTypes = ModelReader.importSemanticModelsFromJsonFiles(SemanticMoldesPath + "labeled-models-json-20230712-pgm", Params.MODEL_MAIN_FILE_EXT);
            semanticModelsWithCandidateSemanticTypes = ModelReader.importSemanticModelsFromJsonFiles(SemanticMoldesPath + "labeled-models-json-20230711", Params.MODEL_MAIN_FILE_EXT);
        }


        /**2023/04/03 obtain the integration graph for embedding**/
//        //obtain the integration graph for embedding
//        semanticModelsWithSteinerNodes.addAll(semanticModelsWithCandidateSemanticTypes);
//        for(SemanticModel sm: semanticModelsWithSteinerNodes){
//            columnNodes.addAll(sm.getColumnNodes());
//        }
////        integrationGraphForEmbedding = getIntegrationGraphWithCandidateSemanticTypesForEmbedding(semanticModelsWithSteinerNodes,semanticModelsWithSteinerNodes);
//        modelLearningGraphForEmbedding = getIntegrationGraphWithCandidateSemanticTypesForEmbedding(semanticModelsWithSteinerNodes,semanticModelsWithSteinerNodes,true);
//
//        Boolean flag = false;
//        for(ColumnNode column_node:columnNodes){
//            flag = false;
//            for(Node node:modelLearningGraphForEmbedding.getGraphBuilder().getGraph().vertexSet()){
//                if((node instanceof ColumnNode) && (node.equals(column_node))){
//                    flag = true;
//                    break;
//                }
//            }
//            if(!flag) {
//                System.out.println("column node:" + column_node.getColumnName() + " not exits");
//            }
//        }
//
////        for(Node node:modelLearningGraphForEmbedding.getGraphBuilder().getGraph().vertexSet()){
////            if(node instanceof InternalNode){
////                if(node.getId().equals("http://erlangen-crm.org/current/E21_Person2")){
////                    System.out.println("http://erlangen-crm.org/current/E21_Person2 exits");
////                }
////                if(node.getId().equals("http://erlangen-crm.org/current/E53_Place2")){
////                    System.out.println("http://erlangen-crm.org/current/E53_Place2 exits");
////                }
////                if(node.getId().equals("http://erlangen-crm.org/current/E44_Place_Appellation1")){
////                    System.out.println("http://erlangen-crm.org/current/E44_Place_Appellation1 exits");
////                }
////            }
////            if((node instanceof ColumnNode) && (((ColumnNode) node).getColumnName().equals("biography"))){
////                System.out.println("biography exits");
////            }
////        }
//
//
//        Boolean flag1 = false;
//        String small_link_id = null;
//        String link_id = null;
//        List<Integer> notExist = new ArrayList<Integer>();
//        List<String> notIntegrationExist = new ArrayList<String>();
//
//        List<LabeledLink> notLabledLinks = new ArrayList<LabeledLink>();
//        List<CompactLink> notCompactLinks = new ArrayList<CompactLink>();
//
//        for(int j=0;j<29;j++) {
////            if(j<8)
////                continue;
////            else if(j>8)
////                break;
//            predictSourceIndex = j;
////            predictSemanticModel = semanticModels.get(predictSourceIndex);
//            predictSemanticModel = semanticModelsWithCandidateSemanticTypes.get(predictSourceIndex);
//
//            // get train semantic models index array
//            trainSemanticModels = new ArrayList<SemanticModel>();
//            for (int i = 0; i < sourceNum; i++) {
//                if (i != predictSourceIndex) {
//                    trainSemanticModels.add(semanticModels.get(i));
//                }
//            }
//
////        integrationGraph = getIntegrationGraphWithCandidateSemanticTypes(predictSemanticModel,trainSemanticModels);
//            integrationGraph = getIntegrationGraphWithCandidateSemanticTypesForTraining(predictSemanticModel, trainSemanticModels);
//
//            System.out.println(predictSemanticModel.getName() + " integrationGraph links size:" + integrationGraph.edgeSet().size());
//            System.out.println(predictSemanticModel.getName() + " integrationGraph nodes size:" + integrationGraph.vertexSet().size());
//
//            notLabledLinks = new ArrayList<LabeledLink>();
//            notCompactLinks = new ArrayList<CompactLink>();
//
//            for(DefaultLink small_link: integrationGraph.edgeSet()){
//                if(small_link.getTarget() instanceof InternalNode)
//                    small_link_id = small_link.getId();
//                else
//                    small_link_id = small_link.getSource().getId()+small_link.getUri()+((ColumnNode)small_link.getTarget()).getColumnName();
//                flag1 = false;
//                for(DefaultLink link: modelLearningGraphForEmbedding.getGraphBuilder().getGraph().edgeSet()){
//                    if(link.getTarget() instanceof InternalNode)
//                        link_id = link.getId();
//                    else
//                        link_id = link.getSource().getId()+link.getUri()+((ColumnNode)link.getTarget()).getColumnName();
//                    if(link_id.equals(small_link_id)){
//                        flag1 = true;
//                        break;
//                    }
//                }
//                if(!flag1){
//                    System.out.println("small_link type:" + small_link.getType());
//                    if(small_link instanceof LabeledLink)
//                        notLabledLinks.add((LabeledLink) small_link);
//                    else if(small_link instanceof CompactLink)
//                        notCompactLinks.add((CompactLink) small_link);
//
//                    notExist.add(predictSourceIndex);
//                    System.out.println(small_link_id + " not exits");
////                    break;
//                }
//            }
//            if((notLabledLinks.size() > 0) || ((notCompactLinks.size() > 0))) {
//                finalModelLearningGraphForEmbedding = getIntegrationGraphForEmbedding(modelLearningGraphForEmbedding, notLabledLinks, notCompactLinks, PatternWeightSystem.JWSPaperFormula, predictSemanticModel);
//                System.out.println("finalModelLearningGraphForEmbedding links size:" + finalModelLearningGraphForEmbedding.getGraphBuilder().getGraph().edgeSet().size());
//                System.out.println("finalModelLearningGraphForEmbedding nodes size:" + finalModelLearningGraphForEmbedding.getGraphBuilder().getGraph().vertexSet().size());
//                if ((notLabledLinks.size() > 0) && (finalModelLearningGraphForEmbedding.getGraphBuilder().getGraph().edgeSet().containsAll(notLabledLinks))) {
//                    System.out.println("notLabledLinks success");
//                }
//                if ((notCompactLinks.size() > 0) && (finalModelLearningGraphForEmbedding.getGraphBuilder().getGraph().edgeSet().containsAll(notCompactLinks))) {
//                    System.out.println("notCompactLinks success");
//                }
//                modelLearningGraphForEmbedding = finalModelLearningGraphForEmbedding;
//            }
//        }
//
//        for(LabeledLink labeledLink: notLabledLinks){
//            System.out.println("labeledLink " + labeledLink.getId() + " not exits");
//        }
//
//        for(CompactLink compactLink: notCompactLinks){
//            System.out.println("compactLink " + compactLink.getId() + " not exits");
//        }
//
//        List<DefaultLink> notLinks = new ArrayList<DefaultLink>();
//        for(int j=0;j<29;j++) {
////            if(j<8)
////                continue;
////            else if(j>8)
////                break;
//            predictSourceIndex = j;
////            predictSemanticModel = semanticModels.get(predictSourceIndex);
//            predictSemanticModel = semanticModelsWithCandidateSemanticTypes.get(predictSourceIndex);
//
//            // get train semantic models index array
//            trainSemanticModels = new ArrayList<SemanticModel>();
//            for (int i = 0; i < sourceNum; i++) {
//                if (i != predictSourceIndex) {
//                    trainSemanticModels.add(semanticModels.get(i));
//                }
//            }
//
//            integrationGraph = getIntegrationGraphWithCandidateSemanticTypesForTraining(predictSemanticModel, trainSemanticModels);
//            System.out.println("integrationGraph with candidate semantic types links:" + integrationGraph.edgeSet().size());
//            System.out.println("integrationGraph with candidate semantic types nodes:" + integrationGraph.vertexSet().size());
//
//            for(DefaultLink small_link: integrationGraph.edgeSet()){
//                if(small_link.getTarget() instanceof InternalNode)
//                    small_link_id = small_link.getId();
//                else
//                    small_link_id = small_link.getSource().getId()+small_link.getUri()+((ColumnNode)small_link.getTarget()).getColumnName();
//                flag1 = false;
//                for(DefaultLink link: modelLearningGraphForEmbedding.getGraphBuilder().getGraph().edgeSet()){
//                    if(link.getTarget() instanceof InternalNode)
//                        link_id = link.getId();
//                    else
//                        link_id = link.getSource().getId()+link.getUri()+((ColumnNode)link.getTarget()).getColumnName();
//                    if(link_id.equals(small_link_id) || (link.equals(small_link))){
//                        flag1 = true;
//                        break;
//                    }
//                }
//                if(!flag1){
//                    notIntegrationExist.add(predictSemanticModel.getName());
//                    notLinks.add(small_link);
//                    System.out.println("small_link " + small_link.getId() + " not exits");
////                    break;
//                }
//            }
//
//        }
//
//        System.out.println("notIntegrationExist:" + notIntegrationExist);
//
//        System.out.println("notLinks size:" + notLinks.size());
//
//        System.out.println(modelLearningGraphForEmbedding.getGraphBuilder().getGraph().edgeSet().containsAll(notLinks));
//
//        System.out.println("final integrationGraphForEmbedding links:" + modelLearningGraphForEmbedding.getGraphBuilder().getGraph().edgeSet().size());
//        System.out.println("final integrationGraphForEmbedding nodes:" + modelLearningGraphForEmbedding.getGraphBuilder().getGraph().vertexSet().size());
        /**2023/04/03 obtain the integration graph for embedding**/

        /**2023/04/03 generate negative semantic models for all data source**/
        JSONObject jsonObject = null;//embeddings of the integration graph for embedding, it is not empty
        Map<SemanticModel,List<SemanticModel>> subPositiveSemanticModelWithSubNegativeSemanticModels = new HashMap<SemanticModel,List<SemanticModel>>();
        for(int j=0;j<29;j++) {

            if(j<4)
                continue;
            else if(j>4)
                break;

            predictSourceIndex = j;
            predictSemanticModel = semanticModelsWithCandidateSemanticTypes.get(predictSourceIndex);

            // get train semantic models index array
            trainSemanticModels = new ArrayList<SemanticModel>();
            for (int i = 0; i < sourceNum; i++) {
                if (i != predictSourceIndex) {
                    trainSemanticModels.add(semanticModels.get(i));
                }
            }

//            // 2023/04/22 get specific train semantic models
//            trainSemanticModels = new ArrayList<SemanticModel>();
//            Integer[] sourceIndex = new Integer[]{0,3};
//            for(Integer i: sourceIndex){
//                trainSemanticModels.add(semanticModels.get(i));
//            }

            //obtain the integration for generate negative semantic models
            integrationGraph = getIntegrationGraphWithCandidateSemanticTypesForTraining(predictSemanticModel, trainSemanticModels);

            //obtain the source nodes set and target nodes set for any node in the integration graph
            Set<ColumnNode> columnNodesWithTrueUseOntInternalNodes = new HashSet<ColumnNode>();
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
                else if((integrationLink.getTarget() instanceof ColumnNode) && (((ColumnNode) integrationLink.getTarget()).getUseOntInternalNodes())){
                    columnNodesWithTrueUseOntInternalNodes.add((ColumnNode) integrationLink.getTarget());
                }
            }

            System.out.println("columnNodesWithTrueUseOntInternalNodes:" + columnNodesWithTrueUseOntInternalNodes.size());
            System.out.println("internalNodesWithUseOntPaths:" + internalNodesWithUseOntPaths.size());

            System.out.println(predictSemanticModel.getName() + " integrationGraph links size:" + integrationGraph.edgeSet().size());
            System.out.println(predictSemanticModel.getName() + " integrationGraph nodes size:" + integrationGraph.vertexSet().size());

            /**obtain the steiner nodes using ontology internal nodes and ontology paths in predict semantic model**/
            for(ColumnNode columnNode1: columnNodesWithTrueUseOntInternalNodes){
                for(ColumnNode columnNode2: predictSemanticModel.getColumnNodes()){
                    if(columnNode2.getId().equals(columnNode1.getId())){
                        columnNode2.setUseOntInternalNodes(true);
                        break;
                    }
                }
            }

            /**obtain all negative semantic models using original method (test for predicting correct semantic models)**/
//            subPositiveSemanticModelWithSubNegativeSemanticModels = getNegativeSemanticModelsForEmbedding(predictSourceIndex,predictSemanticModel,integrationGraph,jsonObject,internalNodesWithUseOntPaths);
//            System.out.println("subPositiveSemanticModelWithSubNegativeSemanticModels size:" + subPositiveSemanticModelWithSubNegativeSemanticModels.size());


            /**test for obtaining the same positive semantic models for a given positive semantic model**/
//            testForGetSamePositiveSemanticModelsForOneSemanticModel(integrationGraph);

            /**obtain all sub and same positive semantic models
             * (contains the semantic models with only one attribute node and the semantic models with all attribute nodes)**/
            getAllPositiveSemanticModelForOneGoldSemanticModel(predictSourceIndex,predictSemanticModel,integrationGraph,jsonObject);

            /**obtain all negative semantic models for one data source on 14 April 2023**/
            if(predictSourceIndex < 9)
                dataSourceName = "s0" + (predictSourceIndex + 1);
            else
                dataSourceName = "s" + (predictSourceIndex + 1);

//            String positiveSemanticModelSavePathForOneDataSource = "D:\\ASM\\CRM\\positive-models\\sub-same-positive-models-json-all\\" + dataSourceName + "\\";
//            String positiveSemanticModelSavePathForOneDataSource = Params.ROOT_DIR_2023 + "positive-models\\sub-same-positive-models-json-all\\" + dataSourceName + "\\";
//            String positiveSemanticModelSavePathForOneDataSource = Params.ROOT_DIR_2023_LINUX + "positive-models/sub-same-positive-models-json-all/" + dataSourceName + "_pgm" + "/";
//            String positiveSemanticModelSavePathForOneDataSource = Params.EDM_ROOT_DIR_2023 + "positive-models/sub-same-positive-models-json-all/" + dataSourceName;
            String positiveSemanticModelSavePathForOneDataSource = Params.EDM_ROOT_DIR_2023_LINUX + "positive-models/sub-same-positive-models-json-all/" + dataSourceName;

            File allOriginalSubPositiveSemanticModelsFilePath = new File(positiveSemanticModelSavePathForOneDataSource);

            File[] allOriginalSubPositiveSemanticModelsFiles = allOriginalSubPositiveSemanticModelsFilePath.listFiles();

            if(allOriginalSubPositiveSemanticModelsFiles != null) {
                for (File subPositiveSemanticModelsFile : allOriginalSubPositiveSemanticModelsFiles) {
                    System.out.println("subPositiveSemanticModelsFile:" + subPositiveSemanticModelsFile.getName());
                    File[] samePositiveSemanticModelForOneSubPositiveSemanticModelFiles = subPositiveSemanticModelsFile.listFiles();
                    if(samePositiveSemanticModelForOneSubPositiveSemanticModelFiles != null) {
                        for (File samePositiveSemanticModelForOneSubPositiveSemanticModel: samePositiveSemanticModelForOneSubPositiveSemanticModelFiles) {
                            System.out.println(samePositiveSemanticModelForOneSubPositiveSemanticModel.getName());
                            SemanticModel positiveSemanticModel = ModelReader.importSemanticModelFromJsonFile(samePositiveSemanticModelForOneSubPositiveSemanticModel.getAbsolutePath(),Params.MODEL_MAIN_FILE_EXT);
                            if(positiveSemanticModel != null) {
                                String[] fileNames = positiveSemanticModel.getName().replace(".csv", "").split("_", 4);
                                getNegativeSemanticModelsForOneSemanticModel(fileNames, positiveSemanticModel, integrationGraph, jsonObject, internalNodesWithUseOntPaths);
                            }
                        }
                    }
                }
            }
            /**test for generating all negative semantic models for one positive semantic model**/
//            SemanticModel positiveSemanticModel = ModelReader.importSemanticModelFromJsonFile("D:\\ASM\\CRM\\positive-models\\sub-same-positive-models-json-all\\s01\\s01_Sub2_1\\s01_Sub2_1_Same1.model.json",Params.MODEL_MAIN_FILE_EXT);
//            if(positiveSemanticModel != null) {
//                String[] fileNames = positiveSemanticModel.getName().replace(".csv", "").split("_", 4);
//                getNegativeSemanticModelsForOneSemanticModel(fileNames, positiveSemanticModel, integrationGraph, jsonObject);
//            }
            /**obtain all negative semantic models for one data source on 14 April 2023**/

            /**test for obtaining the ancestor nodes for the given two nodes**/
//            testForGetCommonAncestorNodes(integrationGraph);
        }
        /**2023/04/03 generate negative semantic models for all data source**/

        /**test for descartes**/
//        testForDescartes();

        /**test for write json**/
//        testForWriteJson();

        /**test for evaluate**/
//        testForEvaluateModels();

        /**test for save similarity_scores.txt**/
//        testForSaveSimilarityScores();

        /**test for recursive**/
//        testForRecursive();

        /**test for obtaining the samples num for one data source**/
//        testForObtainingSamplesNumForOneDataSource(dataSourceName,Params.EDM_ROOT_DIR_2023+"/negative-models/sub-same-negative-models-json-all");

        /**obtain the integration graph with candidate semantic types for model (GATNE-T + Cross-Attention Network) training**/
//        getIntegrationGraphTriplesForModelTraining();

        System.out.println("generate nagetive samples run completly");
    }
}
