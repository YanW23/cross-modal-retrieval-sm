/*******************************************************************************
 * This new version is to combine Steiner tree algorithm with subgraph matching algorithm in GraMi. 14 August 2018.
 ******************************************************************************/

package edu.isi.karma.research.modeling;


import com.hp.hpl.jena.ontology.*;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import edu.isi.karma.config.ModelingConfiguration;
import edu.isi.karma.config.ModelingConfigurationRegistry;
import edu.isi.karma.modeling.alignment.*;
import edu.isi.karma.modeling.alignment.learner.*;
import edu.isi.karma.modeling.ontology.OntologyManager;
import edu.isi.karma.modeling.research.Params;
import edu.isi.karma.modeling.steiner.topk.Edge;
import edu.isi.karma.rep.alignment.*;
import edu.isi.karma.rep.alignment.SemanticType.Origin;
import edu.isi.karma.util.RandomGUID;
import edu.isi.karma.webserver.ContextParametersRegistry;
import edu.isi.karma.webserver.ServletContextParameterMap;
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

import java.io.*;
import java.text.DecimalFormat;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public class ModelLearner_KnownModels4 {

    private static Logger logger = LoggerFactory.getLogger(ModelLearner_KnownModels4.class);
    private static OntologyManager ontologyManager = null;
    private static List<SemanticModel> semanticModels = null;
    private GraphBuilder graphBuilder = null;
    private NodeIdFactory nodeIdFactory = null;
    private List<Node> steinerNodes = null;
    private PrintWriter resultFile;
    private static OntModel ontModel = ModelFactory.createOntologyModel(OntModelSpec.OWL_MEM);


    public ModelLearner_KnownModels4(OntologyManager ontologyManager,
                                     List<Node> steinerNodes) throws FileNotFoundException {
        if (ontologyManager == null ||
                steinerNodes == null ||
                steinerNodes.isEmpty()) {
            logger.error("cannot instanciate model learner!");
            return;
        }
        GraphBuilder gb = ModelLearningGraph.getInstance(ontologyManager, ModelLearningGraphType.Compact).getGraphBuilder();
        this.ontologyManager = ontologyManager;
        this.steinerNodes = steinerNodes;
        this.graphBuilder = cloneGraphBuilder(gb); // create a copy of the graph builder
        this.nodeIdFactory = this.graphBuilder.getNodeIdFactory();

    }

    public ModelLearner_KnownModels4(GraphBuilder graphBuilder,
                                     List<Node> steinerNodes) throws FileNotFoundException {
        if (graphBuilder == null ||
                steinerNodes == null ||
                steinerNodes.isEmpty()) {
            logger.error("cannot instanciate model learner!");
            return;
        }
        this.ontologyManager = graphBuilder.getOntologyManager();
        this.steinerNodes = steinerNodes;
        this.graphBuilder = cloneGraphBuilder(graphBuilder); // create a copy of the graph builder
        this.nodeIdFactory = this.graphBuilder.getNodeIdFactory();
    }

    /**set Steiner nodes in this model learner. 8 June 2018.**/
    public void setSteinerNodes (List<Node> steinerNodes) {
        this.steinerNodes.clear();

        Iterator<Node> iterator = steinerNodes.iterator();
        while (iterator.hasNext()) {

            Node node = iterator.next();

            this.steinerNodes.add(node);


        }

        //steinerNodes = steinerNodes;

    }

    /**get Steiner nodes in this model learner. 8 June 2018.**/
    public List<Node> getSteinerNodes () {

        return this.steinerNodes;
    }

    private GraphBuilder cloneGraphBuilder(GraphBuilder graphBuilder) {

        GraphBuilder clonedGraphBuilder = null;
        if (graphBuilder == null || graphBuilder.getGraph() == null) {
            clonedGraphBuilder = new GraphBuilderTopK(this.ontologyManager, false);
        } else {
            clonedGraphBuilder = new GraphBuilderTopK(this.ontologyManager, graphBuilder.getGraph());
        }
        return clonedGraphBuilder;
    }

    public List<SortableSemanticModel> hypothesize1(boolean useCorrectTypes,int numberOfCandidates) throws Exception {
        ModelingConfiguration modelingConfiguration = ModelingConfigurationRegistry.getInstance().getModelingConfiguration(ontologyManager.getContextId());
        List<SortableSemanticModel> sortableSemanticModels = new ArrayList<SortableSemanticModel>();
        Set<Node> addedNodes = new HashSet<Node>(); //They should be deleted from the graph after computing the semantic models
        List<ColumnNode> columnNodes = new LinkedList<ColumnNode>();

        for (Node n : steinerNodes)
            if (n instanceof ColumnNode)
                columnNodes.add((ColumnNode)n);

        logger.info("finding candidate steiner sets ... ");
        System.out.println("finding candidate steiner sets ...");
        System.out.println("??????addedNodes?????????"+addedNodes.size());
        System.out.println("??????getCandidateSteinerSets??????---------------");
        CandidateSteinerSets candidateSteinerSets = getCandidateSteinerSets(steinerNodes, useCorrectTypes, numberOfCandidates, addedNodes);
        System.out.println("getCandidateSteinerSet?????????addedNodes?????????"+addedNodes.size());

        if (candidateSteinerSets == null ||
                candidateSteinerSets.getSteinerSets() == null ||
                candidateSteinerSets.getSteinerSets().isEmpty()) {
            logger.error("there is no candidate set of steiner nodes.");
            System.out.println("there is no candidate set of steiner nodes.");

            DirectedWeightedMultigraph<Node, LabeledLink> tree =
                    new DirectedWeightedMultigraph<Node, LabeledLink>(LabeledLink.class);

            for (Node n : steinerNodes)
                tree.addVertex(n);

            SemanticModel sm = new SemanticModel(new RandomGUID().toString(), tree);
            SortableSemanticModel sortableSemanticModel = new SortableSemanticModel(sm, null, false);
            sortableSemanticModels.add(sortableSemanticModel);
            return sortableSemanticModels;
        }
        logger.info("graph nodes: " + this.graphBuilder.getGraph().vertexSet().size());
        logger.info("graph links: " + this.graphBuilder.getGraph().edgeSet().size());

        System.out.println("graph nodes:"+this.graphBuilder.getGraph().vertexSet().size());
        System.out.println("graph links:"+this.graphBuilder.getGraph().edgeSet().size());
        return null;
    }

    private CandidateSteinerSets getCandidateSteinerSets(List<Node> steinerNodes, boolean useCorrectTypes, int numberOfCandidates, Set<Node> addedNodes) {

        if (steinerNodes == null || steinerNodes.isEmpty())
            return null;


        int maxNumberOfSteinerNodes = steinerNodes.size() * 2;
        CandidateSteinerSets candidateSteinerSets = new CandidateSteinerSets(maxNumberOfSteinerNodes,ontologyManager.getContextId());
//        System.out.println("??????candidateSteinerSets?????????"+candidateSteinerSets.numberOfCandidateSets());


        if (addedNodes == null)
            addedNodes = new HashSet<Node>();


        Set<SemanticTypeMapping> tempSemanticTypeMappings;
        HashMap<ColumnNode, List<SemanticType>> columnSemanticTypes = new HashMap<ColumnNode, List<SemanticType>>();
        HashMap<String, Integer> semanticTypesCount = new HashMap<String, Integer>();
        List<SemanticType> candidateSemanticTypes = null;
        String domainUri = "", propertyUri = "";

        for (Node n : steinerNodes) {

            ColumnNode cn = null;
            if (n instanceof ColumnNode)
                cn = (ColumnNode) n;
            else
                continue;

            System.out.println(cn.getColumnName());

            if (!useCorrectTypes) {
                candidateSemanticTypes = cn.getTopKLearnedSemanticTypes(numberOfCandidates);
            } else if (cn.getSemanticTypeStatus() == ColumnSemanticTypeStatus.UserAssigned) {
                candidateSemanticTypes = cn.getUserSemanticTypes();
            }


            if (candidateSemanticTypes == null) {
                logger.error("No candidate semantic type found for the column " + cn.getColumnName());
                return null;
            }

            columnSemanticTypes.put(cn, candidateSemanticTypes);

            for (SemanticType semanticType: candidateSemanticTypes) {

                if (semanticType == null ||
                        semanticType.getDomain() == null ||
                        semanticType.getType() == null) continue;

                domainUri = semanticType.getDomain().getUri();
                propertyUri = semanticType.getType().getUri();

//                System.out.println("??????domainUri + propertyUri?????????"+domainUri + propertyUri);

                Integer count = semanticTypesCount.get(domainUri + propertyUri);//?????????????????????????????????????????????????????????????????????
                if (count == null) semanticTypesCount.put(domainUri + propertyUri, 1);
                else semanticTypesCount.put(domainUri + propertyUri, count.intValue() + 1);
                System.out.println("??????semanticTypesCount?????????"+semanticTypesCount); //semanticTypesCount????????????????????????????????????????????????????????????
            }
        }

        long numOfMappings = 1;

        for (Node n : steinerNodes) {

            if (n instanceof InternalNode)
                continue;

            ColumnNode cn = null;
            if (n instanceof ColumnNode)
                cn = (ColumnNode)n;
            else
                continue;

            candidateSemanticTypes = columnSemanticTypes.get(n);//????????????node???4???Semantictype
            if (candidateSemanticTypes == null) continue;

            logger.info("===== Column: " + cn.getColumnName());

            Set<SemanticTypeMapping> semanticTypeMappings = null;

//			if (cn.hasUserType()) {
//				HashMap<SemanticType, LabeledLink> domainLinks =
//						GraphUtil.getDomainLinks(this.graphBuilder.getGraph(), cn, cn.getUserSemanticTypes());
//				if (domainLinks != null && !domainLinks.isEmpty()) {
//					for (SemanticType st : cn.getUserSemanticTypes()) {
//						semanticTypeMappings = new HashSet<SemanticTypeMapping>();
//						LabeledLink domainLink = domainLinks.get(st);
//						if (domainLink == null || domainLink.getSource() == null || !(domainLink.getSource() instanceof InternalNode))
//							continue;
//						SemanticTypeMapping mp =
//								new SemanticTypeMapping(cn, st, (InternalNode)domainLink.getSource(), domainLink, cn);
//						semanticTypeMappings.add(mp);
//						candidateSteinerSets.updateSteinerSets(semanticTypeMappings);
//					}
//				}
//			} else
            {
                semanticTypeMappings = new HashSet<SemanticTypeMapping>();
                for (SemanticType semanticType: candidateSemanticTypes) {//????????????node?????????semantictype

                    logger.info("\t" + semanticType.getConfidenceScore() + " :" + semanticType.getModelLabelString());

                    if (semanticType == null ||
                            semanticType.getDomain() == null ||
                            semanticType.getType() == null) continue;

                    domainUri = semanticType.getDomain().getUri();

                    propertyUri = semanticType.getType().getUri();

                    Integer countOfSemanticType = semanticTypesCount.get(domainUri + propertyUri);//?????????semantictype???????????????
                    logger.debug("count of semantic type: " +  countOfSemanticType);
                    System.out.println("count of semantic type: " +  countOfSemanticType);


                    System.out.println("??????findSemanticTypeInGraph???????????????????????????????????????????????????mapping------------");
                    tempSemanticTypeMappings = findSemanticTypeInGraph(cn, semanticType, semanticTypesCount, addedNodes);
                    System.out.println("??????findSemanticTypeInGraph??????------------");

                    logger.debug("number of matches for semantic type: " +
                            + (tempSemanticTypeMappings == null ? 0 : tempSemanticTypeMappings.size()));
                    System.out.println("number of matches for semantic type: " +
                            + (tempSemanticTypeMappings == null ? 0 : tempSemanticTypeMappings.size()));

                    if (tempSemanticTypeMappings != null)
                        semanticTypeMappings.addAll(tempSemanticTypeMappings);

                    int countOfMatches = tempSemanticTypeMappings == null ? 0 : tempSemanticTypeMappings.size();
//					if (countOfMatches < countOfSemanticType)
                    if (countOfMatches == 0) // No struct in graph is matched with the semantic type, we add a new struct to the graph
                    {
                        System.out.println("??????no struct?????????addedNodes???"+addedNodes.size());
                        SemanticTypeMapping mp = addSemanticTypeStruct(cn, semanticType, addedNodes);
                        if (mp != null)
                            semanticTypeMappings.add(mp);
                    }
                }

                //			System.out.println("number of matches for column " + n.getColumnName() +
                //					": " + (semanticTypeMappings == null ? 0 : semanticTypeMappings.size()));
                logger.debug("number of matches for column " + cn.getColumnName() +
                        ": " + (semanticTypeMappings == null ? 0 : semanticTypeMappings.size()));
                numOfMappings *= (semanticTypeMappings == null || semanticTypeMappings.isEmpty() ? 1 : semanticTypeMappings.size());

                logger.debug("number of candidate steiner sets before update: " + candidateSteinerSets.getSteinerSets().size());
                candidateSteinerSets.updateSteinerSets(semanticTypeMappings);
                logger.debug("number of candidate steiner sets after update: " + candidateSteinerSets.getSteinerSets().size());
            }
        }

        for (Node n : steinerNodes) {
            if (n instanceof InternalNode) {
                candidateSteinerSets.updateSteinerSets((InternalNode)n);
            }
        }

        //		System.out.println("number of possible mappings: " + numOfMappings);
        logger.info("number of possible mappings: " + numOfMappings);

        return candidateSteinerSets;
    }

    private Set<SemanticTypeMapping> findSemanticTypeInGraph(ColumnNode sourceColumn, SemanticType semanticType,
                                                             HashMap<String, Integer> semanticTypesCount, Set<Node> addedNodes) {

        logger.debug("finding matches for semantic type in the graph ... ");
        System.out.println("finding matches for semantic type in the graph ...");
        ModelingConfiguration modelingConfiguration = ModelingConfigurationRegistry.getInstance().getModelingConfiguration(ontologyManager.getContextId());
        System.out.println("??????findSemanticTypeInGraph???addedNodes?????? ..."+addedNodes.size());
        if (addedNodes == null)
            addedNodes = new HashSet<Node>();

        Set<SemanticTypeMapping> mappings = new HashSet<SemanticTypeMapping>();

        if (semanticType == null) {
            logger.error("semantic type is null.");
            return mappings;

        }
        if (semanticType.getDomain() == null) {
            logger.error("semantic type does not have any domain");
            return mappings;
        }

        if (semanticType.getType() == null) {
            logger.error("semantic type does not have any link");
            return mappings;
        }

        String domainUri = semanticType.getDomain().getUri();
        String propertyUri = semanticType.getType().getUri();
        Double confidence = semanticType.getConfidenceScore();
        Origin origin = semanticType.getOrigin();

        Integer countOfSemanticType = semanticTypesCount.get(domainUri + propertyUri);//????????????node?????????semantictype???????????????
        if (countOfSemanticType == null) {
            logger.error("count of semantic type should not be null or zero");
            return mappings;
        }

        if (domainUri == null || domainUri.isEmpty()) {
            logger.error("semantic type does not have any domain");
            return mappings;
        }

        if (propertyUri == null || propertyUri.isEmpty()) {
            logger.error("semantic type does not have any link");
            return mappings;
        }

        logger.debug("semantic type: " + domainUri + "|" + propertyUri + "|" + confidence + "|" + origin);
        System.out.println("semantic type: " + domainUri + "|" + propertyUri + "|" + confidence + "|" + origin);

        // add dataproperty to existing classes if sl is a data node mapping
        //		Set<Node> foundInternalNodes = new HashSet<Node>();
        Set<SemanticTypeMapping> semanticTypeMatches = this.graphBuilder.getSemanticTypeMatches().get(domainUri + propertyUri);//?????????????????????????????????semantictype?????????link

        if (semanticTypeMatches != null) {//?????????semantictype?????????????????????,???????????????link??????,????????????????????????,?????????mappings?????????

            for (SemanticTypeMapping stm : semanticTypeMatches) {

                SemanticTypeMapping mp =
                        new SemanticTypeMapping(sourceColumn, semanticType, stm.getSource(), stm.getLink(), stm.getTarget());
                mappings.add(mp);//??????columnnode?????????semantictype?????????????????????????????????
                //				foundInternalNodes.add(stm.getSource());
            }
        }



        logger.debug("adding data property to the found internal nodes ...");
        System.out.println("adding data property to the found internal nodes ...");

        Integer count;
        boolean allowMultipleSamePropertiesPerNode = modelingConfiguration.isMultipleSamePropertyPerNode();//???false
//        System.out.println("??????allowMultipleSamePropertiesPerNode???"+allowMultipleSamePropertiesPerNode);
        Set<Node> nodesWithSameUriOfDomain = this.graphBuilder.getUriToNodesMap().get(domainUri);//??????????????????semantictype????????????????????????source node?????????uri????????????internal node?????????????????????????????????

        if (nodesWithSameUriOfDomain != null) {//?????????????????????,???????????????internal nodes,??????????????????????????????semantictype???link?????????link
//            System.out.println("??????nodesWithSameUriOfDomain???"+nodesWithSameUriOfDomain.size());
            for (Node source : nodesWithSameUriOfDomain) {//????????????internal nodes
                count = this.graphBuilder.getNodeDataPropertyCount().get(source.getId() + propertyUri);//????????????????????????internal node?????????semantictype???link?????????link???

                System.out.println("??????count:"+count);

                if (count != null) {//??????count!=null,??????????????????semantic type,???????????????????????????????????????????????????

                    if (allowMultipleSamePropertiesPerNode) {
                        if (count >= countOfSemanticType.intValue())
                            continue;
                    } else {
                        if (count >= 1)
                            continue;
                    }
                }

                //?????????node?????????semantictype,????????????????????????
                String nodeId = new RandomGUID().toString();//???????????????nodeId
                ColumnNode target = new ColumnNode(nodeId, nodeId, sourceColumn.getColumnName(), null,"English");//??????????????????????????????columnnode

                if (!this.graphBuilder.addNode(target)) continue;//????????????????????????semantictype???node????????????columnnode
                addedNodes.add(target);
                System.out.println("??????addedNodes??????1???"+addedNodes.size());

                String linkId = LinkIdFactory.getLinkId(propertyUri, source.getId(), target.getId());//???????????????????????????internal node?????????semantic types??????link
                LabeledLink link = new DataPropertyLink(linkId, new Label(propertyUri));//??????DataPropertyLink
                System.out.println("??????link?????????????????????"+this.graphBuilder.addLink(source, target, link));
                if (!this.graphBuilder.addLink(source, target, link)) {
                    System.out.println("??????????????????link???????????????"+link.getUri());
                    continue;
                }

                SemanticTypeMapping mp = new SemanticTypeMapping(sourceColumn, semanticType, (InternalNode)source, link, target);
                mappings.add(mp);
            }
        }

        return mappings;
    }

    private SemanticTypeMapping addSemanticTypeStruct(ColumnNode sourceColumn, SemanticType semanticType, Set<Node> addedNodes) {

        logger.debug("adding semantic type to the graph ... ");
        System.out.println("adding semantic type to the graph ... ");


        if (addedNodes == null)
            addedNodes = new HashSet<Node>();

        if (semanticType == null) {
            logger.error("semantic type is null.");
            return null;

        }
        if (semanticType.getDomain() == null) {
            logger.error("semantic type does not have any domain");
            return null;
        }

        if (semanticType.getType() == null) {
            logger.error("semantic type does not have any link");
            return null;
        }

        String domainUri = semanticType.getDomain().getUri();
        String propertyUri = semanticType.getType().getUri();
        Double confidence = semanticType.getConfidenceScore();
        Origin origin = semanticType.getOrigin();

        if (domainUri == null || domainUri.isEmpty()) {
            logger.error("semantic type does not have any domain");
            return null;
        }

        if (propertyUri == null || propertyUri.isEmpty()) {
            logger.error("semantic type does not have any link");
            return null;
        }

        logger.debug("semantic type: " + domainUri + "|" + propertyUri + "|" + confidence + "|" + origin);

        InternalNode source = null;
        String nodeId;

        nodeId = nodeIdFactory.getNodeId(domainUri);
        source = new InternalNode(nodeId, new Label(domainUri));
        if (!this.graphBuilder.addNodeAndUpdate(source, addedNodes)) return null;//??????

        nodeId = new RandomGUID().toString();
        ColumnNode target = new ColumnNode(nodeId, nodeId, sourceColumn.getColumnName(), null,"English");
        if (!this.graphBuilder.addNode(target)) return null;
        addedNodes.add(target);

        System.out.println("???????????????");
        String linkId = LinkIdFactory.getLinkId(propertyUri, source.getId(), target.getId());
        LabeledLink link;
        if (propertyUri.equalsIgnoreCase(ClassInstanceLink.getFixedLabel().getUri())) {
            link = new ClassInstanceLink(linkId);
        }
        else {
            Label label = this.ontologyManager.getUriLabel(propertyUri);//??????link???label
            link = new DataPropertyLink(linkId, label);
        }

        this.graphBuilder.addLink(source, target, link);
        if (!this.graphBuilder.addLink(source, target, link)) {
            return null;
        }

        SemanticTypeMapping mappingStruct = new SemanticTypeMapping(sourceColumn, semanticType, source, link, target);

        return mappingStruct;
    }

    /**Compute the Steiner tree for a single table. 17 May 2018.**/
    public List<SortableSemanticModel> hypothesize(boolean useCorrectTypes, int numberOfCandidates) throws Exception {

        ModelingConfiguration modelingConfiguration = ModelingConfigurationRegistry.getInstance().getModelingConfiguration(ontologyManager.getContextId());
        List<SortableSemanticModel> sortableSemanticModels = new ArrayList<SortableSemanticModel>();

        /**It is used to save the mapping relations between the column nodes in new source and merged graph. 8 June 2018**/
        //???????????????merged graph??????????????????
        Map<ColumnNode, ColumnNode> mappingToSourceColumns = new HashMap<ColumnNode, ColumnNode>();

        /**It is used to save the steiner nodes in the merged graph. 8 June 2018.**/
        //??????merged graph??????steiner nodes
        List<ColumnNode> columnNodes = new LinkedList<ColumnNode>();

        /**The column nodes in the new source is saved in 'steinerNodes'. 8 June 2018.**/
        for (Node n : steinerNodes)
            if (n instanceof ColumnNode) {
                ColumnNode c = (ColumnNode)n;
                columnNodes.add(c);/**Here, we get the steiner node in the merged graph. 8 June 2018.**/
                mappingToSourceColumns.put(c, c);//what's mean for this code???
            }

        System.out.println("??????mappingToSourceColumns?????????"+mappingToSourceColumns.size());
        for(ColumnNode node: mappingToSourceColumns.keySet()){
            System.out.println(node.getColumnName() + "----" + mappingToSourceColumns.get(node).getColumnName());
        }

        for (Node n : steinerNodes) {
            if (n instanceof ColumnNode) {
                ColumnNode steinerNode = (ColumnNode)n;
//                getCandidateSteinerSets(steinerNode, useCorrectTypes, numberOfCandidates);
                List<SemanticType> candidateSemanticTypes = getCandidateSteinerSets(steinerNode, useCorrectTypes, numberOfCandidates);
                System.out.println("hypothesize???candidateSemanticTypes????????????" + candidateSemanticTypes.size());
                System.out.println(steinerNode.getColumnName());
                for(SemanticType semantictype: candidateSemanticTypes){
                    System.out.println("??????semantictype:" + semantictype.getDomain() + "|" + semantictype.getType());
                }
                addSteinerNodeToTheGraph(steinerNode, candidateSemanticTypes);
            }
        }

        /**??????3.30**/
        Set<Node> sn = new HashSet<Node>(steinerNodes);
        List<DirectedWeightedMultigraph<Node, LabeledLink>> topKSteinerTrees;
        if (this.graphBuilder instanceof GraphBuilderTopK) {

            /**Get the top k Steiner Trees. 22 May 2018.**/
            int k = modelingConfiguration.getTopKSteinerTree();
            System.out.println("??????getTopKSteinerTree??????k??????"+k);///////////////

            topKSteinerTrees =  ((GraphBuilderTopK)this.graphBuilder).getTopKSteinerTrees(sn, k, null, null, false);
        }
        else
        {
            topKSteinerTrees = new LinkedList<DirectedWeightedMultigraph<Node, LabeledLink>>();
            SteinerTree steinerTree = new SteinerTree(
                    new AsUndirectedGraph<Node, DefaultLink>(this.graphBuilder.getGraph()), Lists.newLinkedList(sn));
            WeightedMultigraph<Node, DefaultLink> t = steinerTree.getDefaultSteinerTree();
            TreePostProcess treePostProcess = new TreePostProcess(this.graphBuilder, t);
            if (treePostProcess.getTree() != null)
                topKSteinerTrees.add(treePostProcess.getTree());
        }

//		System.out.println(GraphUtil.labeledGraphToString(treePostProcess.getTree()));

//		logger.info("END ...");

        /**????????????,????????????tree?????????semantic model,???????????????sortedsemanticmodel,?????????sortedsemanticmodel?????????**/
        for (DirectedWeightedMultigraph<Node, LabeledLink> tree: topKSteinerTrees) {
            if (tree != null) {
//					System.out.println();
                SemanticModel sm = new SemanticModel(new RandomGUID().toString(),
                        tree,
                        columnNodes,
                        mappingToSourceColumns
                );
                SortableSemanticModel sortableSemanticModel =
                        new SortableSemanticModel(sm, false);
                sortableSemanticModels.add(sortableSemanticModel);

//					System.out.println(GraphUtil.labeledGraphToString(sm.getGraph()));
//					System.out.println(sortableSemanticModel.getLinkCoherence().printCoherenceList());
            }
        }

        Collections.sort(sortableSemanticModels);
        int count = Math.min(sortableSemanticModels.size(), modelingConfiguration.getNumCandidateMappings());
        logger.info("results are ready ...");
//		sortableSemanticModels.get(0).print();
        return sortableSemanticModels.subList(0, count);
        /**??????3.30**/
//        return null;
    }

    //??????useCorrectTypes??????????????????nodes???links
    public List<SortableSemanticModel> hypothesize2(boolean useCorrectTypes, int numberOfCandidates) throws Exception {

        ModelingConfiguration modelingConfiguration = ModelingConfigurationRegistry.getInstance().getModelingConfiguration(ontologyManager.getContextId());
        List<SortableSemanticModel> sortableSemanticModels = new ArrayList<SortableSemanticModel>();

        /**It is used to save the mapping relations between the column nodes in new source and merged graph. 8 June 2018**/
        //???????????????merged graph??????????????????
        Map<ColumnNode, ColumnNode> mappingToSourceColumns = new HashMap<ColumnNode, ColumnNode>();

        /**It is used to save the steiner nodes in the merged graph. 8 June 2018.**/
        //??????merged graph??????steiner nodes
        List<ColumnNode> columnNodes = new LinkedList<ColumnNode>();

        /**The column nodes in the new source is saved in 'steinerNodes'. 8 June 2018.**/
        for (Node n : steinerNodes)
            if (n instanceof ColumnNode) {
                ColumnNode c = (ColumnNode)n;
                columnNodes.add(c);/**Here, we get the steiner node in the merged graph. 8 June 2018.**/
                mappingToSourceColumns.put(c, c);//what's mean for this code???
            }

        System.out.println("??????mappingToSourceColumns?????????"+mappingToSourceColumns.size());
        for(ColumnNode node: mappingToSourceColumns.keySet()){
            System.out.println(node.getColumnName() + "----" + mappingToSourceColumns.get(node).getColumnName());
        }

        for (Node n : steinerNodes) {
            if (n instanceof ColumnNode) {
                ColumnNode steinerNode = (ColumnNode)n;
                List<SemanticType> candidateSemanticTypes = getCandidateSteinerSets(steinerNode, useCorrectTypes, numberOfCandidates);
                addSteinerNodeToTheGraph(steinerNode, candidateSemanticTypes);
            }
        }



        return null;
    }

    public List<SortableSemanticModel> hypothesize_correct_candidates_smtypes(int numberOfCandidates) throws Exception {

        ModelingConfiguration modelingConfiguration = ModelingConfigurationRegistry.getInstance().getModelingConfiguration(ontologyManager.getContextId());
        List<SortableSemanticModel> sortableSemanticModels = new ArrayList<SortableSemanticModel>();

        /**It is used to save the mapping relations between the column nodes in new source and merged graph. 8 June 2018**/
        //???????????????merged graph??????????????????
        Map<ColumnNode, ColumnNode> mappingToSourceColumns = new HashMap<ColumnNode, ColumnNode>();

        /**It is used to save the steiner nodes in the merged graph. 8 June 2018.**/
        //??????merged graph??????steiner nodes
        List<ColumnNode> columnNodes = new LinkedList<ColumnNode>();

        /**The column nodes in the new source is saved in 'steinerNodes'. 8 June 2018.**/
        for (Node n : steinerNodes)
            if (n instanceof ColumnNode) {
                ColumnNode c = (ColumnNode)n;
                columnNodes.add(c);/**Here, we get the steiner node in the merged graph. 8 June 2018.**/
                mappingToSourceColumns.put(c, c);//what's mean for this code???
            }

        System.out.println("??????mappingToSourceColumns?????????"+mappingToSourceColumns.size());
        for(ColumnNode node: mappingToSourceColumns.keySet()){
            System.out.println(node.getColumnName() + "----" + mappingToSourceColumns.get(node).getColumnName());
        }

        for (Node n : steinerNodes) {
            if (n instanceof ColumnNode) {
                ColumnNode steinerNode = (ColumnNode)n;
                List<SemanticType> candidateSemanticTypes = getCandidateSteinerSets_Correct_Candidates(steinerNode,numberOfCandidates);
                addSteinerNodeToTheGraph(steinerNode, candidateSemanticTypes);
            }
        }

        return null;
    }

    //??????useCorrectTypes?????????false ??????columnnode???candidate semantic types
    private List<SemanticType> getCandidateSteinerSets(ColumnNode steinerNode, boolean useCorrectTypes, int numberOfCandidates) {

        if (steinerNode == null)
            return null;

        List<SemanticType> candidateSemanticTypes = null;

        if (!useCorrectTypes) {
            System.out.println("!useCorrectTypes");
            candidateSemanticTypes = steinerNode.getTopKLearnedSemanticTypes(numberOfCandidates);//??????????????????????????????numberOfCandidates?????????????????????
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

    //??????columnnode???correct_candidates semantic types
    private static List<SemanticType> getCandidateSteinerSets_Correct_Candidates(ColumnNode steinerNode, int numberOfCandidates) {

        if (steinerNode == null)
            return null;

        List<SemanticType> correctSemnaticTypes = null;
        List<SemanticType> candidateSemanticTypes = null;
        Set<SemanticType> SemanticTypesTmp = new HashSet<SemanticType>();
        List<SemanticType> FinalSemanticTypes = new ArrayList<SemanticType>();
        //??????????????????semantic type
        correctSemnaticTypes = steinerNode.getUserSemanticTypes();
        System.out.println("correctSemnaticTypes.size:" + correctSemnaticTypes.size());
        if(correctSemnaticTypes.size()>0){
            SemanticTypesTmp.addAll(correctSemnaticTypes);
        }
        //??????????????????semantic type
        candidateSemanticTypes = steinerNode.getTopKLearnedSemanticTypes(numberOfCandidates);//??????????????????????????????numberOfCandidates?????????????????????
        if(candidateSemanticTypes.size()>0){
            //??????????????????correct semantic types ???????????????
            if(correctSemnaticTypes.size()>0) {
                //????????????candidates types
                for (SemanticType candidatetype : candidateSemanticTypes) {
                    //???????????????correct types?????? ??????????????????
                    if ((candidatetype.getType().equals(correctSemnaticTypes.get(0).getType())) && (candidatetype.getDomain().equals(correctSemnaticTypes.get(0).getDomain()))) {
                        continue;
                    }
                    SemanticTypesTmp.add(candidatetype);
                }
            }
            //?????? ????????????candidates semantic types
            else{
                SemanticTypesTmp.addAll(candidateSemanticTypes);
            }
        }
        FinalSemanticTypes.addAll(SemanticTypesTmp);

        if (FinalSemanticTypes == null) {
            logger.error("No candidate semantic type found for the column " + steinerNode.getColumnName());
            System.out.println("No candidate semantic type found for the column " + steinerNode.getColumnName());
            return null;
        }
        System.out.println("FinalSemanticTypes.size:" + FinalSemanticTypes.size());
        for(SemanticType smtype: FinalSemanticTypes){
            System.out.println("smtype:" + smtype);
        }

        return FinalSemanticTypes;
    }

    /**?????????????????????????????????**/
    private void addSteinerNodeToTheGraph(ColumnNode steinerNode, List<SemanticType> semanticTypes) {

        if (!this.graphBuilder.addNode(steinerNode)) {
            return ;
        }

        System.out.println("??????addNode(steinerNode)");

        if (semanticTypes == null) {
            logger.error("semantic type is null.");
            System.out.println("semantic type is null.");
            return;
        }

        for (SemanticType semanticType : semanticTypes) {

            if (semanticType == null) {
                logger.error("semantic type is null.");
                System.out.println("semantic type is null.");
                continue;

            }
            if (semanticType.getDomain() == null) {
                logger.error("semantic type does not have any domain");
                System.out.println("semantic type does not have any domain");
                continue;
            }

            if (semanticType.getType() == null) {
                logger.error("semantic type does not have any link");
                System.out.println("semantic type does not have any link");
                continue;
            }

            String domainUri = semanticType.getDomain().getUri();
            String propertyUri = semanticType.getType().getUri();
            Double confidence = semanticType.getConfidenceScore();
            Origin origin = semanticType.getOrigin();

            logger.debug("semantic type: " + domainUri + "|" + propertyUri + "|" + confidence + "|" + origin);
            System.out.println("semantic type: " + domainUri + "|" + propertyUri + "|" + confidence + "|" + origin);

            Set<Node> nodesWithSameUriOfDomain = this.graphBuilder.getUriToNodesMap().get(domainUri);
            if (nodesWithSameUriOfDomain == null || nodesWithSameUriOfDomain.isEmpty()) {
                System.out.println("?????????nodesWithSameUriOfDomain == null??????????????????internalnode");
                String nodeId = nodeIdFactory.getNodeId(domainUri);
                Node source = new InternalNode(nodeId, new Label(domainUri));
                if (!this.graphBuilder.addNodeAndUpdate(source, null)) continue;
                String linkId = LinkIdFactory.getLinkId(propertyUri, source.getId(), steinerNode.getId());
                LabeledLink link = new DataPropertyLink(linkId, new Label(propertyUri));
                if (!this.graphBuilder.addLink(source, steinerNode, link)) continue;
            } else {
                for (Node source : nodesWithSameUriOfDomain) {
                    System.out.println(source.getId()+"?????????nodesWithSameUriOfDomain != null??????");
                    String linkId = LinkIdFactory.getLinkId(propertyUri, source.getId(), steinerNode.getId());
                    LabeledLink link = new DataPropertyLink(linkId, new Label(propertyUri));
                    if (!this.graphBuilder.addLink(source, steinerNode, link)) continue;;
                }
            }

        }
    }

    private static double roundDecimals(double d, int k) {
        String format = "";
        for (int i = 0; i < k; i++) format += "#";
        DecimalFormat DForm = new DecimalFormat("#." + format);
        return Double.valueOf(DForm.format(d));
    }

    @SuppressWarnings("unused")
    private static void getStatistics1(List<SemanticModel> semanticModels) {
        for (int i = 0; i < semanticModels.size(); i++) {
            SemanticModel source = semanticModels.get(i);
            int attributeCount = source.getColumnNodes().size();
            int nodeCount = source.getGraph().vertexSet().size();
            int linkCount = source.getGraph().edgeSet().size();
            int datanodeCount = 0;
            int classNodeCount = 0;
            for (Node n : source.getGraph().vertexSet()) {
                if (n instanceof InternalNode) classNodeCount++;
                if (n instanceof ColumnNode) datanodeCount++;
            }
            System.out.println(attributeCount + "\t" + nodeCount + "\t" + linkCount + "\t" + classNodeCount + "\t" + datanodeCount);

            List<ColumnNode> columnNodes = source.getColumnNodes();
            getStatistics2(columnNodes);

        }
    }

    private static void getStatistics2(List<ColumnNode> columnNodes) {

        if (columnNodes == null)
            return;

        int numberOfAttributesWhoseTypeIsFirstCRFType = 0;
        int numberOfAttributesWhoseTypeIsInCRFTypes = 0;
        for (ColumnNode cn : columnNodes) {
            List<SemanticType> userSemanticTypes = cn.getUserSemanticTypes();
            List<SemanticType> top4Suggestions = cn.getTopKLearnedSemanticTypes(4);

            for (int i = 0; i < top4Suggestions.size(); i++) {
                SemanticType st = top4Suggestions.get(i);
                if (userSemanticTypes != null) {
                    for (SemanticType t : userSemanticTypes) {
                        if (st.getModelLabelString().equalsIgnoreCase(t.getModelLabelString())) {
                            if (i == 0) numberOfAttributesWhoseTypeIsFirstCRFType ++;
                            numberOfAttributesWhoseTypeIsInCRFTypes ++;
                            i = top4Suggestions.size();
                            break;
                        }
                    }
                }
            }

        }

        System.out.println(numberOfAttributesWhoseTypeIsInCRFTypes + "\t" + numberOfAttributesWhoseTypeIsFirstCRFType);
    }


    /**Get candidate semantic models for new data source.
     * @return candidate semantic models (Steiner trees) for the new data source.
     * */
    public static List<SortableSemanticModel> getCandidateSemanticModels(int newSourceIndex, Integer[] trainDataIndex) throws Exception {

        ServletContextParameterMap contextParameters = ContextParametersRegistry.getInstance().getDefault();

        /**??????????????????????????????**/

        String graphPath = Params.GRAPHS_DIR;

        List<SemanticModel> trainingData = new ArrayList<SemanticModel>();//?????????training SemanticModel?????????

        /**Import all of the semantic models, including new data source and training data source, into Karma. 14 Aug 2018**/
        if(semanticModels == null) {
            semanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
        }

        /**begin to import the common data model (CDM)**/
        if(ontologyManager == null) {
            ontologyManager = new OntologyManager(contextParameters.getId());

            File oFile = new File(Params.ROOT_DIR+"ecrm_update(20190521).owl");

            ontologyManager.doImport(oFile, "UTF-8");
            ontologyManager.updateCache();
            System.out.println("2.ontologyManager???"+ontologyManager.getObjectProperties().size());
        }

        ModelLearningGraph modelLearningGraph = null;

        ModelLearner_KnownModels4 modelLearner;

        boolean iterativeEvaluation = false;
        boolean useCorrectType = true;
        boolean randomModel = false;

        int numberOfCandidates = 4;
        int numberOfKnownModels;
        String filePath = Params.RESULTS_DIR + "temp/";
        String filename = "";
        filename += "results";
        filename += useCorrectType ? "-correct types":"-k=" + numberOfCandidates;
        filename += randomModel ? "-random":"";
        filename += iterativeEvaluation ? "-iterative":"";
        filename += ".csv";


        /**Get the semantic model of the new data source
         ???????????????newSourceIndex??????????????????????????????????????????**/
        SemanticModel newSource = semanticModels.get(newSourceIndex);

        logger.info("======================================================");
        logger.info(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");//???????????????????????????
        System.out.println(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");
        logger.info("======================================================");


        /**collect all of the training data set**/

        numberOfKnownModels = trainDataIndex.length;
        System.out.println("numberOfKnownModels:"+numberOfKnownModels);
        for (int i = 0; i < trainDataIndex.length; i++) {
            trainingData.add(semanticModels.get(trainDataIndex[i]));

        }

        /**Until now, the 'userSemanticTypes' and 'learnedSemanticTypes' are still null. 18 June 2018.**/
        modelLearningGraph = (ModelLearningGraphCompact)ModelLearningGraph.getEmptyInstance(ontologyManager, ModelLearningGraphType.Compact);

        /**??????????????????????????????????????????????????????????????????**/
        SemanticModel correctModel = newSource;

        /**Get the Steiner nodes (boxes) from the new source. 8 June 2018.
         ?????????????????????????????????????????????????????????????????????**/
        List<ColumnNode> columnNodes = correctModel.getColumnNodes();

        /**???????????????????????????????????????????????????Node???????????????**/
        List<Node> steinerNodes = new LinkedList<Node>(columnNodes);//get steiner node. very important. 19 Aug 2018

        modelLearner = new ModelLearner_KnownModels4(ontologyManager, steinerNodes);

        System.out.println("steinerNodes:"+steinerNodes.size());
        System.out.println("???????????????modelLearner???????????????:"+modelLearner.graphBuilder.getGraph().vertexSet().size());
        System.out.println("???????????????modelLearner????????????:"+modelLearner.graphBuilder.getGraph().edgeSet().size());

        System.out.println("????????????");
        long start = System.currentTimeMillis();

        //??????integration graph?????????
        String graphName = !iterativeEvaluation?
                graphPath + semanticModels.get(newSourceIndex).getName() + Params.GRAPH_JSON_FILE_EXT :
                graphPath + semanticModels.get(newSourceIndex).getName() + ".knownModels=" + numberOfKnownModels + Params.GRAPH_JSON_FILE_EXT;


        for (SemanticModel sm : trainingData) {

            /**7.22**/
//            modelLearningGraph.addModelAndUpdate(sm, PatternWeightSystem.JWSPaperFormula);//??????????????????????????????????????????
            modelLearningGraph.addModelAndUpdate2016(sm, PatternWeightSystem.JWSPaperFormula);//??????????????????????????????????????????
            /**7.22**/
            System.out.println("???????????????????????????modelLearningGraph???????????????"+modelLearningGraph.getGraphBuilder().getGraph().vertexSet().size());
            System.out.println("???????????????????????????modelLearningGraph????????????"+modelLearningGraph.getGraphBuilder().getGraph().edgeSet().size());
        }

        modelLearner = new ModelLearner_KnownModels4(modelLearningGraph.getGraphBuilder(), steinerNodes);
        System.out.println("??????modelLearner???????????????"+modelLearner.graphBuilder.getGraph().vertexSet().size());
        System.out.println("??????modelLearner????????????"+modelLearner.graphBuilder.getGraph().edgeSet().size());


        /**4.13??????  ???????????????integration graph**/
//        /**2022-04-06 ???????????????????????????**/
//        modelLearningGraph.addSemanticTypesOnModel(newSource);
//        /**2022-04-06 ???????????????????????????**/
//
//        /**2022-04-07 ????????????????????????**/
//        modelLearningGraph.addOntologyPathsOnModel(ontologyManager);
//        /**2022-04-07 ????????????????????????**/
        /**4.13  ???????????????integration graph??????**/

        System.out.println("???????????????modelLearner???????????????"+modelLearner.graphBuilder.getGraph().vertexSet().size());
        System.out.println("???????????????modelLearner????????????"+modelLearner.graphBuilder.getGraph().edgeSet().size());

        /**4.6 9:14**/
//        for(DefaultLink link: modelLearningGraph.getGraphBuilder().getGraph().edgeSet()){
//            System.out.println("????????????????????????????????????"+link.getTarget());
//        }
        /**4.6 9:14**/


        /**4.6 9???10**/
        modelLearner.graphBuilder = modelLearningGraph.getGraphBuilder();
        modelLearner.nodeIdFactory = modelLearner.graphBuilder.getNodeIdFactory();

        /**Compute Steiner tree for a single table. 17 May 2018. //Generating and Ranking Semantic Models (using karma's metrics) **/

        List<SortableSemanticModel> hypothesisList = modelLearner.hypothesize(useCorrectType, numberOfCandidates);
        System.out.println(modelLearner.graphBuilder.getGraph().edgeSet().size());
        System.out.println(modelLearner.graphBuilder.getGraph().vertexSet().size());


        /**??????inverse property????????????**/
//        ontModel.read("file:E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\ecrm_update(20190521).owl");
//        System.out.println(+modelLearner.graphBuilder.getOntologyManager().newgetInverseOfProperty("http://erlangen-crm.org/current/P138i_has_representation",ontModel).getUri());
        /**??????inverse property????????????**/

        /**7.18 ???????????????????????????link**/
//        int isexit = 0;
//        for(DefaultLink link: modelLearner.graphBuilder.getGraph().edgeSet()){
//            if(link.getSource().getId().equals("http://erlangen-crm.org/current/E22_Man-Made_Object1")&&(link.getTarget().getId().equals("http://erlangen-crm.org/current/E31_Document1"))){
//                isexit = 1;
//                System.out.println("?????????link");
//                System.out.println("??????link.getUri:" + link.getUri());
////                break;
//            }
////            if((link.getUri().equals("http://erlangen-crm.org/current/P70i_is_documented_in"))){
////                isexit = 1;
////                System.out.println("?????????link");
////                break;
////            }
//        }
//        if(isexit == 1){
//            System.out.println("?????????link");
//        }
//        else{
//            System.out.println("?????????link");
//        }
        /**7.18 ???????????????????????????link**/

        /**??????integration graph**/
        GraphVizUtil.exportJGraphToGraphviz(modelLearner.graphBuilder.getGraph(),
                "integration_graph",
                false,
                GraphVizLabelType.LocalId,
                GraphVizLabelType.LocalUri,
                false,
                true,
                "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\alignment-graph\\final-integration-graph\\" + newSource.getName() + ".integration-graph.graph.json" + ".dot");

        /**4.6 9???10**/

        long elapsedTimeMillis = System.currentTimeMillis() - start;
        float elapsedTimeSec = elapsedTimeMillis/1000F;

        System.out.println("time: " + elapsedTimeSec);

        int cutoff = 20;//ModelingConfiguration.getMaxCandidateModels();
        List<SortableSemanticModel> topHypotheses = null;
        if (hypothesisList != null) {//hypothesisList?????????????????????????????????semantic models???topHypotheses?????????hypothesisList?????????????????????cutoff???senmantic models
            topHypotheses = hypothesisList.size() > cutoff ?
                    hypothesisList.subList(0, cutoff) :
                    hypothesisList;
        }

        Map<String, SemanticModel> models = new TreeMap<String, SemanticModel>();

        ModelEvaluation me;
        models.put("1-correct model", correctModel);
        if (topHypotheses != null) {
            for (int k = 0; k < topHypotheses.size(); k++) {

                SortableSemanticModel m = topHypotheses.get(k);

//                me = m.evaluate(correctModel);
                me = m.new_evaluate(correctModel);

                String label = "candidate " + k + "\n" +
                        "link coherence:" + (m.getLinkCoherence() == null ? "" : m.getLinkCoherence().getCoherenceValue()) + "\n";
                label += (m.getSteinerNodes() == null || m.getSteinerNodes().getCoherence() == null) ?
                        "" : "node coherence:" + m.getSteinerNodes().getCoherence().getCoherenceValue() + "\n";
                label += "confidence:" + m.getConfidenceScore() + "\n";
                label += m.getSteinerNodes() == null ? "" : "mapping score:" + m.getSteinerNodes().getScore() + "\n";
                label +=
                        "cost:" + roundDecimals(m.getCost(), 6) + "\n" +
                                //								"-distance:" + me.getDistance() +
                                "-precision:" + me.getPrecision() +
                                "-recall:" + me.getRecall();

                models.put(label, m);

                if (k == 0) { // first rank model
                    System.out.println("number of known models: " + numberOfKnownModels +
                            ", precision: " + me.getPrecision() +
                            ", recall: " + me.getRecall() +
                            ", time: " + elapsedTimeSec);
                    logger.info("number of known models: " + numberOfKnownModels +
                            ", precision: " + me.getPrecision() +
                            ", recall: " + me.getRecall() +
                            ", time: " + elapsedTimeSec);

                    String s = "";
                    if (iterativeEvaluation) {
//                        if (resultsArray[numberOfKnownModels + 2].length() > 0)
//                            resultsArray[numberOfKnownModels + 2].append(" \t ");
//                        resultsArray[numberOfKnownModels + 2].append(s);
                    } else {
                        s = newSource.getName() + "," + me.getPrecision() + "," + me.getRecall() + "," + elapsedTimeSec;
                        System.out.println(s);
                    }
                }
            }
        }

        String outputPath = Params.OUTPUT_DIR;
        String outName = !iterativeEvaluation?
                outputPath + semanticModels.get(newSourceIndex).getName() + Params.GRAPHVIS_OUT_DETAILS_FILE_EXT :
                outputPath + semanticModels.get(newSourceIndex).getName() + ".knownModels=" + numberOfKnownModels + Params.GRAPHVIS_OUT_DETAILS_FILE_EXT;

        GraphVizUtil.exportSemanticModelsToGraphviz(
                models,
                newSource.getName(),
                outName,
                GraphVizLabelType.LocalId,
                GraphVizLabelType.LocalUri,
                true,
                true);
        return hypothesisList;
    }


    public static DirectedWeightedMultigraph<Node, DefaultLink> getIntegrationGraph(int newSourceIndex, Integer[] trainDataIndex) throws Exception {

        ServletContextParameterMap contextParameters = ContextParametersRegistry.getInstance().getDefault();

        //????????????integration graph?????????
        String graphPath = Params.GRAPHS_DIR;

        List<SemanticModel> trainingData = new ArrayList<SemanticModel>();//?????????training SemanticModel?????????

        //???????????????semantic models
        if(semanticModels == null) {
//            semanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);//local
            semanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);//local
        }
        //??????ontology????????????
        if(ontologyManager == null) {
            ontologyManager = new OntologyManager(contextParameters.getId());
            File oFile = new File(Params.ROOT_DIR+"ecrm_update(20190521).owl");

            ontologyManager.doImport(oFile, "UTF-8");
            ontologyManager.updateCache();
            System.out.println("2.ontologyManager???"+ontologyManager.getObjectProperties().size());
        }

        ModelLearningGraph modelLearningGraph = null;

        ModelLearner_KnownModels4 modelLearner;

        boolean iterativeEvaluation = false;
        boolean useCorrectType = true;
        boolean randomModel = false;

        int numberOfCandidates = 4;
        int numberOfKnownModels;
        String filePath = Params.RESULTS_DIR + "temp/";
        String filename = "";
        filename += "results";
        filename += useCorrectType ? "-correct types":"-k=" + numberOfCandidates;
        filename += randomModel ? "-random":"";
        filename += iterativeEvaluation ? "-iterative":"";
        filename += ".csv";

        /**Get the semantic model of the new data source
         ???????????????newSourceIndex??????????????????????????????????????????**/
        SemanticModel newSource = semanticModels.get(newSourceIndex);

        logger.info("======================================================");
        logger.info(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");//???????????????????????????
        System.out.println(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");
        logger.info("======================================================");

        numberOfKnownModels = trainDataIndex.length;
        System.out.println("numberOfKnownModels:"+numberOfKnownModels);
        for (int i = 0; i < trainDataIndex.length; i++) {
            trainingData.add(semanticModels.get(trainDataIndex[i]));
        }

        modelLearningGraph = (ModelLearningGraphCompact)ModelLearningGraph.getEmptyInstance(ontologyManager, ModelLearningGraphType.Compact);

        /**??????????????????????????????????????????????????????????????????**/
        SemanticModel correctModel = newSource;

        /**Get the Steiner nodes (boxes) from the new source. 8 June 2018.
         ?????????????????????????????????????????????????????????????????????**/
        List<ColumnNode> columnNodes = correctModel.getColumnNodes();

        /**???????????????????????????????????????????????????Node???????????????**/
        List<Node> steinerNodes = new LinkedList<Node>(columnNodes);//get steiner node. very important. 19 Aug 2018

        modelLearner = new ModelLearner_KnownModels4(ontologyManager, steinerNodes);
        long start = System.currentTimeMillis();
        //??????integration graph?????????
        String graphName = !iterativeEvaluation?
                graphPath + semanticModels.get(newSourceIndex).getName() + Params.GRAPH_JSON_FILE_EXT :
                graphPath + semanticModels.get(newSourceIndex).getName() + ".knownModels=" + numberOfKnownModels + Params.GRAPH_JSON_FILE_EXT;

        for (SemanticModel sm : trainingData) {
            modelLearningGraph.addModelAndUpdate(sm, PatternWeightSystem.JWSPaperFormula);//??????????????????????????????????????????
            System.out.println("???????????????????????????modelLearningGraph???????????????"+modelLearningGraph.getGraphBuilder().getGraph().vertexSet().size());
            System.out.println("???????????????????????????modelLearningGraph????????????"+modelLearningGraph.getGraphBuilder().getGraph().edgeSet().size());
        }
        modelLearner = new ModelLearner_KnownModels4(modelLearningGraph.getGraphBuilder(), steinerNodes);
        modelLearner.graphBuilder = modelLearningGraph.getGraphBuilder();
        modelLearner.nodeIdFactory = modelLearner.graphBuilder.getNodeIdFactory();

        modelLearner.hypothesize2(useCorrectType, numberOfCandidates);

        System.out.println(modelLearner.graphBuilder.getGraph().edgeSet().size());
        System.out.println(modelLearner.graphBuilder.getGraph().vertexSet().size());

        return modelLearner.graphBuilder.getGraph();
    }

    /**5.20**/
    public static DirectedWeightedMultigraph<Node, DefaultLink> getIntegrationGraphPrediction(int newSourceIndex, Integer[] trainDataIndex) throws Exception {

        ServletContextParameterMap contextParameters = ContextParametersRegistry.getInstance().getDefault();

        //????????????integration graph?????????
        String graphPath = Params.GRAPHS_DIR;

        List<SemanticModel> trainingData = new ArrayList<SemanticModel>();//?????????training SemanticModel?????????

        //???????????????semantic models
        if(semanticModels == null) {
            semanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
        }
        //??????ontology????????????
        if(ontologyManager == null) {
            ontologyManager = new OntologyManager(contextParameters.getId());
//            System.out.println("1.ontologyManager???"+ontologyManager.getObjectProperties().size());//////////////
//            File oFile = new File(Params.ROOT_DIR + "weapon.owl");
            File oFile = new File(Params.ROOT_DIR+"ecrm_update(20190521).owl");

            ontologyManager.doImport(oFile, "UTF-8");
            ontologyManager.updateCache();
            System.out.println("2.ontologyManager???"+ontologyManager.getObjectProperties().size());
        }

        ModelLearningGraph modelLearningGraph = null;

        ModelLearner_KnownModels4 modelLearner;

        boolean iterativeEvaluation = false;
        boolean useCorrectType = true;
        boolean randomModel = false;

        int numberOfCandidates = 4;
        int numberOfKnownModels;
        String filePath = Params.RESULTS_DIR + "temp/";
        String filename = "";
        filename += "results";
        filename += useCorrectType ? "-correct types":"-k=" + numberOfCandidates;
        filename += randomModel ? "-random":"";
        filename += iterativeEvaluation ? "-iterative":"";
        filename += ".csv";

        /**Get the semantic model of the new data source
         ???????????????newSourceIndex??????????????????????????????????????????**/
        SemanticModel newSource = semanticModels.get(newSourceIndex);

        logger.info("======================================================");
        logger.info(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");//???????????????????????????
        System.out.println(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");
        logger.info("======================================================");

        numberOfKnownModels = trainDataIndex.length;
        System.out.println("numberOfKnownModels:"+numberOfKnownModels);
        for (int i = 0; i < trainDataIndex.length; i++) {
            trainingData.add(semanticModels.get(trainDataIndex[i]));
        }

        modelLearningGraph = (ModelLearningGraphCompact)ModelLearningGraph.getEmptyInstance(ontologyManager, ModelLearningGraphType.Compact);

        /**??????????????????????????????????????????????????????????????????**/
        SemanticModel correctModel = newSource;

        /**Get the Steiner nodes (boxes) from the new source. 8 June 2018.
         ?????????????????????????????????????????????????????????????????????**/
        List<ColumnNode> columnNodes = correctModel.getColumnNodes();

        /**???????????????????????????????????????????????????Node???????????????**/
        List<Node> steinerNodes = new LinkedList<Node>(columnNodes);//get steiner node. very important. 19 Aug 2018

        modelLearner = new ModelLearner_KnownModels4(ontologyManager, steinerNodes);

        long start = System.currentTimeMillis();
        //??????integration graph?????????
        String graphName = !iterativeEvaluation?
                graphPath + semanticModels.get(newSourceIndex).getName() + Params.GRAPH_JSON_FILE_EXT :
                graphPath + semanticModels.get(newSourceIndex).getName() + ".knownModels=" + numberOfKnownModels + Params.GRAPH_JSON_FILE_EXT;

        for (SemanticModel sm : trainingData) {
            modelLearningGraph.addModelAndUpdate(sm, PatternWeightSystem.JWSPaperFormula);//??????????????????????????????????????????
            System.out.println("???????????????????????????modelLearningGraph???????????????"+modelLearningGraph.getGraphBuilder().getGraph().vertexSet().size());
            System.out.println("???????????????????????????modelLearningGraph????????????"+modelLearningGraph.getGraphBuilder().getGraph().edgeSet().size());
        }
        modelLearner = new ModelLearner_KnownModels4(modelLearningGraph.getGraphBuilder(), steinerNodes);
        modelLearner.graphBuilder = modelLearningGraph.getGraphBuilder();
        modelLearner.nodeIdFactory = modelLearner.graphBuilder.getNodeIdFactory();

        //????????????????????????
        modelLearner.hypothesize2(useCorrectType, numberOfCandidates);

        System.out.println(modelLearner.graphBuilder.getGraph().edgeSet().size());
        System.out.println(modelLearner.graphBuilder.getGraph().vertexSet().size());

        return modelLearner.graphBuilder.getGraph();
    }

    public static List<SortableSemanticModel> getCandidateSemanticModels(int newSourceIndex, Integer[] trainDataIndex, String outputPath) throws Exception {


        ServletContextParameterMap contextParameters = ContextParametersRegistry.getInstance().getDefault();


        /**Import all of the semantic models, including new data source and training data source, into Karma. 14 Aug 2018**/
        if(semanticModels == null) {
            semanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-tmp", Params.MODEL_MAIN_FILE_EXT);
        }


        List<SemanticModel> trainingData = new ArrayList<SemanticModel>();

        /**begin to import the common data model (CDM)**/
        if(ontologyManager == null) {
            ontologyManager = new OntologyManager(contextParameters.getId());
            File oFile = new File(Params.ROOT_DIR+"ecrm_update(20190521).owl");
            ontologyManager.doImport(oFile, "UTF-8");
            ontologyManager.updateCache();
        }


        ModelLearningGraph modelLearningGraph = null;

        ModelLearner_KnownModels4 modelLearner;

        boolean iterativeEvaluation = false;
        boolean useCorrectType = true;
        boolean randomModel = false;

        int numberOfCandidates = 1;
        int numberOfKnownModels;
        String filePath = Params.RESULTS_DIR + "temp/";
        String filename = "";
        filename += "results";
        filename += useCorrectType ? "-correct types":"-k=" + numberOfCandidates;
        filename += randomModel ? "-random":"";
        filename += iterativeEvaluation ? "-iterative":"";
        filename += ".csv";



        /**Get the semantic model of the new data source**/
        SemanticModel newSource = semanticModels.get(newSourceIndex);

        logger.info("======================================================");
        logger.info(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");
        System.out.println(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");
        logger.info("======================================================");


        /**collect all of the training data set**/

        numberOfKnownModels = trainDataIndex.length;
        for (int i = 0; i < trainDataIndex.length; i++) {
            trainingData.add(semanticModels.get(trainDataIndex[i]));
        }


        /**Until now, the 'userSemanticTypes' and 'learnedSemanticTypes' are still null. 18 June 2018.**/
        modelLearningGraph = (ModelLearningGraphCompact)ModelLearningGraph.getEmptyInstance(ontologyManager, ModelLearningGraphType.Compact);

        SemanticModel correctModel = newSource;

        /**Get the Steiner nodes (boxes) from the new source. 8 June 2018.**/
        List<ColumnNode> columnNodes = correctModel.getColumnNodes();


        List<Node> steinerNodes = new LinkedList<Node>(columnNodes);//get steiner node. very important. 19 Aug 2018



        modelLearner = new ModelLearner_KnownModels4(ontologyManager, steinerNodes);

        long start = System.currentTimeMillis();

        for (SemanticModel sm : trainingData)
            modelLearningGraph.addModelAndUpdate(sm, PatternWeightSystem.JWSPaperFormula);

        modelLearner.graphBuilder = modelLearningGraph.getGraphBuilder();
        modelLearner.nodeIdFactory = modelLearner.graphBuilder.getNodeIdFactory();


        /**Compute Steiner tree for a single table. 17 May 2018. //Generating and Ranking Semantic Models (using karma's metrics) **/
        List<SortableSemanticModel> hypothesisList = modelLearner.hypothesize(useCorrectType, numberOfCandidates);

        long elapsedTimeMillis = System.currentTimeMillis() - start;
        float elapsedTimeSec = elapsedTimeMillis/1000F;

        System.out.println("time: " + elapsedTimeSec);

        int cutoff = 20;//ModelingConfiguration.getMaxCandidateModels();
        List<SortableSemanticModel> topHypotheses = null;
        if (hypothesisList != null) {
            topHypotheses = hypothesisList.size() > cutoff ?
                    hypothesisList.subList(0, cutoff) :
                    hypothesisList;
        }

        Map<String, SemanticModel> models = new TreeMap<String, SemanticModel>();

        ModelEvaluation me;
        models.put("1-correct model", correctModel);
        if (topHypotheses != null) {
            for (int k = 0; k < topHypotheses.size(); k++) {

                SortableSemanticModel m = topHypotheses.get(k);

                me = m.evaluate(correctModel);

                String label = "candidate " + k + "\n" +
//								(m.getSteinerNodes() == null ? "" : m.getSteinerNodes().getScoreDetailsString()) +
                        "link coherence:" + (m.getLinkCoherence() == null ? "" : m.getLinkCoherence().getCoherenceValue()) + "\n";
                label += (m.getSteinerNodes() == null || m.getSteinerNodes().getCoherence() == null) ?
                        "" : "node coherence:" + m.getSteinerNodes().getCoherence().getCoherenceValue() + "\n";
                label += "confidence:" + m.getConfidenceScore() + "\n";
                label += m.getSteinerNodes() == null ? "" : "mapping score:" + m.getSteinerNodes().getScore() + "\n";
                label +=
                        "cost:" + roundDecimals(m.getCost(), 6) + "\n" +
                                //								"-distance:" + me.getDistance() +
                                "-precision:" + me.getPrecision() +
                                "-recall:" + me.getRecall();

                models.put(label, m);

                if (k == 0) { // first rank model
                    System.out.println("number of known models: " + numberOfKnownModels +
                            ", precision: " + me.getPrecision() +
                            ", recall: " + me.getRecall() +
                            ", time: " + elapsedTimeSec);
                    logger.info("number of known models: " + numberOfKnownModels +
                            ", precision: " + me.getPrecision() +
                            ", recall: " + me.getRecall() +
                            ", time: " + elapsedTimeSec);
                    String s = "";
                    if (iterativeEvaluation) {
//                        if (resultsArray[numberOfKnownModels + 2].length() > 0)
//                            resultsArray[numberOfKnownModels + 2].append(" \t ");
//                        resultsArray[numberOfKnownModels + 2].append(s);
                    } else {
                        s = newSource.getName() + "," + me.getPrecision() + "," + me.getRecall() + "," + elapsedTimeSec;
                        System.out.println(s);
                    }
                }
            }
        }



        String outName = !iterativeEvaluation?
                outputPath + "\\" + semanticModels.get(newSourceIndex).getName() + Params.GRAPHVIS_OUT_DETAILS_FILE_EXT :
                outputPath + "\\" + semanticModels.get(newSourceIndex).getName() + ".knownModels=" + numberOfKnownModels + Params.GRAPHVIS_OUT_DETAILS_FILE_EXT;

        GraphVizUtil.exportSemanticModelsToGraphviz(
                models,
                newSource.getName(),
                outName,
                GraphVizLabelType.LocalId,
                GraphVizLabelType.LocalUri,
                true,
                true);

        return hypothesisList;

    }

    /**Get a node from knowledge graph*
     *@start from 28 May 2019
     * @param nodeUri
     * @param graph
     * @return node that named that URI
     * */
    public static Node getNodeFromDirectedWeightedMultigraph (String nodeUri, DirectedWeightedMultigraph<Node,DefaultLink> graph) {

        Node node = null;
        Set<Node> nodeSet = graph.vertexSet();
        for (Node node1 : nodeSet) {

            if (node1.getUri().equals(nodeUri)) {
                node = node1;
            }
        }
        return node;
    }

    /**Print graph*
     * @start from 29 May 2019
     * */
    public static void printDirectedWeightedMultigraph (DirectedWeightedMultigraph<Node,DefaultLink> graph) {
        Set<Node> nodeSet = graph.vertexSet();
        Set<DefaultLink> defaultLinks = graph.edgeSet();
        for (Node node : nodeSet) {
            String uri = node.getUri();
            System.out.println("Node URI is: " + uri);
        }


        for (DefaultLink defaultLink : defaultLinks) {
            String linkUri = defaultLink.getUri();
            Node source = defaultLink.getSource();
            Node target = defaultLink.getTarget();
            System.out.println("Edge URI is: " + linkUri + ", the source URI is: " + source.getUri() + ", the target URI is: " + target.getUri());
            //System.out.println("Edge ID is: " + defaultLink.getId() + ", the source ID is: " + source.getId() + ", the target ID is: " + target.getId());
        }



    }

    /**SemanticModel?????????SortableSemanticModel ???CorrectSemanticModel????????????**/
    public static void EvaluateSemanticModel(int SourceId) throws Exception {
        if(semanticModels == null) {
            semanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
        }

        /**Get the semantic model of the new data source
         ???????????????newSourceIndex??????????????????????????????????????????**/
        SemanticModel newSource = semanticModels.get(SourceId);
        SemanticModel correctModel = newSource.clone();

        //E22_Man-Made_Object1
        Node sourcenode1 = null, targetnode1 = null, targetnode2 = null, targetnode3 = null, targetnode4 = null, targetnode5 = null;
        //E12_Production1
        Node sourcenode2 = null, targetnode2_1 = null;
        Node targetnode3_1 = null;
        Node E35_Title1 = null, E54_Dimension1 = null , E12_Production1 = null  ,E52_Time_Span3 = null, E55_Type1 = null,
                E67_Birth1 = null, Begin_Date = null, E69_Death1 = null, E21_Person1 = null, E82_Actor_Appellation = null, Actor_URL = null;

        logger.info("======================================================");
        logger.info(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");//???????????????????????????
        System.out.println(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");
        System.out.println("?????????links?????????"+ newSource.getGraph().edgeSet().size());
        logger.info("======================================================");



        for(Node node: newSource.getGraph().vertexSet()) {
            //E22_Man-Made_Object1
            if(node.getId().equals("http://erlangen-crm.org/current/E22_Man-Made_Object1")){
                sourcenode1 = node;
            }
            //Attribution
            if(node.getId().equals("HN1382")){
                targetnode1 = node;
            }
            //Title
            if(node.getId().equals("HN1385")){
                targetnode2 = node;
            }
            //Medium
            if(node.getId().equals("HN1387")){
                targetnode3 = node;
            }
            //E52_Time-Span1
            if(node.getId().equals("http://erlangen-crm.org/current/E52_Time-Span1")){
                targetnode4 = node;
            }
            //E52_Time-Span2
            if(node.getId().equals("http://erlangen-crm.org/current/E52_Time-Span2")){
                targetnode5 = node;
            }

            //E12_Production1
            if(node.getId().equals("http://erlangen-crm.org/current/E12_Production1")){
                sourcenode2 = node;
            }
            //Dimensions
            if(node.getId().equals("HN1388")){
                targetnode2_1 = node;
            }

            //Dated
            if(node.getId().equals("HN1386")){
                targetnode3_1 = node;
            }

            //E35_Title1
            if(node.getId().equals("http://erlangen-crm.org/current/E35_Title1")){
                E35_Title1 = node;
            }
            //E54_Dimension1
            if(node.getId().equals("http://erlangen-crm.org/current/E54_Dimension1")){
                E54_Dimension1 = node;
            }
            //E12_Production1
            if(node.getId().equals("http://erlangen-crm.org/current/E12_Production1")){
                E12_Production1 = node;
            }
            //E52_Time-Span3
            if(node.getId().equals("http://erlangen-crm.org/current/E52_Time-Span3")){
                E52_Time_Span3 = node;
            }
            //E55_Type1
            if(node.getId().equals("http://erlangen-crm.org/current/E55_Type1")){
                E55_Type1 = node;
            }
            //E67_Birth1
            if(node.getId().equals("http://erlangen-crm.org/current/E67_Birth1")){
                E67_Birth1 = node;
            }
            //Begin Date
            if(node.getId().equals("HN1383")){
                Begin_Date= node;
            }
            //E69_Death1
            if(node.getId().equals("http://erlangen-crm.org/current/E69_Death1")){
                E69_Death1 = node;
            }
            //E21_Person1
            if(node.getId().equals("http://erlangen-crm.org/current/E21_Person1")){
                E21_Person1 = node;
            }
            //E82_Actor_Appellation
            if(node.getId().equals("http://erlangen-crm.org/current/E82_Actor_Appellation1")){
                E82_Actor_Appellation = node;
            }
            //Actor_URL
            if(node.getId().equals("HN2033")){
                Actor_URL = node;
            }
        }

        /**???????????????links**/
        //E22_Man-Made_Object1->P3_has_note->Attribution
        String addedlinkId = LinkIdFactory.getLinkId("http://erlangen-crm.org/current/P3_has_note", "http://erlangen-crm.org/current/E22_Man-Made_Object1", "HN1382");
        LabeledLink addedlink = new DataPropertyLink(addedlinkId, new Label("http://erlangen-crm.org/current/P3_has_note"));
        newSource.getGraph().addEdge(sourcenode1,targetnode1,addedlink);

        //E22_Man-Made_Object1->P3_has_note->Title
        addedlinkId = LinkIdFactory.getLinkId("http://erlangen-crm.org/current/P3_has_note", "http://erlangen-crm.org/current/E22_Man-Made_Object1", "HN1385");
        addedlink = new DataPropertyLink(addedlinkId, new Label("http://erlangen-crm.org/current/P3_has_note"));
        newSource.getGraph().addEdge(sourcenode1,targetnode2,addedlink);

        //E22_Man-Made_Object1->P3_has_note->Medium
        addedlinkId = LinkIdFactory.getLinkId("http://erlangen-crm.org/current/P3_has_note", "http://erlangen-crm.org/current/E22_Man-Made_Object1", "HN1387");
        addedlink = new DataPropertyLink(addedlinkId, new Label("http://erlangen-crm.org/current/P3_has_note"));
        newSource.getGraph().addEdge(sourcenode1,targetnode3,addedlink);

        //E22_Man-Made_Object1->P62_depicts->E52_Time-Span1
        addedlinkId = LinkIdFactory.getLinkId("http://erlangen-crm.org/current/P62_depicts", "http://erlangen-crm.org/current/E22_Man-Made_Object1", "http://erlangen-crm.org/current/E52_Time-Span1");
        addedlink = new DataPropertyLink(addedlinkId, new Label("http://erlangen-crm.org/current/P62_depicts"));
        newSource.getGraph().addEdge(sourcenode1,targetnode4,addedlink);

        //E22_Man-Made_Object1->P62_depicts->E52_Time-Span2
        addedlinkId = LinkIdFactory.getLinkId("http://erlangen-crm.org/current/P62_depicts", "http://erlangen-crm.org/current/E22_Man-Made_Object1", "http://erlangen-crm.org/current/E52_Time-Span2");
        addedlink = new DataPropertyLink(addedlinkId, new Label("http://erlangen-crm.org/current/P62_depicts"));
        newSource.getGraph().addEdge(sourcenode1,targetnode5,addedlink);

//        //E12_Production1->P3_has_note->Dimensions
//        addedlinkId = LinkIdFactory.getLinkId("http://erlangen-crm.org/current/P3_has_note", "http://erlangen-crm.org/current/E12_Production1", "HN1388");
//        addedlink = new DataPropertyLink(addedlinkId, new Label("http://erlangen-crm.org/current/P3_has_note"));
//        newSource.getGraph().addEdge(sourcenode2,targetnode2_1,addedlink);

        //E22_Man-Made_Object1->P3_has_note->Dimensions
        addedlinkId = LinkIdFactory.getLinkId("http://erlangen-crm.org/current/P3_has_note", "http://erlangen-crm.org/current/E22_Man-Made_Object1", "HN1388");
        addedlink = new DataPropertyLink(addedlinkId, new Label("http://erlangen-crm.org/current/P3_has_note"));
        newSource.getGraph().addEdge(sourcenode1,targetnode2_1,addedlink);

        //E52_Time-Span1->P82_at_some_time_within->Dated
        addedlinkId = LinkIdFactory.getLinkId("http://erlangen-crm.org/current/P82_at_some_time_within", "http://erlangen-crm.org/current/E52_Time-Span1", "HN1386");
        addedlink = new DataPropertyLink(addedlinkId, new Label("http://erlangen-crm.org/current/P82_at_some_time_within"));
        newSource.getGraph().addEdge(targetnode4,targetnode3_1,addedlink);

        /**????????????links**/
        newSource.getGraph().removeEdge(sourcenode1,E35_Title1);//E22_Man-Made_Object1->E35_Title1
        newSource.getGraph().removeEdge(E35_Title1,targetnode2);//E35_Title1->Title
        newSource.getGraph().removeEdge(sourcenode1,E54_Dimension1);//E22_Man-Made_Object1->E54_Dimension1
        newSource.getGraph().removeEdge(E54_Dimension1,targetnode2_1);//E54_Dimension1->Dimensions
        newSource.getGraph().removeEdge(E12_Production1,E52_Time_Span3);//E12_Production1->E52_Time-Span3
        newSource.getGraph().removeEdge(E52_Time_Span3,targetnode3_1);//E52_Time-Span3->Dated
        newSource.getGraph().removeEdge(E12_Production1,E55_Type1);//E12_Production1->E55_Type1
        newSource.getGraph().removeEdge(E55_Type1,targetnode3);//E55_Type1->Medium
        newSource.getGraph().removeEdge(E67_Birth1,targetnode4);//E67_Birth1->E52_Time-Span1
        newSource.getGraph().removeEdge(E69_Death1,targetnode5);//E69_Death1->E52_Time-Span2
        newSource.getGraph().removeEdge(E21_Person1,E82_Actor_Appellation);//E21_Person1->E82_Actor_Appellation
        newSource.getGraph().removeEdge(E82_Actor_Appellation,targetnode1);//E82_Actor_Appellation->Attribution

        /**???????????????nodes**/
        newSource.getGraph().removeVertex(E35_Title1);//E35_Title1
        newSource.getGraph().removeVertex(E54_Dimension1);//E54_Dimension1
        newSource.getGraph().removeVertex(E52_Time_Span3);//E52_Time-Span3
        newSource.getGraph().removeVertex(E55_Type1);//E55_Type1
        newSource.getGraph().removeVertex(E82_Actor_Appellation);//E82_Actor_Appellation

        /**5.14**/
        newSource.getGraph().removeVertex(targetnode3);//Medium
        newSource.getGraph().removeVertex(Actor_URL);//Actor_URL


        GraphVizUtil.exportSemanticModelToGraphviz(newSource,GraphVizLabelType.LocalId,
                GraphVizLabelType.LocalUri,true,true,"E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\evaluation-test\\" + "test" + ".graph.json" + ".dot");
        System.out.println("?????????nodes?????????"+ newSource.getGraph().vertexSet().size());
        System.out.println("?????????links?????????"+ newSource.getGraph().edgeSet().size());


        SortableSemanticModel sm = new SortableSemanticModel(newSource,true);
        System.out.println("sm???nodes?????????"+ sm.getGraph().vertexSet().size());
        System.out.println("sm???links?????????"+ sm.getGraph().edgeSet().size());
        System.out.println("correctModel???nodes?????????"+ correctModel.getGraph().vertexSet().size());
        System.out.println("correctModel???links?????????"+ correctModel.getGraph().edgeSet().size());

        ModelEvaluation me;
        me = sm.evaluate(correctModel);
        System.out.println("precision: " + me.getPrecision() +
                ", recall: " + me.getRecall());
    }

    /**2022.5.29 ??????????????????????????????-?????????????????????integration graph(correct semantic types)**/
    public static DirectedWeightedMultigraph<Node, DefaultLink> getIntegrationGraph_AllSMWithCorrectSTs() throws Exception{
        ServletContextParameterMap contextParameters = ContextParametersRegistry.getInstance().getDefault();

        //????????????integration graph?????????
        String graphPath = Params.GRAPHS_DIR;

        List<SemanticModel> trainingData = new ArrayList<SemanticModel>();//?????????training SemanticModel?????????

        //???????????????semantic models
        if(semanticModels == null) {
            semanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
        }
        //??????ontology????????????
        if(ontologyManager == null) {
            ontologyManager = new OntologyManager(contextParameters.getId());
//            System.out.println("1.ontologyManager???"+ontologyManager.getObjectProperties().size());//////////////
//            File oFile = new File(Params.ROOT_DIR + "weapon.owl");
            File oFile = new File(Params.ROOT_DIR+"ecrm_update(20190521).owl");

            ontologyManager.doImport(oFile, "UTF-8");
            ontologyManager.updateCache();
            System.out.println("getIntegrationGraph_AllSMWithCorrectSTs???ontologyManager???"+ontologyManager.getObjectProperties().size());
        }

        ModelLearningGraph modelLearningGraph = null;

        ModelLearner_KnownModels4 modelLearner;

        boolean useCorrectType = true;

        modelLearningGraph = (ModelLearningGraphCompact)ModelLearningGraph.getEmptyInstance(ontologyManager, ModelLearningGraphType.Compact);

        long start = System.currentTimeMillis();
        //??????integration graph?????????
        String graphName = graphPath + "IntegrationGraph_AllSMWithCorrectSTs" + Params.GRAPH_JSON_FILE_EXT;

        for (int i=0;i<semanticModels.size();i++) {
            if(i==26){
                continue;
            }
            modelLearningGraph.addModelAndUpdate(semanticModels.get(i), PatternWeightSystem.JWSPaperFormula);//??????????????????????????????????????????
            System.out.println("???????????????????????????modelLearningGraph???????????????"+modelLearningGraph.getGraphBuilder().getGraph().vertexSet().size());
            System.out.println("???????????????????????????modelLearningGraph????????????"+modelLearningGraph.getGraphBuilder().getGraph().edgeSet().size());
        }

        System.out.println("IntegrationGraph_AllSMWithCorrectSTs.edge.size:" + modelLearningGraph.getGraphBuilder().getGraph().edgeSet().size());
        System.out.println("IntegrationGraph_AllSMWithCorrectSTs.vertex.size:" + modelLearningGraph.getGraphBuilder().getGraph().vertexSet().size());
        return modelLearningGraph.getGraphBuilder().getGraph();
    }

    /**2022.5.29 ??????????????????????????????-?????????????????????integration graph(candidate semantic types)**/
    public static DirectedWeightedMultigraph<Node, DefaultLink> getIntegrationGraph_AllSMWithCandidateSTs() throws Exception{
        ServletContextParameterMap contextParameters = ContextParametersRegistry.getInstance().getDefault();

        //????????????integration graph?????????
        String graphPath = Params.GRAPHS_DIR;

        List<SemanticModel> trainingData = new ArrayList<SemanticModel>();//?????????training SemanticModel?????????

        //???????????????semantic models
        if(semanticModels == null) {
            semanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "models-json-SemanticLabeling-20220430", Params.MODEL_MAIN_FILE_EXT);
        }
        //??????ontology????????????
        if(ontologyManager == null) {
            ontologyManager = new OntologyManager(contextParameters.getId());
//            System.out.println("1.ontologyManager???"+ontologyManager.getObjectProperties().size());//////////////
//            File oFile = new File(Params.ROOT_DIR + "weapon.owl");
            File oFile = new File(Params.ROOT_DIR+"ecrm_update(20190521).owl");

            ontologyManager.doImport(oFile, "UTF-8");
            ontologyManager.updateCache();
            System.out.println("IntegrationGraph_AllSMWithCandidateSTs???ontologyManager???"+ontologyManager.getObjectProperties().size());
        }

        ModelLearningGraph modelLearningGraph = null;

        ModelLearner_KnownModels4 modelLearner;

        boolean useCorrectType = true;
        int numberOfCandidates = 4;


        modelLearningGraph = (ModelLearningGraphCompact)ModelLearningGraph.getEmptyInstance(ontologyManager, ModelLearningGraphType.Compact);


        /**Get the Steiner nodes (boxes) from the new source. 8 June 2018.
         ?????????????????????????????????????????????????????????????????????**/
        List<ColumnNode> columnNodes = new ArrayList<ColumnNode>();
        for(int i=0;i<semanticModels.size();i++){
//            if(i==0){
//                continue;
//            }
            columnNodes.addAll(semanticModels.get(i).getColumnNodes());

            modelLearningGraph.addModelAndUpdate(semanticModels.get(i), PatternWeightSystem.JWSPaperFormula);//??????????????????????????????????????????
            System.out.println("???????????????????????????modelLearningGraph???????????????"+modelLearningGraph.getGraphBuilder().getGraph().vertexSet().size());
            System.out.println("???????????????????????????modelLearningGraph????????????"+modelLearningGraph.getGraphBuilder().getGraph().edgeSet().size());
        }

        /**???????????????????????????????????????????????????Node???????????????**/
        Set<Node> steinerNodes = new HashSet<Node>(columnNodes);//get steiner node. very important. 19 Aug 2018
        System.out.println("IntegrationGraph_AllSMWithCandidateSTs???steinerNodes?????????" + steinerNodes.size());
//        System.out.println("IntegrationGraph_AllSMWithCandidateSTs???columnNodes?????????" + columnNodes.size());
//        System.out.println("IntegrationGraph_AllSMWithCandidateSTs???columnNodes???????????????????????????" + columnNodes.get(0).getColumnName());


        modelLearner = new ModelLearner_KnownModels4(ontologyManager, new ArrayList<Node>(steinerNodes));
        long start = System.currentTimeMillis();
        //??????integration graph?????????
        String graphName = graphPath + "IntegrationGraph_AllSMWithCandidateSTs" + Params.GRAPH_JSON_FILE_EXT;

        modelLearner = new ModelLearner_KnownModels4(modelLearningGraph.getGraphBuilder(), new ArrayList<Node>(steinerNodes));
        modelLearner.graphBuilder = modelLearningGraph.getGraphBuilder();
        modelLearner.nodeIdFactory = modelLearner.graphBuilder.getNodeIdFactory();

        //????????????????????????
        modelLearner.hypothesize2(useCorrectType, numberOfCandidates);////////5.29 ???hypothesize_correct_candidates_smtypes????????????
//        modelLearner.hypothesize_correct_candidates_smtypes(numberOfCandidates);//////5.29

        System.out.println("IntegrationGraph_AllSMWithCandidateSTs???edge.size:"+modelLearner.graphBuilder.getGraph().edgeSet().size());
        System.out.println("IntegrationGraph_AllSMWithCandidateSTs???vertex.size:"+modelLearner.graphBuilder.getGraph().vertexSet().size());

        /**??????json??????**/
        GraphUtil.exportJson(modelLearner.graphBuilder.getGraph(), graphName + ".json",true,true);
        return modelLearner.graphBuilder.getGraph();
    }

    /**2022.5.29 ????????????????????????????????????????????????????????????????????????**/
    public static SemanticModel getSMWithoutSteinerNodes(SemanticModel sm) throws IOException {
        System.out.println("??????sm.edge.size:" + sm.getGraph().edgeSet().size());
        System.out.println("??????sm.vertex.size:" + sm.getGraph().vertexSet().size());
        List<ColumnNode> SteinerNodes = new ArrayList<ColumnNode>();
        SteinerNodes=sm.getColumnNodes();
        System.out.println("SteinerNodes.size???" + SteinerNodes.size());
        //?????????????????????????????????????????????link
        for(ColumnNode node:SteinerNodes) {
            sm.getGraph().removeVertex(node);
            for (LabeledLink link : sm.getGraph().edgeSet()) {
                if (link.getTarget().equals(node)){
                    sm.getGraph().removeEdge(link);
                }
            }

        }
        System.out.println("???????????????sm.edge.size:" + sm.getGraph().edgeSet().size());
        System.out.println("???????????????sm.vertex.size:" + sm.getGraph().vertexSet().size());
        GraphVizUtil.exportSemanticModelToGraphviz(sm, GraphVizLabelType.LocalId,
                GraphVizLabelType.LocalUri, false, false, "E:\\D_Drive\\ASM\\DataSets\\museum-29-crm\\" + "getSMWithoutSteinerNodes" + ".graph.json" + ".dot");
        return sm;
    }

    /**5.29 ???????????????txt????????? ??????????????????**/
    public static void saveArray(String[][] array,String filename){
        //1.?????????????????????
        FileWriter writeFile = null;
        try {
            //2.?????????????????????????????????
            File file = new File(filename);
            //3.????????????????????????????????????
            if(!file.exists()) {
                file.createNewFile();
            }
            //4.??????????????????????????????
            writeFile = new FileWriter(file);
            //5.???????????????????????????txt?????????
            for(int i = 0; i < array.length; i++) {
                //6.?????????n - 1???????????????","
                for(int j = 0; j < array[0].length - 1; j++) {
                    writeFile.write(array[i][j] + "\t");
                }
                //7.??????????????????????????????","
                writeFile.write(array[i][array[0].length - 1] + "");
                //8.???????????????
                writeFile.write("\n");
            }
            //9.???writeFile??????????????????????????????????????????????????????
            writeFile.flush();
        } catch (Exception e) {//10.????????????
            e.printStackTrace();
        } finally {
            try {
                //11.??????writeFile???????????????????????????
                if(writeFile != null)
                    writeFile.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }
    /**6.9 ???????????????txt?????? ???????????????**/
    public static void saveArray_Space(String[][] array,String filename){
        //1.?????????????????????
        FileWriter writeFile = null;
        try {
            //2.?????????????????????????????????
            File file = new File(filename);
            //3.????????????????????????????????????
            if(!file.exists()) {
                file.createNewFile();
            }
            //4.??????????????????????????????
            writeFile = new FileWriter(file);
            //5.???????????????????????????txt?????????
            for(int i = 0; i < array.length; i++) {
                //6.?????????n - 1???????????????","
                for(int j = 0; j < array[0].length - 1; j++) {
                    writeFile.write(array[i][j] + " ");
                }
                //7.??????????????????????????????","
                writeFile.write(array[i][array[0].length - 1] + "");
                //8.???????????????
                writeFile.write("\n");
            }
            //9.???writeFile??????????????????????????????????????????????????????
            writeFile.flush();
        } catch (Exception e) {//10.????????????
            e.printStackTrace();
        } finally {
            try {
                //11.??????writeFile???????????????????????????
                if(writeFile != null)
                    writeFile.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }
    /**6.9 ??????????????????train.txt??????**/
    public static String[][] SaveGatneTriplesToTXT(DirectedWeightedMultigraph<Node, DefaultLink> integrationgraph){
        String train_triples[][] = new String[9296][3];//????????????????????????????????????????????????????????????
        String positive_train_triples[][] = new String[9296][4];

        int i = 0;
        for(DefaultLink link: integrationgraph.edgeSet()){
//            System.out.println("integrationgraph.link.source:" + link.getSource().getId());
//            System.out.println("integrationgraph.link.uri:" + link.getUri());
//            System.out.println("integrationgraph.link.target:" + link.getTarget().getId());
//            System.out.println("???????????????");
            train_triples[i][0] = link.getUri();
            train_triples[i][1] = link.getSource().getId();
            train_triples[i][2] = link.getTarget().getId();

            positive_train_triples[i][0] = link.getUri();
            positive_train_triples[i][1] = link.getSource().getId();
            positive_train_triples[i][2] = link.getTarget().getId();
            positive_train_triples[i][3] = "1";

            ++i;
        }

        saveArray_Space(train_triples,"gatne_train_triples_candidate_29.txt");//gatne_train_triples[9244][3];gatne_train_triples_correct_29[8556][3]
        saveArray_Space(positive_train_triples,"gatne_positive_triples_candidate_29.txt");//gatne_positive_triples[9244][4];gatne_positive_triples_correct_29[8556][3]
        return train_triples;
    }
    /**5.30 ??????????????????Triples.txt??????**/
    public static String[][] SaveTriplesToTXT(DirectedWeightedMultigraph<Node, DefaultLink> integrationgraph) throws Exception {
        /**??????integration graph ????????????????????????txt?????????**/
//        DirectedWeightedMultigraph<Node, DefaultLink> integrationgraph = null;
//        integrationgraph = getIntegrationGraph_AllSMWithCandidateSTs();
        System.out.println("integrationgraph.edge.size:" + integrationgraph.edgeSet().size());
        System.out.println("integrationgraph.vertex.size:" + integrationgraph.vertexSet().size());
        String Triples[][] = new String[9244][3];//????????????????????????????????????????????????????????????
        Set<String> Node_Type = new HashSet<String>();//??????integration graph???node?????????
        Set<String> Link_Type = new HashSet<String>();//??????link???uri,??????integration graph??????link??????

        int i = 0;
        for(DefaultLink link: integrationgraph.edgeSet()){
            System.out.println("integrationgraph.link.source:" + link.getSource().getId());
            System.out.println("integrationgraph.link.uri:" + link.getUri());
            System.out.println("integrationgraph.link.target:" + link.getTarget().getId());
            //????????????source node type
            if(!(Node_Type.contains(link.getSource().getUri()))){
                Node_Type.add(link.getSource().getUri());
            }
            //????????????target node type
            if(!(Node_Type.contains(link.getTarget().getUri()))){
                Node_Type.add(link.getTarget().getUri());
            }
            //????????????link type
            if(!(Link_Type.contains(link.getUri()))){
                Link_Type.add(link.getUri());
            }

            System.out.println("???????????????");
            Triples[i][0] = link.getSource().getId();
            Triples[i][1] = link.getUri();
            Triples[i][2] = link.getTarget().getId();
            ++i;
//            break;
        }

        for (int j = 0; j < Triples.length; j++) {
            System.out.println("????????????Triple???????????????");
            for (int k = 0; k < Triples[j].length; k++) {
                System.out.println(Triples[j][k]);
            }
        }
        //??????node types???link types??????
        System.out.println("node-types-size:" + Node_Type.size());
        System.out.println("link-types-size:" + Link_Type.size());
        /**??????integration graph ????????????????????????txt?????????**/

        /**??????????????????????????????columnnode.type**/
//        System.out.println("semanticModels.size:"+semanticModels.size());
//        Set<ColumnNode> columnnode_type = new HashSet<ColumnNode>();
//        List<ColumnNode> columnnode_size = new ArrayList<ColumnNode>();
//        int repeat_index=0;
//        for(int j=0;j<semanticModels.size();j++){
//            if(j==26){
//                continue;
//            }
//            for(ColumnNode node: semanticModels.get(j).getColumnNodes()){
//                if(!(columnnode_type.contains(node))){
//                    columnnode_type.add(node);
//                }
//                else{
//                    repeat_index++;
//                }
//                columnnode_size.add(node);
//            }
//        }
//        System.out.println("columnnode_type.size:"+columnnode_type.size());
//        System.out.println("repeat_index:"+repeat_index);
//        System.out.println("columnnode_size:"+columnnode_size.size());
        /**??????????????????????????????columnnode.type**/

        /**??????writer????????????**/
//        String myArray[][] = {{"JavaFX", "HBase", "OpenCV"},{"Java", "Hadoop", "Neo4j"}};
//
//        BufferedWriter writer = new BufferedWriter(new FileWriter("myFile.txt", false));
//
//        for(int i = 0; i<myArray.length;i++) {
//            for(int j=0;j<myArray[i].length;j++) {
//                writer.write(myArray[i][j].toString());
//                if(j!=myArray[i].length-1){
//                    writer.write(",");
//                }
//            }
//            writer.newLine();
//        }
//        writer.flush();
//        System.out.println("Data Entered in to the file successfully");
        /**??????writer????????????**/

        /**??????FileWriter????????????**/
//        String array[][] = {{"JavaFX", "HBase", "OpenCV"},{"Java", "Hadoop", "Neo4j"},{"Hadoop", "Neo4j","OpenCV"}};
        saveArray(Triples,"Triples.txt");
        /**??????FileWriter????????????**/
        return Triples;
    }
    /**5.30 ?????????????????????NodeType.txt??????**/
    public static  String[][] SaveNodeTypesToTXT(DirectedWeightedMultigraph<Node, DefaultLink> integrationgraph) throws Exception {
        /**??????integration graph ????????????????????????txt?????????**/
//        DirectedWeightedMultigraph<Node, DefaultLink> integrationgraph = null;
//        integrationgraph = getIntegrationGraph_AllSMWithCandidateSTs();
        System.out.println("integrationgraph.edge.size:" + integrationgraph.edgeSet().size());
        System.out.println("integrationgraph.vertex.size:" + integrationgraph.vertexSet().size());
        String NodeType[][] = new String[491][1];//????????????????????????????????????????????????????????????
        Set<String> Node_Type = new HashSet<String>();//??????integration graph???node?????????
        Set<String> Node_Type_Id = new HashSet<String>();//??????node.id??????node type???
        String SpecialNodeType[][] = new String[38][2];//???????????????http???HN?????????node type
        String NodeType2TXT[][] = new String[491][2];
        Map<String,String> NodeType_TXT = new HashMap<String,String>();//??????nodetype???id???txt
        Map<String,String> SpecialNodeTypeId_URI = new HashMap<String,String>();

        int i = 0;
        int k = 0;
        int m = 0;
        for(DefaultLink link: integrationgraph.edgeSet()){
//            System.out.println("integrationgraph.link.source:" + link.getSource().getId());
//            System.out.println("integrationgraph.link.target:" + link.getTarget().getId());

            if(!(Node_Type_Id.contains(link.getSource().getId()))){
                Node_Type_Id.add(link.getSource().getId());
                if(link.getSource().getId().startsWith("http")) {//??????http????????????node
                    NodeType_TXT.put(link.getSource().getId(), link.getSource().getId());
                }
                if(!(link.getSource().getId().startsWith("http"))){//?????????http????????????node
                    NodeType_TXT.put(link.getSource().getId(), ((ColumnNode) link.getSource()).getColumnName());
                }
                if(!(link.getSource().getId().startsWith("http")||link.getSource().getId().startsWith("HN"))){
                    SpecialNodeTypeId_URI.put(link.getSource().getId(), ((ColumnNode) link.getSource()).getColumnName());
                    System.out.println("??????SpecialNodeType???uri:" + ((ColumnNode) link.getSource()).getColumnName());
                }
            }
            if(!(Node_Type_Id.contains(link.getTarget().getId()))){
                Node_Type_Id.add(link.getTarget().getId());
                if(link.getTarget().getId().startsWith("http")) {//??????http????????????node
                    NodeType_TXT.put(link.getTarget().getId(), link.getTarget().getId());
                }
                if(!(link.getTarget().getId().startsWith("http"))){//?????????http????????????node
                    NodeType_TXT.put(link.getTarget().getId(), ((ColumnNode) link.getTarget()).getColumnName());
                }
                if(!(link.getTarget().getId().startsWith("http")||link.getTarget().getId().startsWith("HN"))){
                    SpecialNodeTypeId_URI.put(link.getTarget().getId(),((ColumnNode) link.getTarget()).getColumnName());
                    System.out.println("??????SpecialNodeType???uri:" + ((ColumnNode) link.getTarget()).getColumnName());
                }
            }

//            //????????????source node type
//            //?????????????????????????????????http??????HN??????
//            if((link.getSource().getId().startsWith("http")||link.getSource().getId().startsWith("HN"))&&
//                    (!(Node_Type.contains(link.getSource().getId())))){
//                Node_Type.add(link.getSource().getId());
//            }
//            else if(!(link.getSource().getId().startsWith("http")||link.getSource().getId().startsWith("HN"))&&
//                    (!(Node_Type.contains(link.getSource().getUri())))){
//                Node_Type.add(link.getSource().getUri());
//            }
//            //????????????target node type
//            if((link.getTarget().getId().startsWith("http")||link.getTarget().getId().startsWith("HN"))&&
//                    (!(Node_Type.contains(link.getTarget().getId())))){
//                Node_Type.add(link.getTarget().getId());
//            }
//            else if(!(link.getTarget().getId().startsWith("http")||link.getTarget().getId().startsWith("HN"))&&
//                    (!(Node_Type.contains(link.getTarget().getUri())))){
//                Node_Type.add(link.getTarget().getUri());
//            }
        }
        System.out.println("??????Node_Type_Id.size:" + Node_Type_Id.size());

        System.out.println("???????????????");
        for(String nodetype: Node_Type_Id){
            NodeType[i][0] = nodetype;
            ++i;
        }

        for(String nodetype2txt: NodeType_TXT.keySet()){
            NodeType2TXT[m][0] = nodetype2txt;
            NodeType2TXT[m][1] = NodeType_TXT.get(nodetype2txt);
            ++m;
        }

        for(String specialnodetype: SpecialNodeTypeId_URI.keySet()){
            SpecialNodeType[k][0] = specialnodetype;
            SpecialNodeType[k][1] = SpecialNodeTypeId_URI.get(specialnodetype);
            ++k;
        }

        for (int j = 0; j < NodeType.length; j++) {
            System.out.println("????????????Triple???????????????");
            System.out.println(NodeType[j][0]);
        }
//        //??????node types??????
//        System.out.println("node-types-size:" + Node_Type.size());
        /**??????integration graph ????????????????????????txt?????????**/

        /**??????????????????????????????columnnode.type**/
//        System.out.println("semanticModels.size:"+semanticModels.size());
//        Set<ColumnNode> columnnode_type = new HashSet<ColumnNode>();
//        List<ColumnNode> columnnode_size = new ArrayList<ColumnNode>();
//        int repeat_index=0;
//        for(int j=0;j<semanticModels.size();j++){
//            if(j==26){
//                continue;
//            }
//            for(ColumnNode node: semanticModels.get(j).getColumnNodes()){
//                if(!(columnnode_type.contains(node))){
//                    columnnode_type.add(node);
//                }
//                else{
//                    repeat_index++;
//                }
//                columnnode_size.add(node);
//            }
//        }
//        System.out.println("columnnode_type.size:"+columnnode_type.size());
//        System.out.println("repeat_index:"+repeat_index);
//        System.out.println("columnnode_size:"+columnnode_size.size());
        /**??????????????????????????????columnnode.type**/


        /**??????FileWriter????????????**/
//        String array[][] = {{"JavaFX", "HBase", "OpenCV"},{"Java", "Hadoop", "Neo4j"},{"Hadoop", "Neo4j","OpenCV"}};
        saveArray(NodeType,"NodeType.txt");
        saveArray(SpecialNodeType,"SpecialNodeType.txt");
        saveArray(NodeType2TXT,"NodeType2TXT.txt");
        /**??????FileWriter????????????**/
        return NodeType2TXT;
    }
    /**5.30 ?????????????????????LinkType.txt??????**/
    public static String[][] SaveLinkTypesToTXT(DirectedWeightedMultigraph<Node, DefaultLink> integrationgraph) throws Exception {
        /**??????integration graph ????????????????????????txt?????????**/
//        DirectedWeightedMultigraph<Node, DefaultLink> integrationgraph = null;
//        integrationgraph = getIntegrationGraph_AllSMWithCandidateSTs();
        System.out.println("integrationgraph.edge.size:" + integrationgraph.edgeSet().size());
        System.out.println("integrationgraph.vertex.size:" + integrationgraph.vertexSet().size());
        String LinkType[][] = new String[33][1];//????????????????????????????????????????????????????????????
        Set<String> Link_Type = new HashSet<String>();//??????link???uri,??????integration graph??????link??????

        int i = 0;
        for(DefaultLink link: integrationgraph.edgeSet()){
//            System.out.println("integrationgraph.link.uri:" + link.getUri());
            //????????????link type
            if(!(Link_Type.contains(link.getUri()))){
                Link_Type.add(link.getUri());
                System.out.println("???????????????");
                LinkType[i][0] = link.getUri();
                ++i;
            }
        }


        for (int j = 0; j < LinkType.length; j++) {
            System.out.println("????????????Triple???????????????");
            System.out.println(LinkType[j][0]);
        }
        //??????link types??????
        System.out.println("link-types-size:" + Link_Type.size());
        /**??????integration graph ????????????????????????txt?????????**/

        /**??????????????????????????????columnnode.type**/
//        System.out.println("semanticModels.size:"+semanticModels.size());
//        Set<ColumnNode> columnnode_type = new HashSet<ColumnNode>();
//        List<ColumnNode> columnnode_size = new ArrayList<ColumnNode>();
//        int repeat_index=0;
//        for(int j=0;j<semanticModels.size();j++){
//            if(j==26){
//                continue;
//            }
//            for(ColumnNode node: semanticModels.get(j).getColumnNodes()){
//                if(!(columnnode_type.contains(node))){
//                    columnnode_type.add(node);
//                }
//                else{
//                    repeat_index++;
//                }
//                columnnode_size.add(node);
//            }
//        }
//        System.out.println("columnnode_type.size:"+columnnode_type.size());
//        System.out.println("repeat_index:"+repeat_index);
//        System.out.println("columnnode_size:"+columnnode_size.size());
        /**??????????????????????????????columnnode.type**/

        /**??????writer????????????**/
//        String myArray[][] = {{"JavaFX", "HBase", "OpenCV"},{"Java", "Hadoop", "Neo4j"}};
//
//        BufferedWriter writer = new BufferedWriter(new FileWriter("myFile.txt", false));
//
//        for(int i = 0; i<myArray.length;i++) {
//            for(int j=0;j<myArray[i].length;j++) {
//                writer.write(myArray[i][j].toString());
//                if(j!=myArray[i].length-1){
//                    writer.write(",");
//                }
//            }
//            writer.newLine();
//        }
//        writer.flush();
//        System.out.println("Data Entered in to the file successfully");
        /**??????writer????????????**/

        /**??????FileWriter????????????**/
//        String array[][] = {{"JavaFX", "HBase", "OpenCV"},{"Java", "Hadoop", "Neo4j"},{"Hadoop", "Neo4j","OpenCV"}};
        saveArray(LinkType,"LinkType.txt");
        /**??????FileWriter????????????**/
        return LinkType;
    }
    /**5.31 ????????????????????????????????????????????????LinkTypeRemoveStr.txt??????**/
    public static String[][] SaveLinkTypesRemoveStrToTXT(DirectedWeightedMultigraph<Node, DefaultLink> integrationgraph) throws Exception {
        String LinkType[][];
        String LinkTypeRemoveStr[] = {"http://erlangen-crm.org/current/","http://isi.edu/integration/karma/dev#","http://www.w3.org/2000/01/rdf-schema#"};
        String LinkTypeRemove[][] = new String[33][1];//??????????????????nodetype
        LinkType = SaveLinkTypesToTXT(integrationgraph);//??????linktype???txt??????

        for(int i=0;i<LinkType.length;i++){
            System.out.println("??????LinkType:");
            System.out.println(LinkType[i][0]);
            for(int j=0;j<LinkTypeRemoveStr.length;j++){
                if(LinkType[i][0].startsWith(LinkTypeRemoveStr[j])){
                    System.out.println("??????????????????LinkeTypeRemoveStr:"+LinkTypeRemoveStr[j]);
                    System.out.println("?????????????????????????????????LinkType:"+LinkType[i][0].replace(LinkTypeRemoveStr[j], ""));
                    LinkTypeRemove[i][0]=LinkType[i][0].replace(LinkTypeRemoveStr[j], "");
                    break;
                }
            }
        }

        saveArray(LinkTypeRemove,"LinkTypeRemoveStr.txt");
        /**??????FileWriter????????????**/
        return LinkTypeRemove;
    }
    /**5.31 ????????????????????????????????????????????????NodeTypeRemoveStr.txt??????**/
    public static String[][] SaveNodeTypesRemoveStrToTXT(DirectedWeightedMultigraph<Node, DefaultLink> integrationgraph) throws Exception {
        String NodeType2TXT[][];
        String NodeTypeRemoveStr[] = {"http://erlangen-crm.org/current/","http://www.w3.org/2002/07/owl#"};
        String NodeTypeRemove[][] = new String[491][2];//??????????????????nodetype
        String NodeType_One_Remove[][] = new String[491][1];
        NodeType2TXT = SaveNodeTypesToTXT(integrationgraph);//??????linktype???txt??????


        for(int i=0;i<NodeType2TXT.length;i++){
//            System.out.println("??????NodeType2TXT:");
//            System.out.println(NodeType2TXT[i][0]);
            for(int j=0;j<NodeTypeRemoveStr.length;j++){
                if(NodeType2TXT[i][0].startsWith(NodeTypeRemoveStr[j])){
                    System.out.println("??????????????????NodeTypeRemoveStr:"+NodeTypeRemoveStr[j]);
                    System.out.println("?????????????????????????????????LinkType:"+NodeType2TXT[i][0].replace(NodeTypeRemoveStr[j], ""));
                    NodeTypeRemove[i][0]=NodeType2TXT[i][0].replace(NodeTypeRemoveStr[j], "");
                    NodeTypeRemove[i][1]=NodeType2TXT[i][1].replace(NodeTypeRemoveStr[j], "");
                    NodeType_One_Remove[i][0]=NodeType2TXT[i][0].replace(NodeTypeRemoveStr[j], "");
                    break;
                }
                else{
                    NodeTypeRemove[i][0]=NodeType2TXT[i][0];
                    NodeTypeRemove[i][1]=NodeType2TXT[i][1];
                    NodeType_One_Remove[i][0]=NodeType2TXT[i][0];
                }
            }
        }

        saveArray(NodeTypeRemove,"NodeTypeRemoveStr.txt");
        saveArray(NodeType_One_Remove,"NodeType_One_RemoveStr.txt");
        /**??????FileWriter????????????**/
        return NodeTypeRemove;
    }
    /**6.8 ?????????????????????????????????????????????TriplesRemoveStr.txt**/
    public static String[][] SaveTriplesRemoveStrToTXT(DirectedWeightedMultigraph<Node, DefaultLink> integrationgraph) throws Exception {
        String Triples[][];
        String TriplesNodeRemoveStr[] = {"http://erlangen-crm.org/current/","http://www.w3.org/2002/07/owl#"};
        String TriplesLinkRemoveStr[] = {"http://erlangen-crm.org/current/","http://isi.edu/integration/karma/dev#","http://www.w3.org/2000/01/rdf-schema#"};
        String TriplesRemove[][] = new String[9244][3];//??????????????????nodetype
        Triples = SaveTriplesToTXT(integrationgraph);//??????linktype???txt??????


        for(int i=0;i<Triples.length;i++){
//            System.out.println("??????NodeType2TXT:");
//            System.out.println(NodeType2TXT[i][0]);
            /**??????node**/
            for(int j=0;j<TriplesNodeRemoveStr.length;j++){
                //??????head node
                if(Triples[i][0].startsWith(TriplesNodeRemoveStr[j])){
                    System.out.println("??????????????????NodeTypeRemoveStr:"+TriplesNodeRemoveStr[j]);
                    System.out.println("?????????????????????????????????LinkType:"+Triples[i][0].replace(TriplesNodeRemoveStr[j], ""));
                    TriplesRemove[i][0]=Triples[i][0].replace(TriplesNodeRemoveStr[j], "");
//                    NodeTypeRemove[i][1]=NodeType2TXT[i][1].replace(NodeTypeRemoveStr[j], "");
                    break;
                }
                else{
                    TriplesRemove[i][0]=Triples[i][0];
//                    NodeTypeRemove[i][1]=NodeType2TXT[i][1];
                }
            }

            for(int j=0;j<TriplesNodeRemoveStr.length;j++){
                //??????tail node
                if(Triples[i][2].startsWith(TriplesNodeRemoveStr[j])){
                    System.out.println("??????????????????NodeTypeRemoveStr:"+TriplesNodeRemoveStr[j]);
                    System.out.println("?????????????????????????????????LinkType:"+Triples[i][2].replace(TriplesNodeRemoveStr[j], ""));
                    TriplesRemove[i][2]=Triples[i][2].replace(TriplesNodeRemoveStr[j], "");
//                    NodeTypeRemove[i][1]=NodeType2TXT[i][1].replace(NodeTypeRemoveStr[j], "");
                    break;
                }
                else{
                    TriplesRemove[i][2]=Triples[i][2];
//                    NodeTypeRemove[i][1]=NodeType2TXT[i][1];
                }
            }
            /**??????node**/

            /**??????relation**/
            for(int j=0;j<TriplesLinkRemoveStr.length;j++){
                if(Triples[i][1].startsWith(TriplesLinkRemoveStr[j])){
                    System.out.println("??????????????????LinkeTypeRemoveStr:"+TriplesLinkRemoveStr[j]);
                    System.out.println("?????????????????????????????????LinkType:"+Triples[i][1].replace(TriplesLinkRemoveStr[j], ""));
                    TriplesRemove[i][1]=Triples[i][1].replace(TriplesLinkRemoveStr[j], "");
                    break;
                }
            }
            /**??????relation**/

        }

        saveArray(TriplesRemove,"TriplesRemoveStr.txt");
        /**??????FileWriter????????????**/
        return TriplesRemove;
    }

    public static List<Integer> randomIndex(int min, int max){
        int len = max-min+1;
        if(max < min){
            return null;
        }
        //???????????????????????????????????????
        List<Integer> result = new ArrayList<>();
        for (int i = min; i < min+len; i++){
            result.add(i);
        }
        Collections.shuffle(result);
        return result;
    }

    public static <K extends Comparable,V extends Comparable> Map<K, V> sortMapByValues(Map<K, V> map){
        Map<K, V> result = new LinkedHashMap<K, V>();
        //??????map?????????Entry<K,V>???????????????????????????????????????????????????????????????
        List<Map.Entry<K, V>> list = map.entrySet()
                .stream()
                .sorted((p1,p2)->p1.getValue().compareTo(p2.getValue()))
                .collect(Collectors.toList());
        //???????????????????????????????????????Entry<K,V>????????????map?????????
        //??????HashMap???????????????????????????????????????map??????HashMap???????????????????????????????????????????????????
        //????????????map??????LinkedHashMap??????????????????????????????LinkedHashMap????????????????????????
        list.forEach(ele->result.put(ele.getKey(), ele.getValue()));
        return result;
    }

    public static int[] LOO(int i){
        ArrayList<Integer> list = new ArrayList<>();


        for (int j = 0; j < 15; j++) {
            list.add(j);
        }

        list.remove(i);
        int[] arr = new int[14];
        for (int j = 0; j < 14; j++) {
            arr[j] = list.get(j);
        }

        return arr;
    }

    public static Integer[] randomTrainIndex(int testIndex, int numbersOfKnownModels, int seed){
        PythonInterpreter interpreter = new PythonInterpreter();
        interpreter.execfile("C:\\D_Drive\\ASM\\DataMatchingMaster\\randomTrainIndex.py");
        PyFunction pyFunction = interpreter.get("randomTrainIndex", PyFunction.class);
        PyList pyList = (PyList) pyFunction.__call__(new PyInteger(testIndex), new PyInteger(numbersOfKnownModels), new PyInteger(seed));
        pyList.sort();
        Integer[] arr = new Integer[numbersOfKnownModels];
        for (int j = 0; j < numbersOfKnownModels; j++) {
            arr[j] = (int) pyList.get(j);
        }
        return arr;
    }

    /**just for test . 14 Aug 2018.**/
    public static void main(String[] args) throws Exception {

        semanticModels = null;
        ontologyManager = null;

        getCandidateSemanticModels(24, new Integer[]{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,25,26,27,28});

        /**Reasoning-Evaluation-test**/
//        Map<String,String> map1 = new HashMap<String,String>();
//        map1.put("b","1");
//        map1.put("a","2");
//        map1.put("c","3");
//        System.out.println("??????map1:" + map1);
//        Set<String> set1 = new HashSet<String>(map1.keySet());
//        System.out.println("??????set1:" + set1);
//        List<String> list1 = new LinkedList<String>(set1);
//        System.out.println("??????list1:" + list1);
//
//        List<Integer> list2 = new LinkedList<Integer>();
//        for(int i=1 ;i<=3;i++){
//            list2.add(i);
//        }
//        System.out.println("??????list2:" + list2);
//        /**???position????????????????????????**/
//        List<List<Integer>> result = new ArrayList<List<Integer>>();
//        int allCombinationNum = 1 << list2.size();
//        for (int i = 0; i < allCombinationNum; i++) {
//            LinkedList<Integer> resultChildList = new LinkedList<>();
//            for (int j = 0; j < list2.size(); j++) {
//                if ((i & (1 << j)) != 0) {
//                    resultChildList.add(list2.get(j));
//                }
//            }
//            if(resultChildList.size()>0) {
//                result.add(resultChildList);
//            }
//        }
//        System.out.println("??????result:" + result);
//        /**???position????????????????????????**/
        /**Reasoning-Evaluation-test**/

        /**test**/
//        EvaluateSemanticModel(0);
//        getIntegrationGraph_AllSMWithCorrectSTs();
//        SaveTriplesToTXT();//??????triples???txt??????
//        SaveNodeTypesToTXT();//??????nodetype???txt??????
        /**test**/

    }
}