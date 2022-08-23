package edu.isi.karma.research.modeling;

import java.io.*;

import com.google.gson.stream.JsonReader;
import com.google.gson.stream.JsonToken;

import edu.isi.karma.config.ModelingConfiguration;
import edu.isi.karma.config.ModelingConfigurationRegistry;
import edu.isi.karma.modeling.alignment.*;
import edu.isi.karma.modeling.alignment.learner.*;
import edu.isi.karma.modeling.ontology.OntologyManager;
import edu.isi.karma.modeling.research.Params;
import edu.isi.karma.rep.alignment.*;
import edu.isi.karma.rep.alignment.SemanticType.Origin;
import edu.isi.karma.util.RandomGUID;
import edu.isi.karma.webserver.ContextParametersRegistry;
import edu.isi.karma.webserver.ServletContextParameterMap;
import jdk.internal.org.objectweb.asm.tree.ClassNode;
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

import java.text.DecimalFormat;
import java.util.*;

public class IntegrationReader {
    private static Logger logger = LoggerFactory.getLogger(IntegrationReader.class);
    private static List<SemanticModel> semanticModels = null;
    private static DirectedWeightedMultigraph<Node, DefaultLink> graph =null;
    private GraphBuilder graphBuilder = null;
    public static  void main(String[] args) throws Exception {
        File file = new File("E:/D_Drive/ASM/DataSets/museum-29-crm/alignment-graph/s01-cb.csv.graph.json.json");
        InputStream iStream = new FileInputStream(file);
        InputStreamReader in = new InputStreamReader(iStream);
        JsonReader reader = new JsonReader(in);

        if(graph==null){
//            graph=GraphUtil.readGraph();
            graph = GraphUtil.readGraph(reader);
        }
//        System.out.println("(#attributes:" + newSource.getColumnNodes().size() + ")");
        for (Node node : graph.vertexSet()) {
            if(node instanceof ColumnNode){
                System.out.println(((ColumnNode) node).getColumnName());
            }
//            System.out.println(node);
        }



//        System.out.println(graph.getClass());

//        if (semanticModels == null) {
//            semanticModels = ModelReader.importSemanticModelsFromJsonFiles(Params.ROOT_DIR + "alignment-graph", Params.MODEL_MAIN_FILE_EXT);
//        }

//        System.out.println(semanticModels.size());

//        SemanticModel newSource = semanticModels.get(0);

//        logger.info("======================================================");
//        logger.info(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");//获取新源的数据节点
//        System.out.println(newSource.getName() + "(#attributes:" + newSource.getColumnNodes().size() + ")");
//        logger.info("======================================================");
//        List<ColumnNode> columnNodes = newSource.getColumnNodes();
//        for(ColumnNode i: columnNodes){
//            System.out.println(i.getColumnName());
//        }

    }
}
