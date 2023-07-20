package edu.isi.karma.research.modeling;

import edu.isi.karma.modeling.alignment.GraphUtil;
import edu.isi.karma.modeling.alignment.GraphVizUtil;
import edu.isi.karma.modeling.alignment.SemanticModel;
import edu.isi.karma.modeling.alignment.learner.ModelReader;
import edu.isi.karma.modeling.research.Params;
import edu.isi.karma.rep.alignment.ColumnNode;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class GetAttributeCombinationFromSemanticModel {

    public static void getAttributeCombinationFromSemanticModel(String dataSource) throws IOException {
        File files = new File("D:/ASM/CRM/positive-models/sub-same-positive-models-json-all/"+dataSource);
        System.out.println("filePath:" + files.getPath());
        File[] subFilePath = files.listFiles();
        System.out.println("subFilePath.size:" + subFilePath.length);
        for(File subFile: subFilePath){
            File firstFileForOneSubFile = subFile.listFiles()[0];
            System.out.println("firstFileForOneSubFile.path:" + firstFileForOneSubFile.getPath());
            SemanticModel sm = ModelReader.importSemanticModelFromJsonFile(firstFileForOneSubFile.getPath(), Params.MODEL_MAIN_FILE_EXT);
            List<String> columnsName = new ArrayList<String>();
            for(ColumnNode columnNode: sm.getColumnNodes()){
                columnsName.add(columnNode.getColumnName());
            }
            System.out.println("attribute combination:" + columnsName);
        }
    }
    public static void main(String[] args) throws IOException {
        System.out.println("run GetAttributeCombinationSemanticModel success");
        String dataSource = "s01";
        getAttributeCombinationFromSemanticModel(dataSource);
    }
}
