package edu.isi.karma.research.modeling;
import edu.isi.karma.modeling.alignment.SemanticModel;
import edu.isi.karma.modeling.alignment.learner.ModelReader;
import edu.isi.karma.modeling.research.Params;
import edu.isi.karma.rep.alignment.ColumnNode;
import edu.isi.karma.rep.alignment.SubClassLink;
import org.hsqldb.Column;
import org.python.antlr.op.Param;
import org.python.antlr.op.Sub;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.*;

import static edu.isi.karma.research.modeling.EliminateNodes.NewEliminatedSemanticModelsForSubSM;
import static edu.isi.karma.research.modeling.EliminateNodes.getSubSemanticModels;
import static edu.isi.karma.research.modeling.SearchForSemanticModels.CreateFile;

public class GenerateSamples {
    private static List<SemanticModel> SemanticModels = null;
    private static SemanticModel SemanticModel = null;

    public static void subList(List<String> list, int start, List<String> item, List<List<String>> SubSets) {
        for (int i = start; i < list.size(); i++) {
            item.add(list.get(i));
            SubSets.add(new ArrayList<String>(item));
            subList(list, i + 1, item, SubSets);
            item.remove(item.size() - 1);
        }
    }

    public static List<List<String>> getSubSets(List<String> Columns) {
        List<List<String>> subSets = new ArrayList<List<String>>();
        if (Columns.size() == 0 || Columns == null) {
            return subSets;
        }
//        Arrays.sort(Columns.toArray()); //sort

        List<String> item = new ArrayList<String>();
        subList(Columns, 0, item, subSets);

//        SubSets.add(new ArrayList<String>()); //add empty list

        return subSets;
    }

//    public static List<List<String>> getSubSetsContainsOneElement(List<String> Columns) {
//        List<List<String>> subSets = new ArrayList<List<String>>();
//        if (Columns.size() == 0 || Columns == null) {
//            return subSets;
//        }
////        Arrays.sort(Columns.toArray()); //sort
//
//        List<String> item = new ArrayList<String>();
//        subList(Columns, 0, item, subSets);
//
////        SubSets.add(new ArrayList<String>()); //add empty list
//
//        System.out.println("subSet.size before:" + subSets.size());
//
//        //add subSet with only one column
//        for(String columnName: Columns){
//            List<String> subSet = new ArrayList<String>(Arrays.asList(columnName));
//            subSets.add(subSet);
//        }
//        System.out.println("subSet.size after:" + subSets.size());
//
//        return subSets;
//    }

    public static List<List<String>> getCombinedSubSets(List<List<String>> unique_SubSets, List<List<String>> added_SubSets){
        List<List<String>> combinedSubSets = new LinkedList<List<String>>();
        List<String> temp_combined_subset = new ArrayList<String>();

        for(List<String> unique_subset: unique_SubSets){
            if(unique_subset.size() > 1){
                combinedSubSets.add(unique_subset);
            }
            for(List<String> added_subset: added_SubSets){
                temp_combined_subset = new ArrayList<>(unique_subset);
                temp_combined_subset.addAll(added_subset);
                combinedSubSets.add(temp_combined_subset);
            }
        }

        return combinedSubSets;
    }

    public static Integer getNumOfSpecificColumn(List<List<String>> subSets, String columnName){
        int num = 0;
        for(List<String> subset: subSets){
            if(subset.contains(columnName)){
                num++;
            }
        }
        return num;
    }

    public static List<String> str2List(String str, String splitStr, List<String> replacePattern){
        String singleStr = null;
        List<String> strList = new ArrayList<String>();

        if(str.length()>2) {
            for (int i = 0; i < str.split(splitStr).length; i++) {
                singleStr = str.split(splitStr)[i];
                for (int j = 0; j < replacePattern.size(); j++) {
                    if (singleStr.contains(replacePattern.get(j))) {
                        singleStr = singleStr.replace(replacePattern.get(j), "");
                    }
                }
                if (singleStr.startsWith(" ")) {
//                System.out.println("contain space:" + singleStr);
                    singleStr = singleStr.substring(1);
                }
//            System.out.println("split:" + singleStr);
                strList.add(singleStr);
            }
        }
        return strList;
    }

    public static List<String> getMainColumnNames(String dataSourcePath){
        String unique_columns = null;
        List<String> unique_columns_list = new ArrayList<String>();
        List<String> replacePattern = new ArrayList<String>(Arrays.asList("[","'","]"));

        try{
            String[] args = new String[] {"python", "D:\\ASM\\CRM\\DataSourceProcess\\get_main_attributes.py", dataSourcePath};
            Process proc = Runtime.getRuntime().exec(args);//执行py文件
            //intercept results by I/O streams
            BufferedReader in = new BufferedReader(new InputStreamReader(proc.getInputStream()));
            String line = null;

//            while((line = in.readLine()) != null){
//                System.out.println("输出line:"+line);
//            }

            if((line = in.readLine()) != null){
                unique_columns = line;
            }

            in.close();
            proc.waitFor();

        } catch (IOException e) {
            e.printStackTrace();
        } catch (InterruptedException e) {
            e.printStackTrace();
        }

        unique_columns_list = str2List(unique_columns,",",replacePattern);

        return unique_columns_list;
    }

    public static List<SemanticModel> getPositiveSemanticModels(SemanticModel sm, int sm_index, List<String> unique_columns, String savePath) throws Exception {
        String SM_Graphviz_Path = savePath + "positive-models-graphviz/" + sm.getName();
        String SM_Json_Path = savePath + "positive-models-json/" + sm.getName();
        List<ColumnNode> columnNodes = new ArrayList<ColumnNode>();
        List<String> columnNames = new ArrayList<String>();
        List<String> temp_columnNames = new ArrayList<String>();
        List<String> uniqueColumns = new ArrayList<String>(unique_columns);
        List<String> addedColumns = new ArrayList<String>();
        List<List<String>> subSets = new ArrayList<List<String>>();
        List<String> delColumns = new ArrayList<String>();
        List<List<String>> delColumnsList = new ArrayList<List<String>>();
        SemanticModel cloneSM = null;
        SemanticModel positiveSemanticModel = null;
        List<SemanticModel> positiveSemanticModels = new ArrayList<SemanticModel>();

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

        if(unique_columns.size()!=0) {
            subSets = getCombinedSubSets(getSubSets(uniqueColumns), getSubSets(addedColumns));
        }
        else{
            subSets = getSubSets(addedColumns);
        }


//        System.out.println("subSets.size:" + subSets.size());

        int index = 0;
        for(List<String> subset: subSets){
            if(subset.size()>1) {
                index++;
                System.out.println("subset:" + subset);
                temp_columnNames = new ArrayList<String>(columnNames);
                temp_columnNames.removeAll(subset);
                System.out.println("temp_columnNames:" + temp_columnNames);
                cloneSM = sm.clone();
//            positiveSemanticModel = NewEliminatedSemanticModelsForSubSM(cloneSM,index,new HashSet<String>(temp_columnNames),SM_Graphviz_Path,SM_Json_Path);
                positiveSemanticModel = getSubSemanticModels(cloneSM, index, temp_columnNames, SM_Graphviz_Path, SM_Json_Path);
                positiveSemanticModels.add(positiveSemanticModel);
            }
        }
        System.out.println("positiveSemanticModels.size:" + positiveSemanticModels.size());
//        System.out.println("NumOfSpecificColumn:" + getNumOfSpecificColumn(subSets, "Title"));  check the number of subsets with specific column name
        return positiveSemanticModels;
    }

    public static List<SemanticModel> getAllPositiveSemanticModels(SemanticModel sm, int sm_index, List<String> unique_columns, String savePath) throws Exception {
        String SM_Graphviz_Path = savePath + "positive-models-graphviz-all/" + sm.getName();
        String SM_Json_Path = savePath + "positive-models-json-all/" + sm.getName();
        List<ColumnNode> columnNodes = new ArrayList<ColumnNode>();
        List<String> columnNames = new ArrayList<String>();
        List<String> temp_columnNames = new ArrayList<String>();
        List<String> uniqueColumns = new ArrayList<String>(unique_columns);
        List<String> addedColumns = new ArrayList<String>();
        List<List<String>> subSets = new ArrayList<List<String>>();
        List<String> delColumns = new ArrayList<String>();
        List<List<String>> delColumnsList = new ArrayList<List<String>>();
        SemanticModel cloneSM = null;
        SemanticModel positiveSemanticModel = null;
        List<SemanticModel> positiveSemanticModels = new ArrayList<SemanticModel>();

        CreateFile(SM_Graphviz_Path);
        CreateFile(SM_Json_Path);

        columnNodes = sm.getColumnNodes();

//        addedColumns = new ArrayList<>(Arrays.asList("Begin Date", "Attribution", "End Date", "Dated"));// test

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

//        System.out.println("subSets.size:" + subSets.size());
//        for(List<String> subset: subSets){
//            System.out.println("subset:" + subset);
//        }
//        int count = 0;
//        for(int i = 0; i<subSets.size(); i++){
//            if(subSets.get(i).size()>1){
//                ++count;
//                System.out.println("reversed subset:" + subSets.get(i));
//            }
//        }
//        System.out.println("count:" + count);

        int index = 0;
        for(List<String> subset: subSets){
            if(subset.size()>1) {
                index++;
//                if(index > 6) break; // test for partition samples, don't forget delete
                System.out.println("subset:" + subset);
                temp_columnNames = new ArrayList<String>(columnNames);
                temp_columnNames.removeAll(subset);
                System.out.println("temp_columnNames:" + temp_columnNames);
                cloneSM = sm.clone();
                positiveSemanticModel = getSubSemanticModels(cloneSM, index, temp_columnNames, SM_Graphviz_Path, SM_Json_Path);
                positiveSemanticModels.add(positiveSemanticModel);
            }
        }
        System.out.println("positiveSemanticModels.size:" + positiveSemanticModels.size());
//        System.out.println("NumOfSpecificColumn:" + getNumOfSpecificColumn(subSets, "Title"));  check the number of subsets with specific column name
        return positiveSemanticModels;
    }



    public static void main(String[] args) throws Exception {
        String SemanticMoldes_Path = "D:\\ASM\\CRM\\";
        int sourceIndex = 0;
        String sourcePath = "D:\\ASM\\CRM\\sources20230313\\";
        List<String> unique_columns = new ArrayList<String>();
        Boolean flag = true;
        List<SemanticModel> PositiveSamples = new ArrayList<SemanticModel>();
//        List<String> unique_columns = Arrays.asList("Title", "Dimensions"); // test

        if (SemanticModels == null){
            SemanticModels = ModelReader.importSemanticModelsFromJsonFiles(SemanticMoldes_Path + "models-json-20230313", Params.MODEL_MAIN_FILE_EXT);
        }

        if(sourceIndex < 9) {
            sourcePath = sourcePath + "s0" + String.valueOf(++sourceIndex) + ".csv";
        }
        else{
            sourcePath = sourcePath + "s" + String.valueOf(++sourceIndex) + ".csv";
        }


        if(flag){
            PositiveSamples = getAllPositiveSemanticModels(SemanticModels.get(--sourceIndex),--sourceIndex,unique_columns,SemanticMoldes_Path + "positive-models/");
        }
        else{
            unique_columns = getMainColumnNames(sourcePath);
            PositiveSamples = getPositiveSemanticModels(SemanticModels.get(--sourceIndex),--sourceIndex,unique_columns,SemanticMoldes_Path + "positive-models/");
        }


//        for(int i = 0;i<SemanticModels.size();i++){
//            sourceIndex = i;
//            sourcePath = "D:\\ASM\\CRM\\sources20230313\\";
//            if(sourceIndex < 9) {
//                sourcePath = sourcePath + "s0" + String.valueOf(++sourceIndex) + ".csv";
//            }
//            else{
//                sourcePath = sourcePath + "s" + String.valueOf(++sourceIndex) + ".csv";
//            }
//
//            if(flag){
//                PositiveSamples = getAllPositiveSemanticModels(SemanticModels.get(--sourceIndex),--sourceIndex,unique_columns,SemanticMoldes_Path + "positive-models/");
//                System.out.println("obtain all positive semantic models");
//            }
//            else{
//                System.out.println("sourcePath:" + sourcePath);
//                unique_columns = getMainColumnNames(sourcePath);
//                PositiveSamples = getPositiveSemanticModels(SemanticModels.get(--sourceIndex),--sourceIndex,unique_columns,SemanticMoldes_Path + "positive-models/");
//                System.out.println("obtain positive semantic models considering unique columns");
//            }
//        }

    }
}
