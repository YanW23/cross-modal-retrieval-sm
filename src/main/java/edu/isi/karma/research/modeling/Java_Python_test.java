package edu.isi.karma.research.modeling;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

public class Java_Python_test {
    public static void main(String[] args){
//        int a = 18;
//        int b = 23;
//        String result = "";
        try{
            String[] args1 = new String[] {"python", "F:\\Cross-Modal Retrieval Model IN Linux\\Cross-Modal Retrieval Model L1 Loss\\my_predict.py"};
            Process proc = Runtime.getRuntime().exec(args1);//执行py文件
            //用输入输出流来截取结果
            BufferedReader in = new BufferedReader(new InputStreamReader(proc.getInputStream()));
            String line = null;
            while((line = in.readLine()) != null){
                System.out.println("输出line:"+line);
            }
//            result = in.readLine();
//            System.out.println("输出result:" + result);
            in.close();
            proc.waitFor();

        } catch (IOException e) {
            e.printStackTrace();
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
//        return result;
    }
}
