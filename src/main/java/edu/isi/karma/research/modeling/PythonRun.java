package edu.isi.karma.research.modeling;
import java.io.*;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

public class PythonRun {
    private String environment = "python";
    private String root = null;
    private String cache = "cache\\";
    private boolean autoRemoveCache = true;

    public String run(String path, String ...args) throws IOException {
        String predict_result = null;
        path = createNewPy(path);
        List<String> inputArgs = new LinkedList<>(Arrays.asList(environment, path));  //设定命令行
        inputArgs.addAll(Arrays.asList(args));
        StringBuilder result = new StringBuilder();
        try {
            Process proc = Runtime.getRuntime().exec(inputArgs.toArray(new String[0]));  //执行py文件
            BufferedReader in = new BufferedReader(new InputStreamReader(proc.getInputStream()));
//            String line;
//            while ((line = in.readLine()) != null) {
//                result.append(line).append("\n");
//            }
            String line = null;
            if((line = in.readLine()) != null){
                predict_result = line;
            }
            in.close();
            proc.waitFor();
        } catch (Exception e) {
            e.printStackTrace();
        }
        if (autoRemoveCache && path != null)
            new File(path).delete();
//        return result.toString();
        return predict_result;
    }

    public static class AResult{
        private PythonRun pythonRun;
        private Process process;
        private String path;
        private BufferedWriter out;
        private BufferedWriter out1;
        private BufferedWriter out2;
        private BufferedReader in;

        public AResult(PythonRun pythonRun, Process process, String path) {
            this.pythonRun = pythonRun;
            this.process = process;
            this.path = path;

            out = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));

            in = new BufferedReader(new InputStreamReader(process.getInputStream()));
        }

        public void close() {
            if (pythonRun.autoRemoveCache && path != null)
                new File(path).delete();
            process.destroy();
        }

        public void input(String arg1,String arg2) throws IOException {
            out.append(arg1);
            out.newLine();
            out.append(arg2);
            out.flush();
        }

        public String getResult() throws Exception{
            String predict_result = null;
            String line = null;
//            StringBuilder result = new StringBuilder();
//            do {
//                line = in.readLine();
//                result.append(line).append("\n");
//            } while (in.ready());
            if((line = in.readLine()) != null){
                predict_result = line;
            }
            return predict_result;
        }
    }

    public AResult asyncRun(String path, String ...args) throws IOException {
        System.out.println("运行到这里了吗?");
        path = createNewPy(path);
        System.out.println("输出path:" + path);
        List<String> inputArgs = new LinkedList<>(Arrays.asList(environment, path));  //设定命令行
        inputArgs.addAll(Arrays.asList(args));
        Process process = Runtime.getRuntime().exec(inputArgs.toArray(new String[1]));
        return new AResult(this, process, path);
    }

    private String createNewPy(String path) {
        File file = new File(path);
        if (file.isFile()){
            String result = loadTxt(file);
            if (root != null){
                result = "import sys\n" +
                        "sys.path.append(\"" + root + "\")\n" + result;
            }
            String save = cache + file.getName();
            saveTxt(save, result);
            return save;
        }
        return null;
    }

    private static File saveTxt(String filename, String string){
        File file = new File(filename);
        try {
            BufferedWriter out = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file),"UTF-8"));
            out.write(string);
            out.flush();
            out.close();
        } catch (Exception e) {
            e.printStackTrace();
        }
        return file;
    }
    private String loadTxt(File file){
        StringBuilder result = new StringBuilder();
        try {
            BufferedReader in = new BufferedReader(new InputStreamReader(new FileInputStream(file), "UTF-8"));
            String str;
            while ((str = in.readLine()) != null) {
                result.append(str).append("\n");
            }
        }catch (Exception e){
            e.printStackTrace();
        }
        return result.toString();
    }

    public String getCache() {
        return cache;
    }

    public void setCache(String cache) {
        this.cache = cache;
    }

    public String getEnvironment() {
        return environment;
    }

    public void setEnvironment(String environment) {
        this.environment = environment;
    }

    public String getRoot() {
        return root;
    }

    public void setRoot(String root) {
        this.root = root;
    }

    public boolean isAutoRemoveCache() {
        return autoRemoveCache;
    }

    public void setAutoRemoveCache(boolean autoRemoveCache) {
        this.autoRemoveCache = autoRemoveCache;
    }
}
