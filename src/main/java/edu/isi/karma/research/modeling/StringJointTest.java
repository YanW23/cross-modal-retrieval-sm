package edu.isi.karma.research.modeling;

import java.util.Scanner;

public class StringJointTest {
    //第一种方法：使用+
    public static  String mergedString1(String string1,String string2) {
        return   string1 + ";" + string2;
    }

    //第二种：使用concat()；
    public static String mergedString2(String string1, String string2) {
        return string1.concat(string2);
    }

    //第三种：使用append()；
    public static  StringBuffer mergedString3(String string1, String string2) {
        StringBuffer sb = new StringBuffer(string1);
        return sb.append(string2);

    }

    public static void main(String[] args) {
//        System.out.print("请输入字符串1:");
//        String string1 = input.nextLine();
//        System.out.print("请输入字符串2:");
//        String string2 = input.nextLine();
        StringBuffer sbf = new StringBuffer();
        for(int i=0;i<5;i++){
            Scanner input = new Scanner(System.in);
            System.out.print("请输入字符串:");
            String string = input.nextLine();
            sbf.append(string);
            if(i<4) {
                sbf.append(";");
            }
        }
        System.out.println("输出字符串:" + sbf.toString());
//        System.out.println("第一种方法输出的字符串是：" + mergedString1(string1, string2));
//        System.out.println("第二种方法输出的字符串是:" + mergedString2(string1,string2));
//        System.out.println("第三种方法输出的字符串是:" + mergedString3(string1,string2));
    }
}

