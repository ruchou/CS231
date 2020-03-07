
class C{
    Object m(){
        return new Integer(4);
    }
    void n(Object o){ System.out.println("C.m")}

    void p(String s){}
}

class D extends C{
    String m(){
        return "hi";
    }

    void p(Object o){}
    void n(String o){System.out.println("D.m")}
   //java does not allow covariance return type
   //not overloading
}

main{
    C c = new  D();
    c.m(new Integer(5))});// c.m
        }


class Main{
    void printAll(List<Object> l){
        for(Object o : l) {
            System.out.println(o.toString());
        }
    }
}