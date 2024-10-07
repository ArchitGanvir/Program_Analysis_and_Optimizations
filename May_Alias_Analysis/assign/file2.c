#include<stdio.h>
#include<stdlib.h>


void foo(int a,int b){
  int *p,*y;

  p=&a;
  y=&b;

  //OUTPUT(From LLVM IR)

  /*
    Points-to information as observed at the last program point in function Foo:
    p -> {}
    y -> {}
  */    

}

int main(){
   int x=10,y=11;
   foo(x,y);
}
