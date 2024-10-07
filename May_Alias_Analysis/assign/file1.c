#include<stdio.h>
#include<stdlib.h>


void foo(){
  int a=10,b=11;
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
   foo();
}
