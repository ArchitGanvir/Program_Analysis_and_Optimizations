#include<stdio.h>
#include<stdlib.h>


void foo(){
  int *p,*y,a,b,**p1;

  p=&a;
  y=&b;

  p1=&p;

  *p1=&b;

}

int main(){
   foo();
}
