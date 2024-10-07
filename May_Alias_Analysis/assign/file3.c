#include<stdio.h>
#include<stdlib.h>


void foo(){
  int a=10,b=11;
  int *p,*y;

  if(b%2){
    p=&a;
  }
  else {
    p=&b; 	
  }
  y=&a;

}

int main(){
   foo();
}
