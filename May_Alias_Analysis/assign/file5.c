#include<stdio.h>
#include<stdlib.h>


void foo(){
  int a=10,b,*p,*q;

  p=&b;

  while(a--){
    if (a > 5){
    	p=&a;
    }
    q=&a;
  } 

}

int main(){
   foo();
}


