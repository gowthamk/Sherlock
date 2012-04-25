#include<stdio.h>
void foo(int a){
    printf("a is %d\n",a);
    return;
}
int main(){
    int a = 9;
    a+=3;
    scanf("%d",&a);
    foo(a);
}
