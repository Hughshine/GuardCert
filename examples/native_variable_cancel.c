#include <stdio.h>
#include <limits.h>

int guarded_mul_div(int x,int y) {
  if(y==0)return 73;
  if(y==-1 && x==INT_MIN)return 74;
  return (x*y)/y;
}
int guarded_mul_div_context(int x,int y) {
  if(y==0)return 73;
  if(y==-1 && x==INT_MIN)return 74;
  return ((x*y)/y+17)*3;
}
int guarded_square_div(int x) {
  if(x==0)return 75;
  return (x*x)/x;
}
int unreachable_division(int x,int y) {
  if(y==0)return y && ((x*y)/y);
  return 76;
}
int main(void){return 0;}
