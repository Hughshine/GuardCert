/* Independent adaptation of the OLO Figure 1/2 motivating shape.
   Fixed 16x16x5 layout; flat signed32 data and a replacement arithmetic body.
   This is an excerpt coverage probe, not the NPB BT benchmark. */
#include <stdio.h>
int bt_j,bt_i,bt_c;
void bt_excerpt(int *output,int *shape){
  int row=0,column=77,component=91;
  for(row=0;row<shape[0]+1;row++)
    for(column=0;column<shape[1]+1;column++)
      for(component=0;component<5;component++)
        output[(row*16+column)*5+component]=row+column+component;
  bt_j=row;bt_i=column;bt_c=component;
}
void bt_case(int view,int u,int v){
  int data[2048],dims[2],single[1],x,*output=data,*shape=dims;
  for(x=0;x<2048;x++)data[x]=3*x+7;
  dims[0]=u;dims[1]=v;single[0]=u;
  if(view==1){shape=data;shape[0]=u;shape[1]=v;}
  if(view==2){shape=data+5;shape[0]=u;shape[1]=v;}
  if(view==3){shape=single;output=0;}
  if(view==4)output=0;
  bt_excerpt(output,shape);
  printf("%d %d %d %d %d %d %d %d",view,u,v,bt_j,bt_i,bt_c,shape[0],view==3?99:shape[1]);
  for(x=0;x<2048;x++)printf(" %d",data[x]);printf("\n");
}
int main(void){
bt_case(0,2,2);
bt_case(0,0,0);
bt_case(1,2,2);
bt_case(2,2,2);
bt_case(3,-1,99);
bt_case(3,2147483647,99);
bt_case(4,2,-1);
bt_case(0,-2,1);return 0;}
