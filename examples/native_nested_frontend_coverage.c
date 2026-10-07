/* Nested loaded-header frontend coverage; not a benchmark. */
#include <stdio.h>
int nc_row,nc_column,nc_component,nc_pre,nc_post;
void nested_accum(int *a,int *b,int *c,int *shape,int start,int alpha,int take){int row=start,column=77,component=91;for(;row<shape[0]+1;row++)for(column=0;column<shape[1]+1;column++)for(component=0;component<5;component++)a[80*row+5*column+component]=a[80*row+5*column+component]+alpha+row-column+component;nc_row=row;nc_column=column;nc_component=component;}
void nested_multi(int *a,int *b,int *c,int *shape,int start,int alpha,int take){int row=start,column=77,component=91;for(;row<shape[0]+1;row++)for(column=0;column<shape[1]+1;column++)for(component=0;component<5;component++)a[80*row+5*column+component]=b[80*row+5*column+component]+c[80*row+5*column+component]+alpha+row-column+component;nc_row=row;nc_column=column;nc_component=component;}
void nested_chain(int *a,int *b,int *c,int *shape,int start,int alpha,int take){int row=start,column=77,component=91;for(;row<shape[0]+1;row++)for(column=0;column<shape[1]+1;column++)for(component=0;component<5;component++)a[80*row+5*column+component]=a[80*row+5*column+component+75]+alpha+row-column+component;nc_row=row;nc_column=column;nc_component=component;}
void nested_write(int *a,int *b,int *c,int *shape,int start,int alpha,int take){int row=start,column=77,component=91;for(;row<shape[0]+1;row++)for(column=0;column<shape[1]+1;column++)for(component=0;component<5;component++)a[80*row+5*column+component]=1;nc_row=row;nc_column=column;nc_component=component;}
void nested_undefined(int *a,int *b,int *c,int *shape,int start,int alpha,int take){int row=start,column=77,component=91;int local_alpha;if(start<shape[0]+1 && shape[1]+1>0)local_alpha=alpha;for(;row<shape[0]+1;row++)for(column=0;column<shape[1]+1;column++)for(component=0;component<5;component++)a[80*row+5*column+component]=a[80*row+5*column+component]+local_alpha+row-column+component;nc_row=row;nc_column=column;nc_component=component;}
void nested_twice(int *a,int *b,int *c,int *shape,int start,int alpha,int take){int row=start,column=77,component=91;for(;row<shape[0]+1;row++)for(column=0;column<shape[1]+1;column++)for(component=0;component<5;component++)a[80*row+5*column+component]=a[80*row+5*column+component]+alpha+row-column+component;row=0;for(;row<shape[0]+1;row++)for(column=0;column<shape[1]+1;column++)for(component=0;component<5;component++)a[80*row+5*column+component]=a[80*row+5*column+component]+alpha+row-column+component;nc_row=row;nc_column=column;nc_component=component;}
void nested_context(int *a,int *b,int *c,int *shape,int start,int alpha,int take){int row=start,column=77,component=91;nc_pre=nc_pre+7;if(!take){nc_row=-7;nc_column=-8;nc_component=-9;return;}for(;row<shape[0]+1;row++)for(column=0;column<shape[1]+1;column++)for(component=0;component<5;component++)a[80*row+5*column+component]=a[80*row+5*column+component]+alpha+row-column+component;nc_row=row;nc_column=column;nc_component=component;if(take==2){nc_post=nc_post+19;return;}nc_post=nc_post+11;}
void nested_case(int kind,int view,int start,int u,int v,int alpha,int take){
int A[6144],B[2048],C[2048],dims[2],single[1],x;int *a,*b,*c,*shape;
for(x=0;x<6144;x++)A[x]=3*x+1;for(x=0;x<2048;x++){B[x]=3*x+18;C[x]=3*x+35;}
a=A+128;b=B+128;c=C+128;dims[0]=u;dims[1]=v;single[0]=u;shape=dims;
if(view==1){shape=a;shape[0]=u;shape[1]=v;}if(view==2){shape=a+5;shape[0]=u;shape[1]=v;}
if(view==3){b=a;c=a;}if(view==4){b=a+1024;c=a+2048;}if(view==5){b=a+1;c=a+2;}
if(view==7){shape=single;a=0;b=0;c=0;}if(view==8){a=0;b=0;c=0;}
nc_pre=100;nc_post=200;
if(kind==0)nested_accum(a,b,c,shape,start,alpha,take);
if(kind==1)nested_multi(a,b,c,shape,start,alpha,take);
if(kind==2)nested_chain(a,b,c,shape,start,alpha,take);
if(kind==3)nested_write(a,b,c,shape,start,alpha,take);
if(kind==4)nested_undefined(a,b,c,shape,start,alpha,take);
if(kind==5)nested_twice(a,b,c,shape,start,alpha,take);
if(kind==6)nested_context(a,b,c,shape,start,alpha,take);
printf("%d %d %d %d %d %d %d %d %d %d %d %d %d %d",kind,view,start,u,v,alpha,take,nc_row,nc_column,nc_component,nc_pre,nc_post,shape[0],view==7?99:shape[1]);
for(x=0;x<6144;x++)printf(" %d",A[x]);for(x=0;x<2048;x++)printf(" %d",B[x]);for(x=0;x<2048;x++)printf(" %d",C[x]);printf("\n");}
int main(void){
nested_case(0,0,0,2,2,1,1);
nested_case(0,0,0,2,3,1,1);
nested_case(0,0,1,2,2,1,1);
nested_case(0,0,-1,2,2,1,1);
nested_case(0,0,3,2,2,1,1);
nested_case(0,0,0,0,0,1,1);
nested_case(0,0,0,2,0,1,1);
nested_case(0,0,0,4,2,1,1);
nested_case(0,0,0,2,4,1,1);
nested_case(0,0,0,-1,99,2147483647,1);
nested_case(0,0,0,2,2,2147483647,1);
nested_case(0,0,0,2,2,(-2147483647-1),1);
nested_case(0,7,0,-1,99,2147483647,1);
nested_case(0,7,0,2147483647,99,2147483647,1);
nested_case(0,8,0,2,-1,2147483647,1);
nested_case(0,8,0,2,2147483647,2147483647,1);
nested_case(1,0,0,2,2,1,1);
nested_case(1,0,0,2,3,1,1);
nested_case(1,0,1,2,2,1,1);
nested_case(1,0,-1,2,2,1,1);
nested_case(1,0,3,2,2,1,1);
nested_case(1,0,0,0,0,1,1);
nested_case(1,0,0,2,0,1,1);
nested_case(1,0,0,4,2,1,1);
nested_case(1,0,0,2,4,1,1);
nested_case(1,0,0,-1,99,2147483647,1);
nested_case(1,0,0,2,2,2147483647,1);
nested_case(1,0,0,2,2,(-2147483647-1),1);
nested_case(1,7,0,-1,99,2147483647,1);
nested_case(1,7,0,2147483647,99,2147483647,1);
nested_case(1,8,0,2,-1,2147483647,1);
nested_case(1,8,0,2,2147483647,2147483647,1);
nested_case(2,0,0,2,2,1,1);
nested_case(2,0,0,2,3,1,1);
nested_case(2,0,1,2,2,1,1);
nested_case(2,0,-1,2,2,1,1);
nested_case(2,0,3,2,2,1,1);
nested_case(2,0,0,0,0,1,1);
nested_case(2,0,0,2,0,1,1);
nested_case(2,0,0,4,2,1,1);
nested_case(2,0,0,2,4,1,1);
nested_case(2,0,0,-1,99,2147483647,1);
nested_case(2,0,0,2,2,2147483647,1);
nested_case(2,0,0,2,2,(-2147483647-1),1);
nested_case(2,7,0,-1,99,2147483647,1);
nested_case(2,7,0,2147483647,99,2147483647,1);
nested_case(2,8,0,2,-1,2147483647,1);
nested_case(2,8,0,2,2147483647,2147483647,1);
nested_case(3,0,0,2,2,1,1);
nested_case(3,0,0,2,3,1,1);
nested_case(3,0,1,2,2,1,1);
nested_case(3,0,-1,2,2,1,1);
nested_case(3,0,3,2,2,1,1);
nested_case(3,0,0,0,0,1,1);
nested_case(3,0,0,2,0,1,1);
nested_case(3,0,0,4,2,1,1);
nested_case(3,0,0,2,4,1,1);
nested_case(3,0,0,-1,99,2147483647,1);
nested_case(3,0,0,2,2,2147483647,1);
nested_case(3,0,0,2,2,(-2147483647-1),1);
nested_case(3,7,0,-1,99,2147483647,1);
nested_case(3,7,0,2147483647,99,2147483647,1);
nested_case(3,8,0,2,-1,2147483647,1);
nested_case(3,8,0,2,2147483647,2147483647,1);
nested_case(4,0,0,2,2,1,1);
nested_case(4,0,0,2,3,1,1);
nested_case(4,0,1,2,2,1,1);
nested_case(4,0,-1,2,2,1,1);
nested_case(4,0,3,2,2,1,1);
nested_case(4,0,0,0,0,1,1);
nested_case(4,0,0,2,0,1,1);
nested_case(4,0,0,4,2,1,1);
nested_case(4,0,0,2,4,1,1);
nested_case(4,0,0,-1,99,2147483647,1);
nested_case(4,0,0,2,2,2147483647,1);
nested_case(4,0,0,2,2,(-2147483647-1),1);
nested_case(4,7,0,-1,99,2147483647,1);
nested_case(4,7,0,2147483647,99,2147483647,1);
nested_case(4,8,0,2,-1,2147483647,1);
nested_case(4,8,0,2,2147483647,2147483647,1);
nested_case(5,0,0,2,2,1,1);
nested_case(5,0,0,2,3,1,1);
nested_case(5,0,1,2,2,1,1);
nested_case(5,0,-1,2,2,1,1);
nested_case(5,0,3,2,2,1,1);
nested_case(5,0,0,0,0,1,1);
nested_case(5,0,0,2,0,1,1);
nested_case(5,0,0,4,2,1,1);
nested_case(5,0,0,2,4,1,1);
nested_case(5,0,0,-1,99,2147483647,1);
nested_case(5,0,0,2,2,2147483647,1);
nested_case(5,0,0,2,2,(-2147483647-1),1);
nested_case(5,7,0,-1,99,2147483647,1);
nested_case(5,7,0,2147483647,99,2147483647,1);
nested_case(5,8,0,2,-1,2147483647,1);
nested_case(5,8,0,2,2147483647,2147483647,1);
nested_case(6,0,0,2,2,1,1);
nested_case(6,0,0,2,3,1,1);
nested_case(6,0,1,2,2,1,1);
nested_case(6,0,-1,2,2,1,1);
nested_case(6,0,3,2,2,1,1);
nested_case(6,0,0,0,0,1,1);
nested_case(6,0,0,2,0,1,1);
nested_case(6,0,0,4,2,1,1);
nested_case(6,0,0,2,4,1,1);
nested_case(6,0,0,-1,99,2147483647,1);
nested_case(6,0,0,2,2,2147483647,1);
nested_case(6,0,0,2,2,(-2147483647-1),1);
nested_case(6,7,0,-1,99,2147483647,1);
nested_case(6,7,0,2147483647,99,2147483647,1);
nested_case(6,8,0,2,-1,2147483647,1);
nested_case(6,8,0,2,2147483647,2147483647,1);
nested_case(1,3,0,2,3,1,1);
nested_case(1,4,0,2,3,1,1);
nested_case(1,5,0,2,3,1,1);
nested_case(3,1,0,2,2,1,1);
nested_case(3,2,0,2,2,1,1);
nested_case(6,0,0,2,3,1,0);
nested_case(6,0,0,2,3,1,2);return 0;}
