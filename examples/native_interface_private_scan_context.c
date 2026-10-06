#include <stdio.h>
int context_i, context_j, context_mark;

void pointer_control(int *p, int *q, int n, int m, int u, int v, int route) {
  int i=0, j=77;
  context_mark=10;
  switch(route) {
  case 0:
    for (;i<n;i++) for(j=0;j<m;j++) p[16*i+j+u+32]=q[16*i+j+v+33]+i-j;
    context_mark+=1;
    goto done;
  case 1:
    for (;i<n;i++) for(j=0;j<m;j++) p[16*i+j+u+32]=q[16*i+j+v+33]+i-j;
    context_i=i; context_j=j; context_mark+=2;
    return;
  default: context_mark+=3; break;
  }
done:
  context_i=i; context_j=j; context_mark+=4;
}

void pointer_two_regions(int *p, int *q, int n, int m, int u, int v, int route) {
  int i=0, j=77;
  context_mark=20+route;
  for (;i<n;i++) for(j=0;j<m;j++) p[16*i+j+u+32]=q[16*i+j+v+33]+i-j;
  context_mark+=5;
  for(i=0;i<n;i++) for(j=0;j<m;j++) p[16*i+j+u+33]=q[16*i+j+v+34]-i+j;
  context_i=i; context_j=j;
}

void pointer_outer_control(int *p, int *q, int n, int m, int u, int v, int route) {
  int r, i=0, j=77;
  context_mark=30;
  for(r=0;r<3;r++) {
    if(r==1)continue;
    for(i=0;i<n;i++) for(j=0;j<m;j++) p[16*i+j+u+32]=q[16*i+j+v+33]+i-j;
    context_mark++;
    if(route)break;
  }
  context_i=i; context_j=j;
}

void pointer_empty_control(int *p, int *q, int n, int m, int u, int v, int route) {
  int i=0, j=77, local_u, local_v;
  context_mark=40+route;
  if(n>0){local_u=u;local_v=v;}
  for (;i<n;i++) for(j=0;j<m;j++) p[16*i+j+local_u+32]=q[16*i+j+local_v+33]+i-j;
  context_i=i; context_j=j;
}

void context_run(int which,int kind,int route,int n,int m,int u,int v) {
  int a[1280],b[1280],i,*p=a+128,*q=b+128;
  for(i=0;i<1280;i++){a[i]=3*i+1;b[i]=5*i+7;}
  if(kind==1)q=p;
  if(kind==2)q=p+1;
  if(kind==3){p=0;q=0;}
  if(which==0)pointer_control(p,q,n,m,u,v,route);
  else if(which==1)pointer_two_regions(p,q,n,m,u,v,route);
  else if(which==2)pointer_outer_control(p,q,n,m,u,v,route);
  else pointer_empty_control(p,q,n,m,u,v,route);
  printf("%d %d %d %d %d %d %d %d %d %d",which,kind,route,n,m,u,v,context_i,context_j,context_mark);
  for(i=0;i<1280;i++)printf(" %d %d",a[i],b[i]);
  printf("\n");
}

int main(void) {
  int which,kind,route,counts,parameters;
  for(which=0;which<4;which++) for(kind=0;kind<3;kind++) for(route=0;route<3;route++)
    for(counts=0;counts<3;counts++) for(parameters=0;parameters<2;parameters++)
      context_run(which,kind,route,counts==0?0:2,counts==1?0:3,parameters?0:3,parameters?0:7);
  for(which=0;which<4;which++)context_run(which,3,0,0,2,(-2147483647-1),2147483647);
  context_run(0,0,0,2,3,-1,0);
  context_run(1,0,0,2,3,64,1);
  return 0;
}
