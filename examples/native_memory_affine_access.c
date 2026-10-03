#include <stdio.h>
int access_global_a[480],access_global_b[500],access_global_c[600];

void affine_access_transpose(int start,int n,int m,int p) { int a[480],b[500],c[600]; int i=start,j=99,k=55,x,r; for (x=0;x<480;x++) a[x]=3*x+1; for (x=0;x<500;x++) b[x]=5*x+2; for (x=0;x<600;x++) c[x]=-777; for (;i<n;i++) { k=2*i+m-p; for (j=0;j<k;j++) { b[i*20+j] = a[j*17+i]; } } printf("affine_access_transpose-a %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<480;x++) printf("%d%c",a[x],x==479?'\n':' ');
printf("affine_access_transpose-b %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<500;x++) printf("%d%c",b[x],x==499?'\n':' ');
printf("affine_access_transpose-c %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<600;x++) printf("%d%c",c[x],x==599?'\n':' ');
 }


void affine_access_scaled(int start,int n,int m,int p) { int a[480],b[500],c[600]; int i=start,j=99,k=55,x,r; for (x=0;x<480;x++) a[x]=3*x+1; for (x=0;x<500;x++) b[x]=5*x+2; for (x=0;x<600;x++) c[x]=-777; for (;i<n;i++) { k=2*i+m-p; for (j=0;j<k;j++) { b[i*20+j] = a[i*31+j*2]; } } printf("affine_access_scaled-a %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<480;x++) printf("%d%c",a[x],x==479?'\n':' ');
printf("affine_access_scaled-b %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<500;x++) printf("%d%c",b[x],x==499?'\n':' ');
printf("affine_access_scaled-c %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<600;x++) printf("%d%c",c[x],x==599?'\n':' ');
 }


void affine_access_left(int start,int n,int m,int p) { int a[480],b[500],c[600]; int i=start,j=99,k=55,x,r; for (x=0;x<480;x++) a[x]=3*x+1; for (x=0;x<500;x++) b[x]=5*x+2; for (x=0;x<600;x++) c[x]=-777; for (;i<n;i++) { k=2*i+m-p; for (j=0;j<k;j++) { b[i*20+j] = a[31*i+2*j]; } } printf("affine_access_left-a %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<480;x++) printf("%d%c",a[x],x==479?'\n':' ');
printf("affine_access_left-b %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<500;x++) printf("%d%c",b[x],x==499?'\n':' ');
printf("affine_access_left-c %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<600;x++) printf("%d%c",c[x],x==599?'\n':' ');
 }


void affine_access_scatter(int start,int n,int m,int p) { int a[480],b[500],c[600]; int i=start,j=99,k=55,x,r; for (x=0;x<480;x++) a[x]=3*x+1; for (x=0;x<500;x++) b[x]=5*x+2; for (x=0;x<600;x++) c[x]=-777; for (;i<n;i++) { k=2*i+m-p; for (j=0;j<k;j++) { b[j*19+i*2] = a[i*23+j]; } } printf("affine_access_scatter-a %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<480;x++) printf("%d%c",a[x],x==479?'\n':' ');
printf("affine_access_scatter-b %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<500;x++) printf("%d%c",b[x],x==499?'\n':' ');
printf("affine_access_scatter-c %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<600;x++) printf("%d%c",c[x],x==599?'\n':' ');
 }


void affine_access_chain(int start,int n,int m,int p) { int a[480],b[500],c[600]; int i=start,j=99,k=55,x,r; for (x=0;x<480;x++) a[x]=3*x+1; for (x=0;x<500;x++) b[x]=5*x+2; for (x=0;x<600;x++) c[x]=-777; for (;i<n;i++) { k=2*i+m-p; for (j=0;j<k;j++) { b[i*20+j] = a[j*17+i]; c[i*24+j] = b[i*20+j]; b[i*20+j] = b[i*20+j]+(i*11+j+19); } } printf("affine_access_chain-a %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<480;x++) printf("%d%c",a[x],x==479?'\n':' ');
printf("affine_access_chain-b %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<500;x++) printf("%d%c",b[x],x==499?'\n':' ');
printf("affine_access_chain-c %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<600;x++) printf("%d%c",c[x],x==599?'\n':' ');
 }


void affine_access_alias(int start,int n,int m,int p) { int a[480],b[500],c[600]; int i=start,j=99,k=55,x,r; for (x=0;x<480;x++) a[x]=3*x+1; for (x=0;x<500;x++) b[x]=5*x+2; for (x=0;x<600;x++) c[x]=-777; for (;i<n;i++) { k=2*i+m-p; for (j=0;j<k;j++) { b[i*20+j] = b[j*17+i]; } } printf("affine_access_alias-a %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<480;x++) printf("%d%c",a[x],x==479?'\n':' ');
printf("affine_access_alias-b %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<500;x++) printf("%d%c",b[x],x==499?'\n':' ');
printf("affine_access_alias-c %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<600;x++) printf("%d%c",c[x],x==599?'\n':' ');
 }


void affine_access_context(int start,int n,int m,int p) {  int i=start,j=99,k=55,x,r; for (x=0;x<480;x++) access_global_a[x]=3*x+1; for (x=0;x<500;x++) access_global_b[x]=5*x+2; for (x=0;x<600;x++) access_global_c[x]=-777; for (r=0;r<2;r++) { i=start; for (;i<n;i++) { k=2*i+m-p; for (j=0;j<k;j++) { access_global_b[i*20+j] = access_global_a[j*17+i]; } } } printf("affine_access_context-a %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<480;x++) printf("%d%c",access_global_a[x],x==479?'\n':' ');
printf("affine_access_context-b %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<500;x++) printf("%d%c",access_global_b[x],x==499?'\n':' ');
printf("affine_access_context-c %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<600;x++) printf("%d%c",access_global_c[x],x==599?'\n':' ');
 }


void affine_access_neighbor(int start,int n,int m,int p) { int a[480],b[500],c[600]; int i=start,j=99,k=55,x,r; for (x=0;x<480;x++) a[x]=3*x+1; for (x=0;x<500;x++) b[x]=5*x+2; for (x=0;x<600;x++) c[x]=-777; for (;i<n;i++) { k=2*i+m-p; for (j=0;j<k;j++) { b[i*20+j] = a[i*31+j+1]; } } printf("affine_access_neighbor-a %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<480;x++) printf("%d%c",a[x],x==479?'\n':' ');
printf("affine_access_neighbor-b %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<500;x++) printf("%d%c",b[x],x==499?'\n':' ');
printf("affine_access_neighbor-c %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<600;x++) printf("%d%c",c[x],x==599?'\n':' ');
 }


void affine_access_nonlinear(int start,int n,int m,int p) { int a[480],b[500],c[600]; int i=start,j=99,k=55,x,r; for (x=0;x<480;x++) a[x]=3*x+1; for (x=0;x<500;x++) b[x]=5*x+2; for (x=0;x<600;x++) c[x]=-777; for (;i<n;i++) { k=2*i+m-p; for (j=0;j<k;j++) { b[i*20+j] = a[i*j]; } } printf("affine_access_nonlinear-a %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<480;x++) printf("%d%c",a[x],x==479?'\n':' ');
printf("affine_access_nonlinear-b %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<500;x++) printf("%d%c",b[x],x==499?'\n':' ');
printf("affine_access_nonlinear-c %d %d %d %d %d ",i,j,k,m,p); for(x=0;x<600;x++) printf("%d%c",c[x],x==599?'\n':' ');
 }

int main(void) { int n,m,p; for(n=0;n<6;n++) for(m=-1;m<6;m++) for(p=-1;p<2;p++) { affine_access_transpose(0,n,m,p);
affine_access_scaled(0,n,m,p);
affine_access_left(0,n,m,p);
affine_access_scatter(0,n,m,p);
affine_access_chain(0,n,m,p);
affine_access_alias(0,n,m,p);
affine_access_context(0,n,m,p);
affine_access_neighbor(0,n,m,p);
affine_access_nonlinear(0,n,m,p);
 } affine_access_transpose(2,4,5,1); affine_access_transpose(0,0,-2147483647-1,2147483647); affine_access_transpose(0,-2,2147483647,-2147483647-1);
affine_access_scaled(2,4,5,1); affine_access_scaled(0,0,-2147483647-1,2147483647); affine_access_scaled(0,-2,2147483647,-2147483647-1);
affine_access_left(2,4,5,1); affine_access_left(0,0,-2147483647-1,2147483647); affine_access_left(0,-2,2147483647,-2147483647-1);
affine_access_scatter(2,4,5,1); affine_access_scatter(0,0,-2147483647-1,2147483647); affine_access_scatter(0,-2,2147483647,-2147483647-1);
affine_access_chain(2,4,5,1); affine_access_chain(0,0,-2147483647-1,2147483647); affine_access_chain(0,-2,2147483647,-2147483647-1);
affine_access_alias(2,4,5,1); affine_access_alias(0,0,-2147483647-1,2147483647); affine_access_alias(0,-2,2147483647,-2147483647-1);
affine_access_context(2,4,5,1); affine_access_context(0,0,-2147483647-1,2147483647); affine_access_context(0,-2,2147483647,-2147483647-1);
affine_access_neighbor(2,4,5,1); affine_access_neighbor(0,0,-2147483647-1,2147483647); affine_access_neighbor(0,-2,2147483647,-2147483647-1);
affine_access_nonlinear(2,4,5,1); affine_access_nonlinear(0,0,-2147483647-1,2147483647); affine_access_nonlinear(0,-2,2147483647,-2147483647-1);
affine_access_alias(0,6,6,0); affine_access_chain(0,4,100,99); return 0; }
