#include <stdio.h>
#define SIZE 256
static void seed(int *values) { int x; for(x=0;x<SIZE;++x) values[x]=3*x+1; }
static void emit(const char *name,int offset,int *values,int *exits,int start,int n,int m,int p,int alpha,int beta,int rank) { int x; printf("%s %d %d %d %d %d %d %d",name,offset,start,n,m,p,alpha,beta); for(x=0;x<rank;++x) printf(" %d",exits[x]); for(x=0;x<SIZE;++x) printf(" %d",values[x]); putchar(10); }
void signed_read(int *buf,int start,int n,int m,int p,int alpha,int beta,int *exits) {
int i=start,j=77;
for(;i<n;++i) { for(j=0;j<m;++j) {
buf[8*i+j]=buf[63-8*i-j]*alpha+buf[8*i+j]+beta+i*j;
} }
exits[0]=i; exits[1]=j;
}
void run_signed_read(int offset,int start,int n,int m,int p,int alpha,int beta) { int values[SIZE],exits[2]; seed(values); signed_read(offset<0 ? 0 : values+offset,start,n,m,p,alpha,beta,exits); emit("signed_read",offset,values,exits,start,n,m,p,alpha,beta,2); }
void signed_write(int *buf,int start,int n,int m,int p,int alpha,int beta,int *exits) {
int i=start,j=77;
for(;i<n;++i) { for(j=0;j<m;++j) {
buf[63-8*i-j]=buf[8*i+j]*alpha+beta;
} }
exits[0]=i; exits[1]=j;
}
void run_signed_write(int offset,int start,int n,int m,int p,int alpha,int beta) { int values[SIZE],exits[2]; seed(values); signed_write(offset<0 ? 0 : values+offset,start,n,m,p,alpha,beta,exits); emit("signed_write",offset,values,exits,start,n,m,p,alpha,beta,2); }
void signed_chain(int *buf,int start,int n,int m,int p,int alpha,int beta,int *exits) {
int i=start,j=77;
for(;i<n;++i) { for(j=0;j<m;++j) {
buf[63-8*i-j]=buf[63-8*i-j]*alpha+beta;
buf[62-8*i-j]=buf[63-8*i-j]+buf[62-8*i-j]*beta;
} }
exits[0]=i; exits[1]=j;
}
void run_signed_chain(int offset,int start,int n,int m,int p,int alpha,int beta) { int values[SIZE],exits[2]; seed(values); signed_chain(offset<0 ? 0 : values+offset,start,n,m,p,alpha,beta,exits); emit("signed_chain",offset,values,exits,start,n,m,p,alpha,beta,2); }
void signed_context(int *buf,int start,int n,int m,int p,int alpha,int beta,int *exits) {
int i=start,j=77;
int repeat; for(repeat=0;repeat<2;++repeat) { i=start;
for(;i<n;++i) { for(j=0;j<m;++j) {
buf[8*i+j]=buf[63-8*i-j]*alpha+buf[8*i+j]+beta+i*j;
} }
}
exits[0]=i; exits[1]=j;
}
void run_signed_context(int offset,int start,int n,int m,int p,int alpha,int beta) { int values[SIZE],exits[2]; seed(values); signed_context(offset<0 ? 0 : values+offset,start,n,m,p,alpha,beta,exits); emit("signed_context",offset,values,exits,start,n,m,p,alpha,beta,2); }
void signed_three(int *buf,int start,int n,int m,int p,int alpha,int beta,int *exits) {
int i=start,j=77,k=55;
for(;i<n;++i) { for(j=0;j<m;++j) {
for(k=0;k<p;++k) {
buf[32*i+4*j+k]=buf[111-32*i-4*j-k]*alpha+beta+i*k+j;
}
} }
exits[0]=i; exits[1]=j;exits[2]=k;
}
void run_signed_three(int offset,int start,int n,int m,int p,int alpha,int beta) { int values[SIZE],exits[3]; seed(values); signed_three(offset<0 ? 0 : values+offset,start,n,m,p,alpha,beta,exits); emit("signed_three",offset,values,exits,start,n,m,p,alpha,beta,3); }
void signed_undef(int *buf,int start,int n,int m,int p,int alpha,int beta,int *exits) {
int i=start,j=77;
int unused_alpha;
for(;i<n;++i) { for(j=0;j<m;++j) {
buf[63-8*i-j]=buf[63-8*i-j]*unused_alpha+beta;
} }
exits[0]=i; exits[1]=j;
}
void run_signed_undef(int offset,int start,int n,int m,int p,int alpha,int beta) { int values[SIZE],exits[2]; seed(values); signed_undef(offset<0 ? 0 : values+offset,start,n,m,p,alpha,beta,exits); emit("signed_undef",offset,values,exits,start,n,m,p,alpha,beta,2); }
void signed_mixed(int *buf,int start,int n,int m,int p,int alpha,int beta,int *exits) { int i=start,j=77; for(;i<n;++i) { for(j=0;j<m;++j) { buf[8*i+j]=buf[56-8*i+j]*alpha+buf[8*i+j]+beta+i*j; } } exits[0]=i; exits[1]=j; }
void run_signed_mixed(int offset,int start,int n,int m,int p,int alpha,int beta) { int values[SIZE],exits[2]; seed(values); signed_mixed(offset<0 ? 0 : values+offset,start,n,m,p,alpha,beta,exits); emit("signed_mixed",offset,values,exits,start,n,m,p,alpha,beta,2); }
void signed_address_wrap(int *buf,int start,int n,int m,int p,int alpha,int beta,int *exits) { int i=start,j=77; for(;i<n;++i) { for(j=0;j<m;++j) { buf[8*i+j]=buf[63-(2147483647*i+i)+(2147483647*i+i)-8*i-j]*alpha+buf[8*i+j]+beta+i*j; } } exits[0]=i; exits[1]=j; }
void run_signed_address_wrap(int offset,int start,int n,int m,int p,int alpha,int beta) { int values[SIZE],exits[2]; seed(values); signed_address_wrap(offset<0 ? 0 : values+offset,start,n,m,p,alpha,beta,exits); emit("signed_address_wrap",offset,values,exits,start,n,m,p,alpha,beta,2); }
void signed_array(int start,int n,int m,int alpha,int beta) { int a[SIZE],b[SIZE],c[SIZE],i=start,j=77,x; seed(a); seed(b); seed(c); for(;i<n;++i) { for(j=0;j<m;++j) { c[63-8*i-j]=a[8*i+j]*alpha+b[8*i+j]*beta; c[8*i+j]=c[8*i+j]+a[63-8*i-j]*beta; } } printf("signed_array %d %d %d %d %d %d %d",start,n,m,alpha,beta,i,j); for(x=0;x<SIZE;++x) printf(" %d %d %d",a[x],b[x],c[x]); putchar(10); }
void signed_array_no_zero_anchor(int start,int n,int m,int alpha,int beta) { int a[SIZE],b[SIZE],i=start,j=77,x; seed(a); seed(b); for(;i<n;++i) { for(j=0;j<m;++j) { b[63-8*i-j]=a[63-8*i-j]*alpha+beta; } } printf("signed_array_no_zero_anchor %d %d %d %d %d %d %d",start,n,m,alpha,beta,i,j); for(x=0;x<SIZE;++x) printf(" %d %d",a[x],b[x]); putchar(10); }
int main(void) {
run_signed_read(3,0,1,1,1,3,-7);
run_signed_read(3,0,1,1,1,-5,11);
run_signed_read(3,0,1,1,1,2147483647,-2147483648);
run_signed_read(3,0,1,1,1,-2147483648,2147483647);
run_signed_read(3,0,2,3,2,3,-7);
run_signed_read(3,0,2,3,2,-5,11);
run_signed_read(3,0,2,3,2,2147483647,-2147483648);
run_signed_read(3,0,2,3,2,-2147483648,2147483647);
run_signed_read(3,0,3,2,3,3,-7);
run_signed_read(3,0,3,2,3,-5,11);
run_signed_read(3,0,3,2,3,2147483647,-2147483648);
run_signed_read(3,0,3,2,3,-2147483648,2147483647);
run_signed_read(3,0,4,4,4,3,-7);
run_signed_read(3,0,4,4,4,-5,11);
run_signed_read(3,0,4,4,4,2147483647,-2147483648);
run_signed_read(3,0,4,4,4,-2147483648,2147483647);
run_signed_read(-1,0,0,-2147483648,-2147483648,3,-7);
run_signed_read(-1,0,2,0,-2147483648,3,-7);
run_signed_read(3,1,3,2,2,3,-7);
run_signed_write(3,0,1,1,1,3,-7);
run_signed_write(3,0,1,1,1,-5,11);
run_signed_write(3,0,1,1,1,2147483647,-2147483648);
run_signed_write(3,0,1,1,1,-2147483648,2147483647);
run_signed_write(3,0,2,3,2,3,-7);
run_signed_write(3,0,2,3,2,-5,11);
run_signed_write(3,0,2,3,2,2147483647,-2147483648);
run_signed_write(3,0,2,3,2,-2147483648,2147483647);
run_signed_write(3,0,3,2,3,3,-7);
run_signed_write(3,0,3,2,3,-5,11);
run_signed_write(3,0,3,2,3,2147483647,-2147483648);
run_signed_write(3,0,3,2,3,-2147483648,2147483647);
run_signed_write(3,0,4,4,4,3,-7);
run_signed_write(3,0,4,4,4,-5,11);
run_signed_write(3,0,4,4,4,2147483647,-2147483648);
run_signed_write(3,0,4,4,4,-2147483648,2147483647);
run_signed_write(-1,0,0,-2147483648,-2147483648,3,-7);
run_signed_write(-1,0,2,0,-2147483648,3,-7);
run_signed_write(3,1,3,2,2,3,-7);
run_signed_chain(3,0,1,1,1,3,-7);
run_signed_chain(3,0,1,1,1,-5,11);
run_signed_chain(3,0,1,1,1,2147483647,-2147483648);
run_signed_chain(3,0,1,1,1,-2147483648,2147483647);
run_signed_chain(3,0,2,3,1,3,-7);
run_signed_chain(3,0,2,3,1,-5,11);
run_signed_chain(3,0,2,3,1,2147483647,-2147483648);
run_signed_chain(3,0,2,3,1,-2147483648,2147483647);
run_signed_chain(3,0,3,2,1,3,-7);
run_signed_chain(3,0,3,2,1,-5,11);
run_signed_chain(3,0,3,2,1,2147483647,-2147483648);
run_signed_chain(3,0,3,2,1,-2147483648,2147483647);
run_signed_chain(3,0,4,4,1,3,-7);
run_signed_chain(3,0,4,4,1,-5,11);
run_signed_chain(3,0,4,4,1,2147483647,-2147483648);
run_signed_chain(3,0,4,4,1,-2147483648,2147483647);
run_signed_chain(-1,0,0,-2147483648,-2147483648,3,-7);
run_signed_chain(-1,0,2,0,-2147483648,3,-7);
run_signed_chain(3,1,3,2,2,3,-7);
run_signed_context(3,0,1,1,1,3,-7);
run_signed_context(3,0,1,1,1,-5,11);
run_signed_context(3,0,1,1,1,2147483647,-2147483648);
run_signed_context(3,0,1,1,1,-2147483648,2147483647);
run_signed_context(3,0,2,3,2,3,-7);
run_signed_context(3,0,2,3,2,-5,11);
run_signed_context(3,0,2,3,2,2147483647,-2147483648);
run_signed_context(3,0,2,3,2,-2147483648,2147483647);
run_signed_context(3,0,3,2,3,3,-7);
run_signed_context(3,0,3,2,3,-5,11);
run_signed_context(3,0,3,2,3,2147483647,-2147483648);
run_signed_context(3,0,3,2,3,-2147483648,2147483647);
run_signed_context(3,0,4,4,4,3,-7);
run_signed_context(3,0,4,4,4,-5,11);
run_signed_context(3,0,4,4,4,2147483647,-2147483648);
run_signed_context(3,0,4,4,4,-2147483648,2147483647);
run_signed_context(-1,0,0,-2147483648,-2147483648,3,-7);
run_signed_context(-1,0,2,0,-2147483648,3,-7);
run_signed_context(3,1,3,2,2,3,-7);
run_signed_three(3,0,1,1,1,3,-7);
run_signed_three(3,0,1,1,1,-5,11);
run_signed_three(3,0,1,1,1,2147483647,-2147483648);
run_signed_three(3,0,1,1,1,-2147483648,2147483647);
run_signed_three(3,0,2,3,2,3,-7);
run_signed_three(3,0,2,3,2,-5,11);
run_signed_three(3,0,2,3,2,2147483647,-2147483648);
run_signed_three(3,0,2,3,2,-2147483648,2147483647);
run_signed_three(3,0,3,2,3,3,-7);
run_signed_three(3,0,3,2,3,-5,11);
run_signed_three(3,0,3,2,3,2147483647,-2147483648);
run_signed_three(3,0,3,2,3,-2147483648,2147483647);
run_signed_three(3,0,4,4,4,3,-7);
run_signed_three(3,0,4,4,4,-5,11);
run_signed_three(3,0,4,4,4,2147483647,-2147483648);
run_signed_three(3,0,4,4,4,-2147483648,2147483647);
run_signed_three(-1,0,0,-2147483648,-2147483648,3,-7);
run_signed_three(-1,0,2,0,-2147483648,3,-7);
run_signed_three(-1,0,2,2,0,3,-7);
run_signed_three(3,1,3,2,2,3,-7);
run_signed_undef(3,0,0,-2147483648,1,3,-7);
run_signed_undef(3,0,0,-2147483648,1,-5,11);
run_signed_undef(3,0,0,-2147483648,1,2147483647,-2147483648);
run_signed_undef(3,0,0,-2147483648,1,-2147483648,2147483647);
run_signed_undef(3,0,2,0,1,3,-7);
run_signed_undef(3,0,2,0,1,-5,11);
run_signed_undef(3,0,2,0,1,2147483647,-2147483648);
run_signed_undef(3,0,2,0,1,-2147483648,2147483647);
run_signed_undef(-1,0,0,-2147483648,-2147483648,3,-7);
run_signed_undef(-1,0,2,0,-2147483648,3,-7);
signed_array(0,1,1,3,-7);
signed_array(0,1,1,-5,11);
signed_array(0,1,1,2147483647,-2147483648);
signed_array(0,1,1,-2147483648,2147483647);
signed_array(0,2,3,3,-7);
signed_array(0,2,3,-5,11);
signed_array(0,2,3,2147483647,-2147483648);
signed_array(0,2,3,-2147483648,2147483647);
signed_array(0,3,2,3,-7);
signed_array(0,3,2,-5,11);
signed_array(0,3,2,2147483647,-2147483648);
signed_array(0,3,2,-2147483648,2147483647);
signed_array(0,4,4,3,-7);
signed_array(0,4,4,-5,11);
signed_array(0,4,4,2147483647,-2147483648);
signed_array(0,4,4,-2147483648,2147483647);
signed_array(0,5,5,3,-7);
signed_array(0,5,5,-5,11);
signed_array(0,5,5,2147483647,-2147483648);
signed_array(0,5,5,-2147483648,2147483647);
signed_array(0,8,8,3,-7);
signed_array(0,8,8,-5,11);
signed_array(0,8,8,2147483647,-2147483648);
signed_array(0,8,8,-2147483648,2147483647);
signed_array(0,0,-2147483648,3,-7);
signed_array(0,0,-2147483648,-5,11);
signed_array(0,0,-2147483648,2147483647,-2147483648);
signed_array(0,0,-2147483648,-2147483648,2147483647);
signed_array(0,2,0,3,-7);
signed_array(0,2,0,-5,11);
signed_array(0,2,0,2147483647,-2147483648);
signed_array(0,2,0,-2147483648,2147483647);
signed_array(1,3,2,3,-7);
signed_array_no_zero_anchor(0,1,1,3,-7);
signed_array_no_zero_anchor(0,1,1,-5,11);
signed_array_no_zero_anchor(0,1,1,2147483647,-2147483648);
signed_array_no_zero_anchor(0,1,1,-2147483648,2147483647);
signed_array_no_zero_anchor(0,2,3,3,-7);
signed_array_no_zero_anchor(0,2,3,-5,11);
signed_array_no_zero_anchor(0,2,3,2147483647,-2147483648);
signed_array_no_zero_anchor(0,2,3,-2147483648,2147483647);
signed_array_no_zero_anchor(0,3,2,3,-7);
signed_array_no_zero_anchor(0,3,2,-5,11);
signed_array_no_zero_anchor(0,3,2,2147483647,-2147483648);
signed_array_no_zero_anchor(0,3,2,-2147483648,2147483647);
signed_array_no_zero_anchor(0,4,4,3,-7);
signed_array_no_zero_anchor(0,4,4,-5,11);
signed_array_no_zero_anchor(0,4,4,2147483647,-2147483648);
signed_array_no_zero_anchor(0,4,4,-2147483648,2147483647);
signed_array_no_zero_anchor(0,5,5,3,-7);
signed_array_no_zero_anchor(0,5,5,-5,11);
signed_array_no_zero_anchor(0,5,5,2147483647,-2147483648);
signed_array_no_zero_anchor(0,5,5,-2147483648,2147483647);
signed_array_no_zero_anchor(0,8,8,3,-7);
signed_array_no_zero_anchor(0,8,8,-5,11);
signed_array_no_zero_anchor(0,8,8,2147483647,-2147483648);
signed_array_no_zero_anchor(0,8,8,-2147483648,2147483647);
signed_array_no_zero_anchor(0,0,-2147483648,3,-7);
signed_array_no_zero_anchor(0,0,-2147483648,-5,11);
signed_array_no_zero_anchor(0,0,-2147483648,2147483647,-2147483648);
signed_array_no_zero_anchor(0,0,-2147483648,-2147483648,2147483647);
signed_array_no_zero_anchor(0,2,0,3,-7);
signed_array_no_zero_anchor(0,2,0,-5,11);
signed_array_no_zero_anchor(0,2,0,2147483647,-2147483648);
signed_array_no_zero_anchor(0,2,0,-2147483648,2147483647);
signed_array_no_zero_anchor(1,3,2,3,-7);
run_signed_mixed(3,0,1,1,1,3,-7);
run_signed_mixed(3,0,1,1,1,-5,11);
run_signed_mixed(3,0,1,1,1,2147483647,-2147483648);
run_signed_mixed(3,0,1,1,1,-2147483648,2147483647);
run_signed_mixed(3,0,2,3,1,3,-7);
run_signed_mixed(3,0,2,3,1,-5,11);
run_signed_mixed(3,0,2,3,1,2147483647,-2147483648);
run_signed_mixed(3,0,2,3,1,-2147483648,2147483647);
run_signed_mixed(3,0,3,2,1,3,-7);
run_signed_mixed(3,0,3,2,1,-5,11);
run_signed_mixed(3,0,3,2,1,2147483647,-2147483648);
run_signed_mixed(3,0,3,2,1,-2147483648,2147483647);
run_signed_mixed(3,0,4,4,1,3,-7);
run_signed_mixed(3,0,4,4,1,-5,11);
run_signed_mixed(3,0,4,4,1,2147483647,-2147483648);
run_signed_mixed(3,0,4,4,1,-2147483648,2147483647);
run_signed_mixed(3,0,5,5,1,3,-7);
run_signed_mixed(3,0,5,5,1,-5,11);
run_signed_mixed(3,0,5,5,1,2147483647,-2147483648);
run_signed_mixed(3,0,5,5,1,-2147483648,2147483647);
run_signed_mixed(3,0,8,8,1,3,-7);
run_signed_mixed(3,0,8,8,1,-5,11);
run_signed_mixed(3,0,8,8,1,2147483647,-2147483648);
run_signed_mixed(3,0,8,8,1,-2147483648,2147483647);
run_signed_mixed(-1,0,0,-2147483648,1,3,-7);
run_signed_mixed(-1,0,2,0,1,3,-7);
run_signed_mixed(3,1,3,2,1,3,-7);
run_signed_address_wrap(3,0,1,1,1,3,-7);
run_signed_address_wrap(3,0,1,1,1,-5,11);
run_signed_address_wrap(3,0,1,1,1,2147483647,-2147483648);
run_signed_address_wrap(3,0,1,1,1,-2147483648,2147483647);
run_signed_address_wrap(3,0,2,3,1,3,-7);
run_signed_address_wrap(3,0,2,3,1,-5,11);
run_signed_address_wrap(3,0,2,3,1,2147483647,-2147483648);
run_signed_address_wrap(3,0,2,3,1,-2147483648,2147483647);
run_signed_address_wrap(3,0,3,2,1,3,-7);
run_signed_address_wrap(3,0,3,2,1,-5,11);
run_signed_address_wrap(3,0,3,2,1,2147483647,-2147483648);
run_signed_address_wrap(3,0,3,2,1,-2147483648,2147483647);
run_signed_address_wrap(3,0,4,4,1,3,-7);
run_signed_address_wrap(3,0,4,4,1,-5,11);
run_signed_address_wrap(3,0,4,4,1,2147483647,-2147483648);
run_signed_address_wrap(3,0,4,4,1,-2147483648,2147483647);
run_signed_address_wrap(3,0,5,5,1,3,-7);
run_signed_address_wrap(3,0,5,5,1,-5,11);
run_signed_address_wrap(3,0,5,5,1,2147483647,-2147483648);
run_signed_address_wrap(3,0,5,5,1,-2147483648,2147483647);
run_signed_address_wrap(3,0,8,8,1,3,-7);
run_signed_address_wrap(3,0,8,8,1,-5,11);
run_signed_address_wrap(3,0,8,8,1,2147483647,-2147483648);
run_signed_address_wrap(3,0,8,8,1,-2147483648,2147483647);
run_signed_address_wrap(-1,0,0,-2147483648,1,3,-7);
run_signed_address_wrap(-1,0,2,0,1,3,-7);
run_signed_address_wrap(3,1,3,2,1,3,-7);
return 0; }
