"""Defined empty-source inputs, NULL body pointers and an undefined body word."""
SIZE=6000
NAMES=["empty_triangle","empty_double","unmarked_empty","undefined_body_word"]
CONTROLS=[(0,-2,9,7),(0,0,9,7),(0,1,0,7),(0,1,-1,7),(0,2,-1,7),
    (0,3,-2,7),(0,3,-4,7),(0,4,-6,7),(0,3,-7,7),(0,3,1,7),
    (0,3,0,7),(0,5,-16,7),(0,3,-2147483648,7),(1,3,-2,7),
    (3,3,1,7),(-1,0,-4,7),(0,3,-2,2147483647)]


def empty(slot,start,n,m):
    slope=2 if slot==1 else 1
    signed_m=m if STYLE=="add"else-m
    return start>=n or max(slope*start+signed_m,slope*(n-1)+signed_m)<=0


STYLE="add"


def configure(style):
    global STYLE,CASES
    assert style in("add","subtract")
    STYLE=style
    controls=CONTROLS if style=="add"else[(start,n,2147483647 if m==-2147483648 else-m,a)
        for start,n,m,a in CONTROLS]
    CASES=[(slot,kind,*control)for slot in range(4)for kind in range(4)for control in controls
        if(slot!=3 or empty(slot,*control[:3]))
        and(kind not in(1,3)or empty(slot,*control[:3]))
        and(kind!=2 or control[0]>=control[1])]


configure("add")


def word(value):
    return(value+2**31)%2**32-2**31


def source_text(marked=True):
    functions=[]
    for slot,name in enumerate(NAMES):
        begin="#pragma scop"if marked and slot!=2 else ""
        end="#pragma endscop"if marked and slot!=2 else ""
        operator="+"if STYLE=="add"else"-"
        width=("2*i"if slot==1 else"i")+operator+"*height"
        scalar="bodyword"if slot==3 else "a"
        declaration="int bodyword;"if slot==3 else ""
        functions.append(f'''
void {name}(int *p,int *q,int *bound,int *height,int start,int a){{
  int i=start,j=77,k=91; {declaration}
  {begin}
  for(;i<*bound;++i){{
    k={width};
    for(j=0;j<k;++j)p[32+64*i+j]=q[4096+64*i+j]+{scalar};
  }}
  {end}
  public_i=i;public_j=j;public_k=k;
}}
''')
    calls="\n".join("run_case("+",".join(map(str,case))+");"for case in CASES)
    return '''#include <stdio.h>
int public_i,public_j,public_k,public_context;
'''+"".join(functions)+f'''
void run_case(int slot,int kind,int start,int n,int m,int a){{
  int storage[{SIZE}],other[{SIZE}],value=n,height_value=m,x;
  int *p=storage,*q=other,*bound=&value,*height=&height_value;
  for(x=0;x<{SIZE};++x){{storage[x]=x;other[x]=3*x+7;}}
  if(kind==3){{bound=storage+32;height=other+4096;}}
  *bound=n;*height=m;
  if(kind==1){{p=(int *)0;q=(int *)0;}}
  if(kind==2)height=(int *)0;
  public_context=31;
  if(slot==0)empty_triangle(p,q,bound,height,start,a);
  else if(slot==1)empty_double(p,q,bound,height,start,a);
  else if(slot==2)unmarked_empty(p,q,bound,height,start,a);
  else undefined_body_word(p,q,bound,height,start,a);
  public_context+=public_i+public_j+public_k;
  printf("%d %d %d %d %d %d %d %d %d %d %d %d",slot,kind,start,n,m,a,
    public_i,public_j,public_k,public_context,*bound,height?*height:-777);
  for(x=0;x<{SIZE};++x)printf(" %d %d",storage[x],other[x]);
  printf("\\n");
}}
int main(void){{
{calls}
return 0;
}}
'''


def model(slot,kind,start,n,m,a):
    storage,other=list(range(SIZE)),[3*x+7 for x in range(SIZE)]
    if kind==3:
        storage[32],other[4096]=n,m
    i,j,k=start,77,91
    while i<n:
        assert kind!=2
        k=word((2*i if slot==1 else i)+(m if STYLE=="add"else-m))
        j=0
        while j<k:
            assert kind!=1 and slot!=3
            write,read=32+64*i+j,4096+64*i+j
            assert 0<=write<SIZE and 0<=read<SIZE
            storage[write]=word(other[read]+a)
            j+=1
        i=word(i+1)
    return[i,j,k,word(31+i+j+k),n,-777 if kind==2 else m],storage,other


def expected_output():
    rows=[]
    for case in CASES:
        public,storage,other=model(*case)
        row=list(case)+public+[value for pair in zip(storage,other)for value in pair]
        rows.append(" ".join(map(str,row)))
    return"\n".join(rows)+"\n"
