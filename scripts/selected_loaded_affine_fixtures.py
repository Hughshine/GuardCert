"""Complete C inputs and an independent word model for actual loaded-affine regions."""
SIZE, BASE = 9600, 4500
NAMES = ["loaded_triangle", "loaded_parameter", "plain_loaded"]
CONTROLS = [(0, 0, 1, -13), (0, 1, 1, -13), (0, 3, 1, 0),
            (0, 5, 1, 7), (1, 3, 1, 0), (0, -1, 1, 0),
            (0, 3, 0, 0), (0, 3, 3, 2147483647), (0, 3, 16, 0)]
CASES = [(slot, kind, *control) for slot in range(len(NAMES))
         for kind in range(5) for control in CONTROLS]


def word(value):
    return (value + 2**31) % 2**32 - 2**31


def source_text(marked=True):
    functions = []
    for slot, name in enumerate(NAMES):
        begin = "#pragma scop" if marked and slot < 2 else ""
        end = "#pragma endscop" if marked and slot < 2 else ""
        width = "i+m" if slot == 1 else "2*i+1"
        functions.append(f'''
void {name}(int *p,int *q,int *bound,int start,int m,int a) {{
  int i=start,j=77,k=91,rp,rq,snapshot=123;
  {begin}
  rq=*q;rp=*p;
  for(;i<*bound;++i) {{
    k={width};
    for(j=0;j<k;++j) p[32+64*i+j]=q[4096+64*i+j]+a;
  }}
  {end}
  public_i=i;public_j=j;public_k=k;public_rp=rp;public_rq=rq;public_snapshot=snapshot;
  p[0]=rp+17;q[0]=rq+19;
}}
''')
    calls = "\n".join("run_case(" + ",".join(map(str, case)) + ");" for case in CASES)
    return '''#include <stdio.h>
int public_i,public_j,public_k,public_rp,public_rq,public_snapshot,public_context;
''' + "".join(functions) + f'''
void run_case(int slot,int kind,int start,int n,int m,int a) {{
  int storage[{SIZE}],other[{SIZE}],value=n,x;
  int *p=storage+{BASE},*q=p,*bound=&value;
  for(x=0;x<{SIZE};++x) {{storage[x]=x;other[x]=3*x+7;}}
  if(kind==1) bound=p+31;
  if(kind==2) bound=p+32;
  if(kind==3) q=p-4064;
  if(kind==4) q=other+{BASE};
  *bound=n;
  if(kind==2) for(x=0;x<512;++x) q[4096+x]=-1-a;
  public_context=31;
  if(slot==0) loaded_triangle(p,q,bound,start,m,a);
  else if(slot==1) loaded_parameter(p,q,bound,start,m,a);
  else plain_loaded(p,q,bound,start,m,a);
  public_context+=public_i+public_j+public_k;
  printf("%d %d %d %d %d %d %d %d %d %d %d %d %d %d",slot,kind,start,n,m,a,
    public_i,public_j,public_k,public_rp,public_rq,public_snapshot,public_context,*bound);
  for(x=0;x<{SIZE};++x) printf(" %d %d",storage[x],other[x]);
  printf("\\n");
}}
int main(void) {{
{calls}
return 0;
}}
'''


def model(slot, kind, start, n, m, a):
    storage, other = list(range(SIZE)), [3*x+7 for x in range(SIZE)]
    q, qb = (storage, BASE-4064) if kind == 3 else (other, BASE) if kind == 4 else (storage, BASE)
    bound = BASE+31 if kind == 1 else BASE+32 if kind == 2 else None
    if bound is not None:
        storage[bound] = n
    if kind == 2:
        for x in range(512):
            q[qb+4096+x] = word(-1-a)
    rp, rq = storage[BASE], q[qb]
    i, j, k = start, 77, 91
    while i < (storage[bound] if bound is not None else n):
        k = i+m if slot == 1 else 2*i+1
        j = 0
        while j < k:
            storage[BASE+32+64*i+j] = word(q[qb+4096+64*i+j]+a)
            j += 1
        i += 1
    storage[BASE], q[qb] = word(rp+17), word(rq+19)
    final_bound = storage[bound] if bound is not None else n
    header = [slot, kind, start, n, m, a, i, j, k, rp, rq, 123, 31+i+j+k, final_bound]
    return " ".join(map(str, header + [v for pair in zip(storage, other) for v in pair])) + "\n"


def expected_output():
    return "".join(model(*case) for case in CASES)
