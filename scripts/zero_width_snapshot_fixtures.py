"""Zero-width integration cases with an independent full-memory word model."""
SIZE, BASE = 9600, 4500
NAMES = ["loaded_snapshot_triangle", "loaded_snapshot_double", "plain_snapshot"]
CONTROLS = [(0, 0, 1, -13), (0, 1, 1, -13), (0, 3, 1, 0),
            (0, 5, 1, 7), (1, 3, 1, 0), (0, -1, 1, 0),
            (0, 3, 0, 0), (0, 3, 3, 2147483647), (0, 3, 16, 0),
            (0, 3, -1, 0), (1, 3, 2147483647, 0)]
CONTROLS += [(0, 1, 0, 0), (0, 2, 0, 0), (0, 4, 0, 0)]
CASES = [(slot, kind, *control) for slot in range(len(NAMES)) for kind in range(9)
         for control in CONTROLS if (kind != 6 or control[0] >= control[1])
         and (kind != 8 or control[2] <= 3)]


def word(value):
    return (value + 2**31) % 2**32 - 2**31


def source_text(marked=True):
    functions = []
    for slot, name in enumerate(NAMES):
        begin = "#pragma scop" if marked and slot < 2 else ""
        end = "#pragma endscop" if marked and slot < 2 else ""
        width = "2*i+*height" if slot == 1 else "i+*height"
        functions.append(f'''
void {name}(int *p,int *q,int *bound,int *height,int start,int a) {{
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
  int storage[{SIZE}],other[{SIZE}],value=n,height_value=m,x;
  int *p=storage+{BASE},*q=p,*bound=&value,*height=&height_value;
  for(x=0;x<{SIZE};++x) {{storage[x]=x;other[x]=3*x+7;}}
  if(kind==1) {{bound=p+31;height=p+30;}}
  if(kind==2) bound=p+32;
  if(kind==3) height=p+32;
  if(kind==4) q=p-4064;
  if(kind==5) q=other+{BASE};
  if(kind==7) height=q+4096;
  if(kind==8) height=bound;
  *bound=n;*height=m;
  if(kind==2 || kind==3) for(x=0;x<512;++x) q[4096+x]=-1-a;
  if(kind==6) height=(int *)0;
  public_context=31;
  if(slot==0) loaded_snapshot_triangle(p,q,bound,height,start,a);
  else if(slot==1) loaded_snapshot_double(p,q,bound,height,start,a);
  else plain_snapshot(p,q,bound,height,start,a);
  public_context+=public_i+public_j+public_k;
  printf("%d %d %d %d %d %d %d %d %d %d %d %d %d %d %d",slot,kind,start,n,m,a,
    public_i,public_j,public_k,public_rp,public_rq,public_snapshot,public_context,*bound,
    height ? *height : -777);
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
    q, qb = (storage, BASE-4064) if kind == 4 else (other, BASE) if kind == 5 else (storage, BASE)
    bound = BASE+31 if kind == 1 else BASE+32 if kind == 2 else None
    height_array = q if kind == 7 else storage
    height = BASE+30 if kind == 1 else BASE+32 if kind == 3 else qb+4096 if kind == 7 else None
    shared = kind == 8
    if bound is not None:
        storage[bound] = n
    if height is not None:
        height_array[height] = m
    if shared:
        n = m
    if kind in (2, 3):
        for x in range(512):
            q[qb+4096+x] = word(-1-a)
    rp, rq = storage[BASE], q[qb]
    i, j, k = start, 77, 91
    while i < (storage[bound] if bound is not None else n):
        assert kind != 6, "Only reached-source-defined inputs are included"
        current_height = height_array[height] if height is not None else n if shared else m
        k = word((2*i if slot == 1 else i)+current_height)
        j = 0
        while j < k:
            write, read = BASE+32+64*i+j, qb+4096+64*i+j
            assert 0 <= write < SIZE and 0 <= read < SIZE
            storage[write] = word(q[read]+a)
            j += 1
        i = word(i+1)
    storage[BASE], q[qb] = word(rp+17), word(rq+19)
    final_bound = storage[bound] if bound is not None else n
    final_height = -777 if kind == 6 else height_array[height] if height is not None else n if shared else m
    return [i, j, k, rp, rq, 123, 31+i+j+k, final_bound, final_height], storage, other


def expected_output():
    rows = []
    for slot, kind, start, n, m, a in CASES:
        controls, storage, other = model(slot, kind, start, n, m, a)
        rows.append(" ".join(map(str, [slot, kind, start, n, m, a]+controls+
            [v for pair in zip(storage, other) for v in pair]))+"\n")
    return "".join(rows)
