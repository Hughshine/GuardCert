"""Actual marked multi-array C, public exits, shared views and an independent word model."""
from native_selected_regions import function_body, printer_for_gcc, closing_brace

SIZE = 1024
NAMES = ["multi_pair", "multi_shift", "multi_unmarked", "multi_twice", "multi_context", "multi_unsupported"]
MARKED = [1, 1, 0, 2, 1, 1]
INSTALLED = [1, 1, 0, 2, 1, 0]
INPUTS = [
    (0, 0, 2, 2, 3, 8, 1, 7), (0, 0, 3, 2, 5, 8, 2, 2147483647),
    (1, 0, 2, 2, 3, 8, 1, 7), (2, 0, 2, 2, 3, 8, 1, 7),
    (3, 0, 2, 1, 1, 8, 1, 7), (4, 0, 2, 2, 5, 8, 1, 7),
    (5, 0, 0, 99, 99, 0, -99, 7), (0, 0, 2, 0, 3, 8, 1, 7),
    (0, 0, 2, 1, 0, 8, 1, 7), (0, 1, 3, 1, 1, 8, 1, 7),
    (0, 0, 9, 1, 1, 8, 1, 7), (0, 0, 1, 1, 1, 1000, 1, 7),
    (0, 0, 1, 1, 6, 8, 1, 7), (0, 0, 2, 1, 1, 8, -1, 7),
    (0, 0, 1, 1, 1, 8, 9, 7), (0, 4, 5, 1, 1, 8, 1, 7),
]
CASES = [(kind, *case) for kind in range(len(NAMES)) for case in INPUTS]


def word(value):
    return (value + 2**31) % 2**32 - 2**31


def loop(body, column=False):
    major, minor = ("j", "i") if column else ("i", "j")
    index = f"(({major}*ld)+{minor})*5+k"
    return f"for(i=start;i<n;i++)for(j=0;j<m;j++)for(k=0;k<c;k++){{{body(index, major, minor)}}}"


def pair(index, _major, _minor):
    return f"a[{index}]=b[{index}]+alpha;b[{index}]=a[{index}]+alpha;"


def shift(_index, major, minor):
    a = f"(({major}*ld)+({minor}+1))*5+k"
    b = f"(({major}*ld)+({minor}+q))*5+k"
    c = f"(({major}*ld)+{minor})*5+k"
    return f"a[{a}]=b[{b}]+q+alpha;d[{c}]=a[{a}]+alpha;"


def source_text(column=False, markers=True):
    def marked(text):
        return "\n#pragma scop\n"+text+"\n#pragma endscop\n" if markers else text
    signature = "int*a,int*b,int*d,int start,int n,int m,int c,int ld,int q,int alpha"
    prefix = "int i=start,j=77,k=88;"
    suffix = "public_i=i;public_j=j;public_k=k;"
    plain = loop(pair, column)
    shifted = loop(shift, column)
    functions = [
        f"void multi_pair({signature}){{{prefix}{marked(plain)}{suffix}}}",
        f"void multi_shift({signature}){{{prefix}{marked(shifted)}{suffix}}}",
        f"void multi_unmarked({signature}){{{prefix}{plain}{suffix}}}",
        f"void multi_twice({signature}){{{prefix}{marked(plain)}first_i=i;first_j=j;first_k=k;"
        f"arena[900]=arena[900]+11;{marked(plain)}{suffix}}}",
        f"void multi_context({signature}){{{prefix}arena[900]=arena[900]+7;"
        f"if(start==4){{arena[901]=arena[901]+13;}}else{{{marked(plain)}}}"
        f"arena[900]=arena[900]+17;{suffix}}}",
        f"void multi_unsupported({signature}){{{prefix}"
        f"{marked(loop(lambda index,major,minor: f'a[{index}]=b[{index}]^alpha;',column))}{suffix}}}",
    ]
    case = """void multi_case(int kind,int alias,int start,int n,int m,int c,int ld,int q,int alpha){
      int x,*a,*b,*d;for(x=0;x<1024;x++)arena[x]=3*x+1;
      a=arena+64;b=arena+(alias==1?64:alias==2?65:alias==3?80:320);d=arena+(alias==4?64:640);
      if(alias==5){a=0;b=0;d=0;}
      first_i=start;first_j=77;first_k=88;
      switch(kind){CALLS}
      printf("%d %d %d %d %d %d %d %d %d %d %d %d %d %d %d ",kind,alias,start,n,m,c,ld,q,alpha,
        public_i,public_j,public_k,first_i,first_j,first_k);
      for(x=0;x<1024;x++)printf("%d ",arena[x]);printf("\\n");}
    """.replace("CALLS", "".join(f"case {i}:{name}(a,b,d,start,n,m,c,ld,q,alpha);break;" for i,name in enumerate(NAMES)))
    main = "int main(void){"+"".join("multi_case("+",".join(map(str,case))+");" for case in CASES)+"return 0;}\n"
    return "extern int printf(const char*,...);int arena[1024],public_i,public_j,public_k,first_i,first_j,first_k;\n"+"\n".join(functions)+case+main


def bases(alias):
    return 64, {1: 64, 2: 65, 3: 80}.get(alias, 320), 64 if alias == 4 else 640


def indices(kind, i, j, k, ld, q, column):
    major, minor = (j, i) if column else (i, j)
    if kind == 1:
        return word(word(word(major*ld)+word(minor+1))*5+k), word(word(word(major*ld)+word(minor+q))*5+k), word(word(word(major*ld)+minor)*5+k)
    index = word(word(word(major*ld)+minor)*5+k)
    return index, index, index


def model(case, column=False):
    kind, alias, start, n, m, components, ld, q, alpha = case
    memory = [word(3*x+1) for x in range(SIZE)]
    a,b,d = bases(alias)
    public = [start,77,88]
    first = public[:]
    if kind == 4:
        memory[900] = word(memory[900]+7)
    if kind == 4 and start == 4:
        memory[901] = word(memory[901]+13)
    else:
        for repeat in range(2 if kind == 3 else 1):
            public = [start,77,88]
            while public[0] < n:
                public[1] = 0
                while public[1] < m:
                    public[2] = 0
                    while public[2] < components:
                        ai,bi,di = indices(kind,*public,ld,q,column)
                        assert alias != 5
                        assert all(0 <= index < SIZE for index in [a+ai,b+bi,d+di])
                        if kind == 5:
                            memory[a+ai] = word(memory[b+bi] ^ alpha)
                        else:
                            memory[a+ai] = word(memory[b+bi] + (q if kind == 1 else 0) + alpha)
                            target = d+di if kind == 1 else b+bi
                            memory[target] = word(memory[a+ai]+alpha)
                        public[2] += 1
                    public[1] += 1
                public[0] += 1
            if kind == 3 and repeat == 0:
                first = public[:]
                memory[900] = word(memory[900]+11)
    if kind == 4:
        memory[900] = word(memory[900]+17)
    return " ".join(map(str,[*case,*public,*first,*memory]))+" \n"


def expected_output(column=False):
    return "".join(model(case,column) for case in CASES)


def expected_path(case, column=False, installed=True):
    kind,alias,start,n,m,c,ld,q,_alpha = case
    calls = 0 if kind == 4 and start == 4 else 2 if kind == 3 else 1
    if not installed or not INSTALLED[kind]:
        return [0,0,calls]
    setup = start==0 and 1<=n<=8 and 1<=m<=8 and 1<=c<=5 and 1<=ld<1000
    if kind == 1:
        setup = setup and -8<=q<=8 and q>=0 and (n if column else m)+max(1,q)<=ld
    else:
        setup = setup and (n if column else m)<=ld
    if not setup:
        return [0,0,calls]
    a,b,d = bases(alias)
    touched = {"a":set(),"b":set(),"d":set()}
    for i in range(n):
        for j in range(m):
            for k in range(c):
                ai,bi,di=indices(kind,i,j,k,ld,q,column)
                touched["a"].add(a+ai);touched["b"].add(b+bi)
                if kind==1:touched["d"].add(d+di)
    groups=list(touched.values())
    separate = all(not left.intersection(right) for i,left in enumerate(groups) for right in groups[i+1:])
    return [calls,0,0] if separate else [0,calls,calls]
