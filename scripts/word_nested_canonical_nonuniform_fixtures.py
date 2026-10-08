"""Nonuniform affine-map C and independent sequential modular-word execution."""
from native_selected_regions import function_body, printer_for_gcc, closing_brace

SIZE = 1024
NAMES = ["loaded_pair", "loaded_unmarked", "loaded_twice", "loaded_context", "loaded_unsupported"]
INSTALLED = [1, 0, 2, 1, 0]
INPUTS = [
    (0, 0, 2, 3, 1, 16), (0, 0, 3, 2, 2147483647, 16),
    (1, 0, 2, 3, 1, 16), (2, 0, 2, 3, 1, 16),
    (0, 1, 2, 2, 3, 16), (0, 0, 9, 1, 1, 16),
    (6, 0, 0, 99, 7, 16), (7, 0, 2, 0, 7, 16),
    (0, 4, 5, 1, 3, 16),
]
CASES = [(kind, *case) for kind in range(len(NAMES)) for case in INPUTS]


def word(value):
    return (value + 2**31) % 2**32 - 2**31


def source_text(column=False, markers=True, variable_stride=False):
    assert not column and not variable_stride
    index = f"{'j' if column else 'i'}*{'ld' if variable_stride else '16'}+{'i' if column else 'j'}"
    normal = f"a[{index}]=b[i*16+(j+1)]+alpha;b[{index}]=a[{index}]+alpha;"
    unsupported = f"a[{index}]=b[{index}]^alpha;"

    def loop(body):
        return "for(;i<*h+0;i++)for(j=0;j<*k+0;j++){"+body+"}"

    def marked(body):
        return "\n#pragma scop\n"+body+"\n#pragma endscop\n" if markers else body

    signature = "int*a,int*b,int*h,int*k,int start,int alpha,int ld"
    prefix = "int i=start,j=77;"
    suffix = "public_i=i;public_j=j;"
    body = loop(normal)
    call = "a,b,h,k,start,alpha,ld"
    functions = [
        f"void loaded_pair({signature}){{{prefix}{marked(body)}{suffix}}}",
        f"void loaded_unmarked({signature}){{{prefix}{body}{suffix}}}",
        f"void loaded_twice({signature}){{{prefix}{marked(body)}first_i=i;first_j=j;"
        f"arena[900]=arena[900]+11;i=start;{marked(body)}{suffix}}}",
        f"void loaded_context({signature}){{{prefix}arena[900]=arena[900]+7;"
        f"if(start==4){{arena[901]=arena[901]+13;}}else{{{marked(body)}}}"
        f"arena[900]=arena[900]+17;{suffix}}}",
        f"void loaded_unsupported({signature}){{{prefix}{marked(loop(unsupported))}{suffix}}}",
    ]
    case = """void loaded_case(int kind,int alias,int start,int n,int m,int alpha,int ld){
      int x,*a,*b,*h,*k;for(x=0;x<1024;x++)arena[x]=3*x+1;
      a=arena+64;b=arena+(alias==1?64:alias==2?65:320);h=arena;k=arena+1;
      if(alias==3)k=b;if(alias==4)h=b;if(alias==5){h=b;k=b;}
      *h=n;*k=m;
      if(alias==6){a=0;b=0;k=0;}if(alias==7){a=0;b=0;}
      first_i=start;first_j=77;
      switch(kind){CALLS}
      printf("%d %d %d %d %d %d %d %d %d %d %d ",kind,alias,start,n,m,alpha,ld,
        public_i,public_j,first_i,first_j);
      for(x=0;x<1024;x++)printf("%d ",arena[x]);printf("\\n");}
    """.replace("CALLS", "".join(f"case {i}:{name}({call});break;" for i,name in enumerate(NAMES)))
    main = "int main(void){"+"".join("loaded_case("+",".join(map(str,case))+");" for case in CASES)+"return 0;}\n"
    return "extern int printf(const char*,...);int arena[1024],public_i,public_j,first_i,first_j;\n"+"\n".join(functions)+case+main


def initial(case):
    kind, alias, start, n, m, alpha, ld = case
    memory = [word(3*x+1) for x in range(SIZE)]
    a, b = 64, {1: 64, 2: 65}.get(alias, 320)
    h, k = (b if alias in [4, 5] else 0), (b if alias in [3, 5] else 1)
    memory[h], memory[k] = word(n), word(m)
    return memory, a, b, h, k


def point_index(i, j, column=False, variable_stride=False, ld=16):
    major, minor = (j, i) if column else (i, j)
    return word(word(major*(ld if variable_stride else 16))+minor)


def header_accepts(case, memory, a, b, h, k, column, variable_stride):
    _kind, _alias, start, _n, _m, _alpha, ld = case
    n, m = memory[h], memory[k]
    if start != 0 or n < 0:
        return False
    if n == 0:
        return True
    if m < 0:
        return False
    return all(base+point_index(i,j,column,variable_stride,ld) not in [h,k]
               for i in range(n) for j in range(m) for base in [a,b])


def expected_path(case, memory, a, b, h, k, column=False, variable_stride=False, installed=True):
    kind, _alias, start, _n, _m, _alpha, ld = case
    if not installed or not INSTALLED[kind]:
        return [0, 0, 0, 1, 0]
    n, m = memory[h], memory[k]
    if not header_accepts(case,memory,a,b,h,k,column,variable_stride):
        return [0, 0, 0, 1, 0]
    if n == 0:
        return [1, 0, 0, 0, 1]
    stride = ld if variable_stride else 16
    setup = 1 <= n <= 8 and 1 <= m <= 8 and (not variable_stride or 1 <= ld < 1000)
    setup = setup and (n if column else m) <= stride
    if not setup:
        return [1, 0, 1, 0, 0]
    indices = {point_index(i,j,column,variable_stride,ld) for i in range(n) for j in range(m)}
    separate = not {a+x for x in indices}.intersection({b+x for x in indices | {x+1 for x in indices}})
    return [1, 1, 0, 0, 0] if separate else [1, 0, 1, 0, 0]


def model(case, column=False, variable_stride=False, installed=True):
    kind, alias, start, _n, _m, alpha, ld = case
    memory, a, b, h, k = initial(case)
    public, first = [start,77], [start,77]
    paths = [0]*5
    if kind == 3:
        memory[900] = word(memory[900]+7)
    if kind == 3 and start == 4:
        memory[901] = word(memory[901]+13)
    else:
        for repeat in range(2 if kind == 2 else 1):
            public[0] = start
            paths = [x+y for x,y in zip(paths,expected_path(case,memory,a,b,h,k,column,variable_stride,installed))]
            count = 0
            while public[0] < memory[h]:
                assert alias != 6, (case,"unavailable child read")
                public[1] = 0
                while public[1] < memory[k]:
                    assert alias not in [6,7], (case,"unavailable array read")
                    index = point_index(*public,column,variable_stride,ld)
                    assert 0 <= a+index < SIZE and 0 <= b+index < SIZE, (case,public,index)
                    if kind == 4:
                        memory[a+index] = word(memory[b+index] ^ alpha)
                    else:
                        memory[a+index] = word(memory[b+index+1]+alpha)
                        memory[b+index] = word(memory[a+index]+alpha)
                    public[1] += 1
                    count += 1
                    assert count < 10000, (case,"unexpected runaway source")
                public[0] += 1
            if kind == 2 and repeat == 0:
                first = public[:]
                memory[900] = word(memory[900]+11)
    if kind == 3:
        memory[900] = word(memory[900]+17)
    return " ".join(map(str,[*case,*public,*first,*memory]))+" \n", paths


def expected_output(column=False, variable_stride=False):
    return "".join(model(case,column,variable_stride)[0] for case in CASES)
