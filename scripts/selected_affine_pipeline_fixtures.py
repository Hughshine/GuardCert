"""Marked real C and an independent sequential word/memory model."""
SIZE = 2048
NAMES = ["triangular2", "triangular3", "descending3", "chain2", "unmarked2", "two_regions"]
CASES = [(which, mode, start, n, m, p, alpha)
         for which in range(6) for mode in range(4)
         for start, n, m, p, alpha in
         [(0, 3, 2, 2, 3), (1, 4, 1, 1, -7), (-1, 2, 3, 2, 3),
          (0, 3, -2, 1, 3), (3, 2, 2, 2, 3), (0, 6, 1, 1, 3),
          (0, 3, 2, 2, 2147483647)]]


def word(value):
    return (value + 2**31) % 2**32 - 2**31


def literal(value):
    return "(-2147483647-1)" if value == -2**31 else str(value)


def source_text(marked=True):
    def region(loop, selected=True):
        return ("\n#pragma scop\n" + loop + "\n#pragma endscop\n") if marked and selected else "\n" + loop + "\n"
    first = "for(;i<n;i++){K=i+m;for(j=0;j<K;j++){a[64*i+8*j]=b[64*i+8*j]+alpha+i-j;}}"
    deep = "for(;i<n;i++){K=i+m;for(j=0;j<K;j++){L=j+p;for(k=0;k<L;k++){a[64*i+8*j+k]=b[64*i+8*j+k]+c[64*i+8*j+k]+alpha+i-j+k;}}}"
    descending = deep.replace("K=i+m", "K=m-i").replace("L=j+p", "L=p-j")
    chain = first.replace("b[64*i+8*j]+alpha", "b[64*i+8*j]+a[64*i+8*j+56]+alpha")
    second = first.replace("a[64*i+8*j]=b[64*i+8*j]", "b[64*i+8*j]=c[64*i+8*j]")
    source = "#include <stdio.h>\nint out_i,out_j,out_k,out_K,out_L,out_context;\n"
    for name, body in zip(NAMES, [first, deep, descending, chain, first, first]):
        source += f"void {name}(int *a,int *b,int *c,int start,int n,int m,int p,int alpha){{int i=start,j=77,k=91,K=79,L=83;"
        source += region(body, name != "unmarked2")
        if name == "two_regions":
            source += "i=start;\n" + region(second)
        source += "out_i=i;out_j=j;out_k=k;out_K=K;out_L=L;out_context=a[0]+17;\n}\n"
    source += "void run_case(int which,int mode,int start,int n,int m,int p,int alpha){int A[2048],B[2048],C[2048],x;int *a,*b,*c;for(x=0;x<2048;x++){A[x]=3*x+1;B[x]=3*x+18;C[x]=3*x+35;}a=A+256;b=B+256;c=C+256;if(mode==1){b=a;c=a;}if(mode==2){b=a+1;c=a+2;}if(mode==3){b=a+1024;c=a+1280;}\n"
    for which, name in enumerate(NAMES):
        source += f"if(which=={which}){name}(a,b,c,start,n,m,p,alpha);\n"
    source += 'printf("%d %d %d %d %d %d %d %d %d %d %d %d %d",which,mode,start,n,m,p,alpha,out_i,out_j,out_k,out_K,out_L,out_context);for(x=0;x<2048;x++)printf(" %d",A[x]);for(x=0;x<2048;x++)printf(" %d",B[x]);for(x=0;x<2048;x++)printf(" %d",C[x]);printf("\\n");}\nint main(void){\n'
    source += "\n".join("run_case(" + ",".join(map(literal, case)) + ");" for case in CASES)
    return source + "\nreturn 0;}\n"


def output_model(case):
    which, mode, start, n, m, p, alpha = case
    arrays = [[3*x+offset for x in range(SIZE)] for offset in (1, 18, 35)]
    ports = [(0, 256), (1, 256), (2, 256)]
    if mode == 1:
        ports = [(0, 256)]*3
    elif mode == 2:
        ports = [(0, 256), (0, 257), (0, 258)]
    elif mode == 3:
        ports = [(0, 256), (0, 1280), (0, 1536)]
    def load(port, position):
        array, offset = ports[port]
        assert 0 <= offset+position < SIZE
        return arrays[array][offset+position]
    def store(port, position, value):
        array, offset = ports[port]
        assert 0 <= offset+position < SIZE
        arrays[array][offset+position] = word(value)
    i, j, k, K, L = start, 77, 91, 79, 83
    for pass_index in range(2 if which == 5 else 1):
        i = start
        while i < n:
            K = word(m-i if which == 2 else i+m)
            j = 0
            while j < K:
                if which in (1, 2):
                    L = word(p-j if which == 2 else j+p)
                    k = 0
                    while k < L:
                        position = 64*i+8*j+k
                        store(0, position, load(1, position)+load(2, position)+alpha+i-j+k)
                        k += 1
                else:
                    position = 64*i+8*j
                    if pass_index:
                        store(1, position, load(2, position)+alpha+i-j)
                    else:
                        store(0, position, load(1, position)+(load(0, position+56) if which == 3 else 0)+alpha+i-j)
                j += 1
            i += 1
    values = [*case, i, j, k, K, L, word(load(0, 0)+17)] + sum(arrays, [])
    return " ".join(map(str, values))+"\n"


def expected_output():
    return "".join(map(output_model, CASES))
