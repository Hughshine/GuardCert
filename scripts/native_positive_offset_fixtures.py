"""Actual loaded bounds +1, including wrapped bounds and changing header aliases."""
import native_loaded_word_fixtures as historical

prior = historical.prior
NAMES, MARKED, COUNTS = historical.NAMES, historical.MARKED, historical.COUNTS
function_body, printer_for_gcc = historical.function_body, historical.printer_for_gcc
closing_brace, dispatch_sites = historical.closing_brace, historical.dispatch_sites
MAX, MIN = 2**31-1, -2**31
# Tuple fields are start, raw root, stride, raw child, mode, scalar.
INPUTS = [
    (0,2,31,1,5,7), (0,1,3,1,5,MAX), (0,1,31,1,5,MIN),
    (0,2,31,1,5,0), (0,31,32,31,5,0), (0,31,32,31,5,7),
    (0,0,2,0,5,0), (0,32,1,0,5,7), (1,2,31,1,5,3),
    (4,2,31,1,5,7), (0,2,31,-1,5,7), (0,2,31,MAX,5,7),
    (0,2,31,MIN,5,7), (0,-1,1001,99,99,MAX),
    (0,MAX,1001,99,99,MAX), (0,MIN,1001,99,99,MAX),
    (0,-1,1001,99,-8,7), (0,MAX,1001,99,-8,7),
    (0,MIN,1001,99,-8,7), (0,0,3,2,5,7),
]
CASES = [(kind,*values) for kind in range(len(NAMES)) for values in INPUTS]
# Unsupported alpha+1 is checked with separate headers above. Avoid a source
# whose positive update would make aliasing loop bounds grow without limit.
CASES += [(kind,0,1,3,1,-7,-1) for kind in range(5)]
CASES += [(kind,0,1,3,1,-7,0) for kind in range(5)]
CASES += [(kind,0,1,3,2,-7,0) for kind in range(5)]
HELPERS = ["scripts/native_positive_offset_fixtures.py", *historical.HELPERS]


def source_text(markers=True):
    text = historical.source_text(markers)
    text = text.replace("i<*h+0", "i<*h+1").replace("j<h[1]+0", "j<h[1]+1")
    # Raw zero now denotes one iteration, so it must receive a valid output
    # pointer. A nonpositive wrapped root still cannot touch output or child.
    text = text.replace("(n==0?0:A+128)", "(n+1<=0?0:A+128)")
    return text[:text.rindex("int main(void)")] + "int main(void){" + "".join(
        "tensor_case("+",".join(map(prior.literal,case))+");" for case in CASES)+"return 0;}\n"


def model(case,column=False):
    kind,start,n,ld,columns,components,alpha=case
    array=[prior.word(3*x+1) for x in range(prior.SIZE)]
    alias=components==-7
    if alias: array[prior.CENTER:prior.CENTER+2]=[n,columns]
    public=[start,77,88]; first=public[:]
    if kind==4: array[900]=prior.word(array[900]+7)
    if not(kind==4 and start==4):
        for repeat in range(COUNTS[kind]):
            public=[start,77,88]
            while public[0]<prior.word((array[prior.CENTER] if alias else n)+1):
                public[1]=0
                while public[1]<prior.word((array[prior.CENTER+1] if alias else columns)+1):
                    public[2]=0
                    while public[2]<5:
                        i,j,k=public; major,minor=(j,i) if column else(i,j)
                        index=prior.CENTER+prior.word(prior.word(prior.word(major*ld)+minor)*5+k)
                        assert 0<=index<len(array),(case,index)
                        array[index]=prior.word(array[index]+alpha+(kind==5));public[2]+=1
                    public[1]+=1
                public[0]+=1
            if repeat==0: first=public[:]
    if kind==4: array[900]=prior.word(array[900]+11)
    return " ".join(map(str,[*case,*public,*first,107,211,*array]))+"\n"


def expected_output(column=False):
    return "".join(model(case,column) for case in CASES)
