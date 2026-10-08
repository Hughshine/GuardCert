"""Same-C loaded-header Horner RMW fixtures, including aliases and unavailable child reads."""
import re
import native_selected_regions as base

prior = base.prior
NAMES, MARKED, COUNTS = base.NAMES, base.MARKED, base.COUNTS
HELPERS = ["scripts/native_loaded_word_fixtures.py", *base.HELPERS]
function_body, printer_for_gcc, closing_brace = base.function_body, base.printer_for_gcc, base.closing_brace
INPUTS = [*prior.INPUTS, (0,2,3,2,-7,-1), (0,0,1001,99,-8,7)]
CASES = [(kind,*values) for kind in range(len(NAMES)) for values in INPUTS]


def source_text(markers=True):
    text = base.source_text(markers)
    # Existing source remains unchanged outside the newly generated fixture.
    text = text.replace("int i=start,j=77,k=88,fi=start,fj=77,fk=88;",
        "int i=start,j=77,k=88,fi=start,fj=77,fk=88;int H[2],root_only,*h;"
        "H[0]=n;H[1]=columns;h=H;root_only=n;"
        "if(components==-7){h=a;h[0]=n;h[1]=columns;}"
        "if(components==-8)h=&root_only;")
    text = text.replace("i<n", "i<*h+0").replace("j<columns", "j<h[1]+0")
    text = text[:text.rindex("int main(void)")] + "int main(void){" + "".join(
        "tensor_case("+",".join(map(prior.literal,case))+");" for case in CASES)+"return 0;}\n"
    return text


def model(case,column=False):
    kind,start,n,ld,columns,components,alpha=case
    array=[prior.word(3*x+1)for x in range(prior.SIZE)]
    alias=components==-7
    if alias: array[prior.CENTER:prior.CENTER+2]=[n,columns]
    public=[start,77,88]; first=public[:]
    if kind==4: array[900]=prior.word(array[900]+7)
    if not(kind==4 and start==4):
        for repeat in range(COUNTS[kind]):
            public=[start,77,88]
            while public[0]<(array[prior.CENTER]if alias else n):
                public[1]=0
                while public[1]<(array[prior.CENTER+1]if alias else columns):
                    public[2]=0
                    while public[2]<5:
                        i,j,k=public; major,minor=(j,i)if column else(i,j)
                        index=prior.CENTER+prior.word(prior.word(prior.word(major*ld)+minor)*5+k)
                        assert 0<=index<len(array),(case,index)
                        array[index]=prior.word(array[index]+alpha+(kind==5));public[2]+=1
                    public[1]+=1
                public[0]+=1
            if repeat==0:first=public[:]
    if kind==4:array[900]=prior.word(array[900]+11)
    return " ".join(map(str,[*case,*public,*first,107,211,*array]))+"\n"


def expected_output(column=False):
    return "".join(model(case,column)for case in CASES)


def dispatch_sites(body):
    for match in re.finditer(r"if \(\$[0-9]+\) \{",body):
        opening=match.end()-1;end=closing_brace(body,opening)
        no=re.match(r"\s*else\s*\{",body[end+1:])
        if no is None:continue
        fallback=end+1+no.end()-1;finish=closing_brace(body,fallback)
        if "$i <" in body[fallback:finish] and "$h" in body[fallback:finish] and "*($a" in body[opening:end]:
            yield opening,fallback
