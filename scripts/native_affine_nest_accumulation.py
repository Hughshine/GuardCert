"""Run true read-modify-write accumulation with an independently modeled order."""
from native_sources import atomic_write_text
import json,os,subprocess
from pathlib import Path
import affine_inner_interchange_candidate as producer
import external_affine_candidate as syntax
import native_guardcert as compiler
from native_zero_trip import function_body
ROOT=compiler.ROOT;WORK=ROOT/'build/native-affine-nest-accumulation'
SOURCE=ROOT/'examples/native_affine_nest_accumulation.c'
SIZE,CENTER=2048,256

def word(value):return (value+2**31)%2**32-2**31
def literal(value):return '(-2147483647-1)' if value==-2**31 else str(value)
def inputs():
    shapes=[(0,3,2,3),(-2,2,4,2),(1,4,2,2),(3,2,2**31-1,-2**31),
            (0,3,-4,-2**31),(0,3,2,0),(0,3,2,-3),(0,12,2,2),(0,3,9,3)]
    return [(mode,*shape) for mode in range(5) for shape in shapes]+[
        (5,-2**31,-2**31,2**31-1,-2**31),(5,2**31-1,2**31-1,2**31-1,-2**31),(5,3,2,2**31-1,-2**31)]

def views(mode):
    return ([(0,CENTER)]*3 if mode==1 else [(0,CENTER),(0,CENTER+1),(0,CENTER+2)] if mode==2
            else [(0,CENTER),(0,CENTER+512),(0,CENTER+1024)] if mode==3
            else [(0,CENTER),(0,CENTER+32),(0,CENTER+64)] if mode==4
            else [(0,CENTER),(1,CENTER),(2,CENTER)])

def points_and_exit(args):
    _,start,n,m,p=args;points=[];i,j,k,K,L=start,77,91,79,83
    while i<n:
        K=word(i+m);j=0
        while j<K:
            L=p;k=0
            while k<L:points.append((i,j,k));k+=1
            j+=1
        i+=1
    return points,(i,j,k,K,L)

def model(args,order=None):
    mode,*_=args;points,final=points_and_exit(args)
    if order is not None:points=sorted(points,key=order)
    arrays=[[word((3*x+1) if slot==0 else (5*x-7) if slot==1 else (2**31-1-11*x))
             for x in range(SIZE)] for slot in range(3)]
    a,b,c=views(mode)
    for i,j,k in points:
        assert mode!=5
        ai,bi,ci=a[1]+32*i+j,b[1]+32*i+k,c[1]+32*k+j
        assert min(ai,bi,ci)>=0 and max(ai,bi,ci)<SIZE
        arrays[a[0]][ai]=word(arrays[a[0]][ai]+word(arrays[b[0]][bi]*arrays[c[0]][ci]))
    return ' '.join(map(str,[*args,*final,*arrays[0],*arrays[1],*arrays[2]]))+'\n'

def generate():
    text='#include <stdio.h>\nint out_i,out_j,out_k,out_K,out_L;\n'
    text+='void affine_accumulation(int *a,int *b,int *c,int start,int n,int m,int p){int i=start,j=77,k=91,K=79,L=83;for(;i<n;i++){K=i+m;for(j=0;j<K;j++){L=p;for(k=0;k<L;k++){a[32*i+j]=a[32*i+j]+b[32*i+k]*c[32*k+j];}}}out_i=i;out_j=j;out_k=k;out_K=K;out_L=L;}\n'
    text+='void accumulation_case(int mode,int start,int n,int m,int p){int A[2048],B[2048],C[2048],x;int *a,*b,*c;for(x=0;x<2048;x++){A[x]=3*x+1;B[x]=5*x-7;C[x]=2147483647-11*x;}a=A+256;b=B+256;c=C+256;'
    text+='if(mode==1){b=a;c=a;}if(mode==2){b=a+1;c=a+2;}if(mode==3){b=a+512;c=a+1024;}if(mode==4){b=a+32;c=a+64;}if(mode==5){a=0;b=0;c=0;}affine_accumulation(a,b,c,start,n,m,p);'
    text+='printf("%d %d %d %d %d %d %d %d %d %d",mode,start,n,m,p,out_i,out_j,out_k,out_K,out_L);for(x=0;x<2048;x++)printf(" %d",A[x]);for(x=0;x<2048;x++)printf(" %d",B[x]);for(x=0;x<2048;x++)printf(" %d",C[x]);printf("\\n");}\nint main(void){\n'
    text+=''.join('accumulation_case('+','.join(map(literal,row))+');\n' for row in inputs())
    atomic_write_text(SOURCE,text+'return 0;}\n')

def compile_run(name,extra,expected,export=False):
    work=WORK/name;work.mkdir(parents=True,exist_ok=True)
    env={k:v for k,v in os.environ.items() if not k.startswith('GUARDCERT_')}
    env|={'GUARDCERT_AFFINE_PROFILE':'inferred','GUARDCERT_AFFINE_DIAGNOSTICS':'1'}|extra
    with (work/'compile.log').open('w') as log:
        subprocess.run([str(compiler.COMPILER),'-conf',str(compiler.COMPILER.parent/'compcert.ini'),
            '-stdlib',str(compiler.COMPILER.parent/'runtime'),'-dclight','-S','-o',str(work/'program.s'),
            str(SOURCE)],cwd=work,env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=600)
    subprocess.run(['gcc','-no-pie',str(work/'program.s'),'-o',str(work/'program')],check=True,capture_output=True)
    with (work/'output.txt').open('w') as output:
        subprocess.run([str(work/'program')],check=True,stdout=output,timeout=180)
    assert (work/'output.txt').read_text()==expected,name
    dump=work/(SOURCE.stem+'.light.c')
    return {'actual_calls':len(inputs()),'guarded':function_body(dump.read_text(),'affine_accumulation').count('for (')>3,
            'assembly_sha256':compiler.sha(work/'program.s'),'clight_sha256':compiler.sha(dump),
            'compile_log_sha256':compiler.sha(work/'compile.log'),'output_sha256':compiler.sha(work/'output.txt'),
            'all_arrays_and_public_controls_match_model':True}

def main():
    generate();WORK.mkdir(parents=True,exist_ok=True);stamp=compiler.check_build()
    expected=''.join(model(row) for row in inputs())
    compiler.rectangular.common.checked_reference(SOURCE,WORK,expected)
    ikj=lambda point:(point[0],point[2],point[1])
    blocked=lambda point:(point[0]//2,point[2]//3,point[0],point[2],point[1])
    for row in inputs():
        if row[0] in [0,3]:
            assert model(row)==model(row,ikj),row
            assert model(row)==model(row,blocked),row
    witness=(1,0,3,2,3);assert model(witness)!=model(witness,ikj)
    requests=WORK/'requests';requests.mkdir(exist_ok=True)
    configurations={'export':compile_run('export',{'GUARDCERT_AFFINE_MODE':'disabled',
        'GUARDCERT_AFFINE_REQUEST_DIR':str(requests)},expected)}
    accepted=['identity','inner-interchange','inner-interchange-parametric','interchange-tile','partition-interchange-tile',
              'parametric-tile','partition-parametric-tile']
    for name,mode in [('identity','identity'),('inner-interchange','inner-interchange'),
                      ('inner-interchange-parametric','inner-interchange-parametric'),
                      ('interchange-tile','interchange-tile'),('partition-interchange-tile','partition-interchange-tile'),
                      ('parametric-tile','parametric-tile'),('partition-parametric-tile','partition-parametric-tile'),
                      ('wrong-parametric-witness','wrong-parametric-witness'),('dependent-header-tile','dependent-header-tile'),
                      ('wrong-first-tile','wrong-first-tile'),('wrong-witness-tile','wrong-witness-tile'),
                      ('wrong-map','wrong-map'),('resource-limit','inner-interchange')]:
        candidate=WORK/(name+'.sexp')
        if mode=='identity':
            choices=[]
            for path in sorted(requests.glob('*.sexp')):
                fields={x[0]:x[1] for x in syntax.parse(path.read_text())[1:]}
                if len(fields['axes'])==3:choices.append(['request',path.stem,fields['source']])
            candidate.write_text(syntax.render(['choices',*choices])+'\n')
        else:producer.generate(requests,candidate,wrong=mode=='wrong-map',
                               mode='inner-interchange' if mode=='wrong-map' else mode)
        extra={'GUARDCERT_AFFINE_MODE':'external','GUARDCERT_AFFINE_CANDIDATE':str(candidate)}
        if name=='resource-limit':extra['GUARDCERT_FM_ROWS']='0'
        row=compile_run(name,extra,expected)
        assert row['guarded']==(name in accepted),(name,row['guarded'])
        configurations[name]=row|{'candidate_sha256':compiler.sha(candidate)}
        print(name,row['guarded'],flush=True)
    (WORK/'report.json').write_text(json.dumps({'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'entrypoint':stamp['proved_entrypoint'],'source_sha256':compiler.sha(SOURCE),
        'configurations':configurations,'unchecked_alias_interchange_word_model_witness':list(witness),
        'scope':'actual assembly; repeated accumulation, signed32 data wrap, complete arrays and public controls'},
        indent=2)+'\n')

if __name__=='__main__':main()
