"""Measure kernel CPU time separately from correctness and branch regressions."""
import argparse,json,os,re,statistics,subprocess,time
from pathlib import Path
import native_affine_nest_accumulation as fixture
import affine_inner_interchange_candidate as producer
import external_affine_candidate as syntax
from native_zero_trip import function_body
from native_affine_nest_multiple_pointers_paths import marked_source

WORK=fixture.ROOT/'build/native-affine-nest-accumulation-cost'
LAYOUT='pointers'
MODES=['source','identity','inner-interchange','inner-interchange-parametric','interchange-tile','partition-interchange-tile']

def layout_text(text):
    if LAYOUT=='pointers':return text
    text=text.replace('int *a,int *b,int *c,','int *a,')
    text=text.replace('b[32*i+k]','a[512+32*i+k]').replace('c[32*k+j]','a[1024+32*k+j]')
    text=text.replace('affine_accumulation(A+256,B+256,C+256,','affine_accumulation(A+256,')
    return text.replace('C[x]=2147483647-11*x;}',
        'C[x]=2147483647-11*x;}for(x=0;x<512;x++){A[512+x]=5*x-7;A[1024+x]=2147483647-11*x;}')

def generate():
    source=WORK/'cost.c'
    prefix=fixture.SOURCE.read_text().split('void accumulation_case',1)[0]
    prefix+='\n#include <stdlib.h>\n#include <time.h>\nint A[2048],B[2048],C[2048];\n'
    main='int main(int argc,char **argv){int x,r,repetitions=argc>1?atoi(argv[1]):100;clock_t before,after;unsigned checksum=0;for(x=0;x<2048;x++){A[x]=3*x+1;B[x]=5*x-7;C[x]=2147483647-11*x;}before=clock();for(r=0;r<repetitions;r++)affine_accumulation(A+256,B+256,C+256,0,4,2,3);after=clock();for(x=0;x<2048;x++)checksum=checksum+(unsigned)A[x];printf("%d %lu %lu %u %d %d %d %d %d\\n",repetitions,(unsigned long)(after-before),(unsigned long)CLOCKS_PER_SEC,checksum,out_i,out_j,out_k,out_K,out_L);return 0;}\n'
    source.write_text(layout_text(prefix+main));return source

def environment(extra):
    return {k:v for k,v in os.environ.items() if not k.startswith('GUARDCERT_')}|{
        'GUARDCERT_AFFINE_PROFILE':'inferred','GUARDCERT_AFFINE_DIAGNOSTICS':'1'}|extra

def compile_one(source,name,extra):
    compiler=fixture.compiler.COMPILER;started=time.monotonic()
    with (WORK/(name+'.log')).open('w') as log:
        subprocess.run([str(compiler),'-conf',str(compiler.parent/'compcert.ini'),
            '-stdlib',str(compiler.parent/'runtime'),'-dclight','-S','-o',str(WORK/(name+'.s')),
            str(source)],cwd=WORK,env=environment(extra),stdout=log,stderr=subprocess.STDOUT,
            check=True,timeout=600)
    seconds=time.monotonic()-started;dump=WORK/'cost.light.c'
    guarded=function_body(dump.read_text(),'affine_accumulation').count('for (')>3
    assert guarded==(name!='source'),name
    saved=WORK/(name+'.light.c');saved.write_text(dump.read_text())
    subprocess.run(['gcc','-no-pie',str(WORK/(name+'.s')),'-o',str(WORK/name)],check=True,capture_output=True)
    return {'compile_wall_seconds':seconds,'guarded':guarded,
        'assembly_sha256':fixture.compiler.sha(WORK/(name+'.s')),
        'executable_sha256':fixture.compiler.sha(WORK/name),
        'clight_sha256':fixture.compiler.sha(saved),'compile_log_sha256':fixture.compiler.sha(WORK/(name+'.log'))}

def checksum(repetitions):
    a=[3*x+1 for x in range(2048)]
    if LAYOUT=='windows':
        for x in range(512):a[512+x]=5*x-7;a[1024+x]=2**31-1-11*x
    for i,j,k in fixture.points_and_exit((0,0,4,2,3))[0]:
        a[256+32*i+j]+=repetitions*(5*(256+32*i+k)-7)*(2**31-1-11*(256+32*k+j))
    return sum(a)%2**32

def sample(name,repetitions):
    output=subprocess.check_output([str(WORK/name),str(repetitions)],text=True,timeout=60)
    count,ticks,frequency,value,*controls=map(int,output.split())
    assert count==repetitions and value==checksum(repetitions) and controls==[4,5,3,5,3],output
    assert frequency>0 and ticks>=0
    return {'repetitions':count,'ticks':ticks,'ticks_per_second':frequency,
            'seconds_per_call':ticks/frequency/count,'output':output.strip()}

def observe_fast(name):
    dump=(WORK/(name+'.light.c')).read_text().rsplit('\nint main(',1)[0]
    dump=re.sub(r'^int main\([^;\n]*\);\n','',dump,flags=re.M)
    source=marked_source(dump+'\nint main(void)\n{\nreturn 0;\n}\n',['affine_accumulation'])
    source+='\nint main(void){int x;for(x=0;x<2048;x++){A[x]=3*x+1;B[x]=5*x-7;C[x]=2147483647-11*x;}guard_fast[0]=0;guard_fallback[0]=0;affine_accumulation(A+256,B+256,C+256,0,4,2,3);return guard_fast[0]!=1 || guard_fallback[0]!=0;}\n'
    path=WORK/(name+'-diagnostic.c');path.write_text(layout_text(source))
    binary=WORK/(name+'-diagnostic')
    subprocess.run(['gcc','-O0','-fwrapv','-Wno-builtin-declaration-mismatch',str(path),'-o',str(binary)],check=True,capture_output=True)
    subprocess.run([str(binary)],check=True,timeout=60)
    return {'fast':1,'fallback':0,'diagnostic_source_sha256':fixture.compiler.sha(path)}

def main():
    global WORK,LAYOUT
    parser=argparse.ArgumentParser();parser.add_argument('--layout',choices=['pointers','windows'],default='pointers')
    LAYOUT=parser.parse_args().layout
    if LAYOUT=='windows':WORK=fixture.ROOT/'build/native-affine-nest-accumulation-window-cost'
    WORK.mkdir(parents=True,exist_ok=True);stamp=fixture.compiler.check_build();source=generate()
    requests=WORK/'requests';requests.mkdir(exist_ok=True)
    rows={'source':compile_one(source,'source',{'GUARDCERT_AFFINE_MODE':'disabled',
          'GUARDCERT_AFFINE_REQUEST_DIR':str(requests)})}
    for name in MODES[1:]:
        candidate=WORK/(name+'.sexp')
        if name=='identity':
            choices=[]
            for path in sorted(requests.glob('*.sexp')):
                fields={x[0]:x[1] for x in syntax.parse(path.read_text())[1:]}
                if len(fields['axes'])==3:choices.append(['request',path.stem,fields['source']])
            assert choices;candidate.write_text(syntax.render(['choices',*choices])+'\n')
        else:producer.generate(requests,candidate,mode=name)
        row=compile_one(source,name,{'GUARDCERT_AFFINE_MODE':'external',
                                   'GUARDCERT_AFFINE_CANDIDATE':str(candidate)})
        row.update({'candidate_sha256':fixture.compiler.sha(candidate),'path_diagnostic':observe_fast(name)})
        rows[name]=row;print(name,'compiled',row['compile_wall_seconds'],flush=True)
    for name,row in rows.items():
        count=1000;calibration=[]
        for _ in range(5):
            trial=sample(name,count);calibration.append(trial)
            elapsed=trial['ticks']/trial['ticks_per_second']
            if elapsed>=0.08:break
            count=min(50000000,max(count*2,int(count*0.12/max(elapsed,0.00001))))
        samples=[sample(name,count) for _ in range(5)]
        row.update({'calibration':calibration,'samples':samples,
            'median_seconds_per_call':statistics.median(x['seconds_per_call'] for x in samples)})
        print(name,row['median_seconds_per_call'],'seconds/call',flush=True)
    baseline=rows['source']['median_seconds_per_call'];assert baseline>0
    for row in rows.values():row['relative_cpu_cost']=row['median_seconds_per_call']/baseline
    (WORK/'report.json').write_text(json.dumps({'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'source_sha256':fixture.compiler.sha(source),'layout':LAYOUT,'configurations':rows,
        'scope':'empirical CPU cost of one small disjoint accumulation kernel, n=4,m=2,p=3; separate from correctness call counts'},indent=2)+'\n')

if __name__=='__main__':main()
