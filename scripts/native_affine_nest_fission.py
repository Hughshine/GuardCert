"""Exercise actual deep affine multi-statement programs and imported fission."""
import json,os,subprocess
from pathlib import Path
import external_affine_candidate as producer
import native_affine_nest_multiple_pointers as memory
from native_zero_trip import function_body
ROOT=memory.ROOT;WORK=ROOT/'build/native-affine-nest-fission'
SOURCE=ROOT/'examples/native_affine_nest_fission.c';COMPILER=memory.COMPILER
NAMES=['fission_independent2','fission_pointwise2','fission_future2','fission_independent3']
DEPTHS=[2,2,2,3]
SIZE,CENTER=memory.SIZE,memory.CENTER
word,literal=memory.word,memory.literal


def full_inputs():
    result=[(which,mode,start,n,m,p,alpha) for which in range(4) for mode in range(5)
            for start,n,m,p in memory.SHAPES+[(0,3,40,2)] for alpha in [-7,2**31-1]]
    result += [(which,5,start,n,2**31-1,-2**31,2**31-1) for which in range(4)
               for start,n in [(-2**31,-2**31),(2**31-1,2**31-1),(3,2)]]
    return result


def source_points(args):
    which,_,start,n,m,p,_=args;points=[];final=[start,77,91,79,83]
    for i in range(start,n):
        upper=word(i+m);final[1],final[3]=0,upper
        for j in range(max(0,upper)):
            if DEPTHS[which]==2:points.append((i,j))
            else:
                inner=word(j+p);final[2],final[4]=0,inner
                for k in range(max(0,inner)):points.append((i,j,k))
                final[2]=max(0,inner)
        final[1]=max(0,upper)
    final[0]=max(start,n);return points,final


def output_model(args,order='source'):
    which,mode,_,_,_,_,alpha=args
    points,final=source_points(args);beta=word(alpha+5)
    arrays=[[word(3*x+1+17*slot) for x in range(SIZE)] for slot in range(3)]
    views=memory.pointer_views(mode)
    operations=([(operation,point) for point in points for operation in [0,1]] if order=='source' else
                [(operation,point) for operation in ([1,0] if order=='reverse-fission' else [0,1]) for point in points])
    for operation,point in operations:
        assert mode!=5,args
        i,j=point[:2];k=point[2] if len(point)==3 else 0;index=512*i+32*j+k
        a,b,c=[arrays[slot] for slot,_ in views];ai,bi,ci=[offset+index for _,offset in views]
        if operation==0:a[ai]=word(b[bi]+alpha+i-j+k)
        else:
            read=b[bi] if which in [0,3] else a[ai+(480 if which==2 else 0)]
            c[ci]=word(read+beta+i-j+k)
    return ' '.join(map(str,[*args,*final,*arrays[0],*arrays[1],*arrays[2]]))+'\n'


def generate():
    text='#include <stdio.h>\nint multi_i,multi_j,multi_k,multi_K,multi_L;\n'
    for which,name in enumerate(NAMES):
        index='512*i+32*j'+('+k' if DEPTHS[which]==3 else '')
        suffix='+i-j'+('+k' if DEPTHS[which]==3 else '')
        first='a['+index+']=b['+index+']+alpha'+suffix+';'
        read='b['+index+']' if which in [0,3] else 'a['+index+('+480' if which==2 else '')+']'
        leaf=first+'c['+index+']='+read+'+beta'+suffix+';'
        if DEPTHS[which]==3:leaf='L=j+p;for(k=0;k<L;k++){'+leaf+'}'
        loop='for(;i<n;i++){K=i+m;for(j=0;j<K;j++){'+leaf+'}}'
        text+='void '+name+'(int *a,int *b,int *c,int start,int n,int m,int p,int alpha){int i=start,j=77,k=91,K=79,L=83,beta=alpha+5;'+loop+'multi_i=i;multi_j=j;multi_k=k;multi_K=K;multi_L=L;}\n'
    harness=memory.SOURCE.read_text().split('void multi_case',1)[1].split('int main(void)',1)[0]
    for old,new in zip(memory.NAMES,NAMES):harness=harness.replace(old,new)
    import re
    harness=re.sub(r'if\(which==4\)[^;]+;\n','',harness)
    text+='void multi_case'+harness+'int main(void){\n'
    text+=''.join('multi_case('+','.join(map(literal,row))+');\n' for row in full_inputs())
    SOURCE.write_text(text+'return 0;}\n')


def export_requests():
    requests=WORK/'requests';requests.mkdir(parents=True,exist_ok=True)
    env={k:v for k,v in os.environ.items() if not k.startswith('GUARDCERT_')}
    env|={'GUARDCERT_AFFINE_MODE':'disabled','GUARDCERT_AFFINE_PROFILE':'inferred','GUARDCERT_AFFINE_REQUEST_DIR':str(requests)}
    with (WORK/'export.log').open('w') as log:
        result=subprocess.run([str(COMPILER),'-conf',str(COMPILER.parent/'compcert.ini'),
            '-stdlib',str(COMPILER.parent/'runtime'),'-S','-o',str(WORK/'source.s'),str(SOURCE)],
            cwd=WORK,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=600)
    assert result.returncode==0,(WORK/'export.log').read_text()[-4000:]
    return requests


def compile_run(name,candidate,expected,extra):
    work=WORK/name;work.mkdir(parents=True,exist_ok=True)
    env={k:v for k,v in os.environ.items() if not k.startswith('GUARDCERT_')}
    env|={'GUARDCERT_AFFINE_MODE':'external','GUARDCERT_AFFINE_PROFILE':'inferred',
          'GUARDCERT_AFFINE_CANDIDATE':str(candidate),'GUARDCERT_AFFINE_DIAGNOSTICS':'1'}|extra
    with (work/'compile.log').open('w') as log:
        result=subprocess.run([str(COMPILER),'-conf',str(COMPILER.parent/'compcert.ini'),
            '-stdlib',str(COMPILER.parent/'runtime'),'-dclight','-S','-o',str(work/'program.s'),str(SOURCE)],
            cwd=work,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=600)
    assert result.returncode==0,(work/'compile.log').read_text()[-4000:]
    subprocess.run(['gcc','-no-pie',str(work/'program.s'),'-o',str(work/'program')],check=True,capture_output=True)
    with (work/'output.txt').open('w') as output:subprocess.run([str(work/'program')],stdout=output,text=True,check=True,timeout=180)
    assert (work/'output.txt').read_text()==expected,name
    dump_path=work/(SOURCE.stem+'.light.c');dump=dump_path.read_text()
    functions={fn:{'guarded':function_body(dump,fn).count('for (')>depth,
                   'emitted_loops':function_body(dump,fn).count('for (')} for fn,depth in zip(NAMES,DEPTHS)}
    return {'actual_calls':len(full_inputs()),'functions':functions,'candidate_sha256':memory.sha(candidate),
            'all_arrays_and_public_controls_match_model':True,'clight_sha256':memory.sha(dump_path),
            'assembly_sha256':memory.sha(work/'program.s'),'output_sha256':memory.sha(work/'output.txt'),
            'compile_log_sha256':memory.sha(work/'compile.log')}


def main():
    generate();WORK.mkdir(parents=True,exist_ok=True);stamp=memory.unified.check_build();requests=export_requests()
    expected=''.join(output_model(row) for row in full_inputs())
    memory.unified.rectangular.common.checked_reference(SOURCE,WORK,expected)
    witnesses={
        'forward-future':((2,0,0,3,2,2,-7),'fission'),
        'reverse-pointwise':((1,0,0,3,2,2,-7),'reverse-fission'),
        'reverse-outside-guard':((2,0,0,3,40,2,-7),'reverse-fission')}
    for args,order in witnesses.values():assert output_model(args)!=output_model(args,order),(args,order)
    configurations={}
    for name,mode,extra in [('identity','identity',{}),('fission','fission',{}),
            ('reverse-fission','reverse-fission',{}),('resource-limit','fission',{'GUARDCERT_FM_ROWS':'0'})]:
        candidate=WORK/(name+'.sexp');producer.generate(requests,candidate,mode,1)
        row=compile_run(name,candidate,expected,extra)
        guarded={fn for fn,facts in row['functions'].items() if facts['guarded']}
        wanted={'identity':set(NAMES),'fission':set(NAMES)-{'fission_future2'},
                'reverse-fission':{'fission_independent2','fission_independent3','fission_future2'},'resource-limit':set()}[name]
        assert guarded==wanted,(name,guarded,wanted)
        configurations[name]=row
        (WORK/'partial-report.json').write_text(json.dumps(configurations,indent=2)+'\n')
        print(name,sorted(guarded),flush=True)
    (WORK/'report.json').write_text(json.dumps({'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'entrypoint':stamp['proved_entrypoint'],'source_sha256':memory.sha(SOURCE),'configurations':configurations,
        'counterexample_word_model_inputs':witnesses,
        'scope':'actual CompCert assembly; imported multi-statement fission; independent, pointwise, and future dependencies'},indent=2)+'\n')

if __name__=='__main__':main()
