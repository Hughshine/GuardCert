"""Run actual compiled affine nests with distinct and overlapping pointer views."""
from pathlib import Path
import hashlib, json, os, subprocess
import native_affine_nest as deep
import native_guardcert as unified
from native_zero_trip import function_body
ROOT = deep.ROOT
SOURCE = ROOT/'examples/native_affine_nest_multiple_pointers.c'
WORK = ROOT/'build/native-affine-nest-multiple-pointers'
COMPILER = unified.COMPILER
SIZE, CENTER = 32768, 4096
NAMES = ['multi_triangular2','multi_triangular3','multi_chain2','multi_undefined3','multi_descending3']
DEPTHS = [2,3,2,3,3]
SHAPES = [(-2,3,4,2),(0,3,2,2),(1,4,2,2),(-3,-1,4,2),
          (-2,3,1,2),(0,3,-1,2),(0,3,2,-4),(3,2,2,2),
          (0,3,0,0),(-5,3,8,8),(0,12,2,2)]
word, literal = deep.word, deep.literal

def full_inputs():
    rows = [(which,mode,start,n,m,p,alpha) for which in range(5)
            for mode in range(5) for start,n,m,p in SHAPES for alpha in [-7,2**31-1]]
    rows += [(which,5,start,n,2**31-1,-2**31,2**31-1) for which in range(5)
             for start,n in [(-2**31,-2**31),(2**31-1,2**31-1),(3,2)]]
    rows += [(3,mode,1,2,-3,2**31-1,-7) for mode in range(5)]
    return rows

def source_points(args):
    return deep.source_points(args)

def pointer_views(mode):
    if mode == 0: return [(0,CENTER),(1,CENTER),(2,CENTER)]
    if mode == 1: return [(0,CENTER)]*3
    if mode == 2: return [(0,CENTER),(0,CENTER+1),(0,CENTER+2)]
    if mode == 3: return [(0,CENTER),(0,CENTER+4096),(0,CENTER+8192)]
    if mode == 4: return [(0,CENTER),(0,CENTER+480),(0,CENTER+960)]
    return [(0,CENTER),(1,CENTER),(2,CENTER)]

def output_model(args,point_order=None):
    which,mode,_,_,_,_,alpha = args
    points,final = source_points(args)
    if point_order is not None:points=point_order
    arrays = [[word(3*x+1+17*slot) for x in range(SIZE)] for slot in range(3)]
    views = pointer_views(mode)
    for point in points:
        assert mode != 5, args
        i,j = point[:2]; k = point[2] if len(point)==3 else 0
        index = 512*i+32*j+k
        a,b,c = [arrays[slot] for slot,_ in views]
        ai,bi,ci = [offset+index for _,offset in views]
        assert min(ai,bi,ci)>=0 and max(ai,bi,ci)<SIZE, (args,point)
        value = b[bi]
        if DEPTHS[which]==3: value = word(value+c[ci])
        if which==2: value = word(value+a[ai+480])
        a[ai] = word(value+alpha+i-j+k)
    return ' '.join(map(str,[*args,*final,*arrays[0],*arrays[1],*arrays[2]]))+'\n'


def generate():
    text = '#include <stdio.h>\nint multi_i,multi_j,multi_k,multi_K,multi_L;\n'
    for which,name in enumerate(NAMES):
        prefix,p_used,alpha_used = '', 'p', 'alpha'
        if which==3:
            prefix='int local_p,local_alpha;if(start<n && n-1+m>0)local_p=p;if(start<n && n-1+m>0 && n-2+m+p>0)local_alpha=alpha;'
            p_used,alpha_used='local_p','local_alpha'
        index='512*i+32*j'+('+k' if DEPTHS[which]==3 else '')
        value='b['+index+']'
        if DEPTHS[which]==3: value+='+c['+index+']'
        if which==2: value+='+a['+index+'+480]'
        value+='+'+alpha_used+'+i-j'+('+k' if DEPTHS[which]==3 else '')
        leaf='a['+index+']='+value+';'
        if DEPTHS[which]==3:
            leaf='L='+('p-j' if which==4 else 'j+'+p_used)+';for(k=0;k<L;k++){'+leaf+'}'
        upper='m-i' if which==4 else 'i+m'
        loop='for(;i<n;i++){K='+upper+';for(j=0;j<K;j++){'+leaf+'}}'
        text+='void '+name+'(int *a,int *b,int *c,int start,int n,int m,int p,int alpha){int i=start,j=77,k=91,K=79,L=83;'+prefix+loop+'multi_i=i;multi_j=j;multi_k=k;multi_K=K;multi_L=L;}\n'
    text+='void multi_case(int which,int mode,int start,int n,int m,int p,int alpha){int A[32768],B[32768],C[32768],x;int *a,*b,*c;for(x=0;x<32768;x++){A[x]=3*x+1;B[x]=3*x+18;C[x]=3*x+35;}a=A+4096;b=B+4096;c=C+4096;'
    text+='if(mode==1){b=a;c=a;}if(mode==2){b=a+1;c=a+2;}if(mode==3){b=a+4096;c=a+8192;}if(mode==4){b=a+480;c=a+960;}if(mode==5){a=0;b=0;c=0;}\n'
    for which,name in enumerate(NAMES):
        text+='if(which=='+str(which)+')'+name+'(a,b,c,start,n,m,p,alpha);\n'
    text+='printf("%d %d %d %d %d %d %d %d %d %d %d %d",which,mode,start,n,m,p,alpha,multi_i,multi_j,multi_k,multi_K,multi_L);for(x=0;x<32768;x++)printf(" %d",A[x]);for(x=0;x<32768;x++)printf(" %d",B[x]);for(x=0;x<32768;x++)printf(" %d",C[x]);printf("\\n");}\nint main(void){\n'
    text+=''.join('multi_case('+','.join(map(literal,row))+');\n' for row in full_inputs())
    SOURCE.write_text(text+'return 0;}\n')


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def compile_run(name,mode,extra,expected,directory=WORK):
    work=directory/name; work.mkdir(parents=True,exist_ok=True)
    candidate=work/'candidate.sexp'; candidate.write_text('(interval (per-axis (schedule ((coordinate 99) ordinal) ())))\n')
    env={k:v for k,v in os.environ.items() if not k.startswith('GUARDCERT_')}
    env|={'GUARDCERT_AFFINE_MODE':mode,'GUARDCERT_AFFINE_PROFILE':'inferred',
          'GUARDCERT_AFFINE_DIAGNOSTICS':'1','GUARDCERT_LOOP_CANDIDATE':str(candidate)}|extra
    with (work/'compile.log').open('w') as log:
        result=subprocess.run([str(COMPILER),'-conf',str(COMPILER.parent/'compcert.ini'),
            '-stdlib',str(COMPILER.parent/'runtime'),'-dclight','-S','-o',str(work/'program.s'),
            str(SOURCE)],cwd=work,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=600)
    assert result.returncode==0,(name,(work/'compile.log').read_text()[-4000:])
    subprocess.run(['gcc','-no-pie',str(work/'program.s'),'-o',str(work/'program')],check=True,capture_output=True)
    with (work/'output.txt').open('w') as output:
        subprocess.run([str(work/'program')],stdout=output,text=True,check=True,timeout=180)
    assert (work/'output.txt').read_text()==expected,name
    dump_path=work/(SOURCE.stem+'.light.c'); dump=dump_path.read_text()
    functions={fn:{'guarded':function_body(dump,fn).count('for (')>depth,
                    'source_depth':depth,'emitted_loops':function_body(dump,fn).count('for (')}
               for fn,depth in zip(NAMES,DEPTHS)}
    return {'actual_calls':len(full_inputs()),'functions':functions,
            'all_three_arrays_and_public_controls_match_model':True,
            'clight_sha256':sha(dump_path),'assembly_sha256':sha(work/'program.s'),
            'output_sha256':sha(work/'output.txt'),'compile_log_sha256':sha(work/'compile.log')}


def main():
    generate(); WORK.mkdir(parents=True,exist_ok=True)
    stamp=unified.check_build()
    expected=''.join(output_model(row) for row in full_inputs())
    deep.checked_reference(SOURCE,WORK,expected) if hasattr(deep,'checked_reference') else unified.rectangular.common.checked_reference(SOURCE,WORK,expected)
    print('multiple-pointer complete-array reference passed',flush=True)
    configurations={}
    options=[('disabled','disabled',{}),('identity','identity',{}),('interchange','interchange',{}),
             ('tile-2-3','tile-2-3',{}),('wrong-witness','wrong-tiling-witness',{}),
             ('resource-limit','interchange',{'GUARDCERT_FM_ROWS':'0'})]
    for name,mode,extra in options:
        row=compile_run(name,mode,extra,expected)
        guarded={fn for fn,facts in row['functions'].items() if facts['guarded']}
        wanted=set() if name in ['disabled','wrong-witness','resource-limit'] else set(NAMES)
        if name in ['interchange','tile-2-3']: wanted-={'multi_chain2'}
        assert guarded==wanted,(name,guarded,wanted)
        configurations[name]=row
        (WORK/'partial-report.json').write_text(json.dumps(configurations,indent=2)+'\n')
        print(name,sorted(guarded),flush=True)
    (WORK/'report.json').write_text(json.dumps({'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'entrypoint':stamp['proved_entrypoint'],'source_sha256':sha(SOURCE),'configurations':configurations,
        'scope':'actual CompCert assembly; source-domain cross-pointer alias scans; complete arrays and public exits'},indent=2)+'\n')

if __name__=='__main__': main()
