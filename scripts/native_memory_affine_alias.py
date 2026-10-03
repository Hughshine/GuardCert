"""Check complete C programs with affine address scans and private guard state."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
from native_zero_trip import function_body
from native_memory_recursive import loop_template
ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'examples/native_memory_affine_alias.c'
RESOURCE_SOURCE=ROOT/'examples/native_memory_affine_alias_resources.c'
COMPILER=ROOT/'build/compcert-memory-unified/ccomp'
WORK=ROOT/'build/native-memory-affine-alias'
SIZE=4600
NAMES=['affine_stride','affine_reverse','affine_constant','affine_chain','affine_three','affine_wrap']
def word(x): return (x+2**31)%2**32-2**31

def indices(which,i):
    if which==0:return [('p',2*i),('q',3*i+1)]
    if which==1:return [('p',i),('q',1023-i)]
    if which==2:return [('p',i),('q',1)]
    if which==3:return [('p',i),('q',i),('q',i+1)]
    if which==4:return [('p',2*i),('q',3*i+1),('r',4*i+2)]
    return [('p',2*i),('q',1)]

def physical(kind):
    return {'p':(0,0),'q':((0,1) if kind==1 else (0,1500) if kind==2 else (0,0) if kind==3 else (1,0)),
            'r':((0,3000) if kind==2 else (0,0) if kind==3 else (1,0) if kind==4 else (2,0))}

def separated(args):
    which,kind,start,n,_,_=args
    cells={cell for i in range(start,n) for cell in indices(which,i)}
    locations=physical(kind)
    mapped=[(locations[p][0],locations[p][1]+j) for p,j in cells]
    return len(set(mapped))==len(cells)

def output_model(args,reverse=False,fission=False):
    which,kind,start,n,alpha,beta=args
    arrays=[[3*i+1 for i in range(SIZE)],[5*i+7 for i in range(SIZE)],[7*i+11 for i in range(SIZE)]]
    bindings=physical(kind)
    def get(pointer,index):
        block,base=bindings[pointer];assert 0<=base+index<SIZE,(args,pointer,index)
        return arrays[block][base+index]
    def put(pointer,index,value):
        block,base=bindings[pointer];assert 0<=base+index<SIZE,(args,pointer,index)
        arrays[block][base+index]=word(value)
    order=[(i,site) for i in range(start,n) for site in range(2 if which in [3,4] else 1)]
    if reverse:order.sort(key=lambda x:(-x[0],x[1]))
    if fission:order.sort(key=lambda x:(x[1],x[0]))
    for i,site in order:
        if which==0:put('p',2*i,get('q',3*i+1)*alpha+beta)
        elif which==1:put('p',i,get('q',1023-i)*alpha+beta)
        elif which==2:put('p',i,get('q',1)*alpha+beta)
        elif which==3:
            if site==0:put('p',i,get('q',i)*alpha+beta)
            else:put('q',i+1,get('p',i)+get('q',i+1)*beta)
        elif which==4:
            if site==0:put('p',2*i,get('q',3*i+1)*alpha+get('r',4*i+2)*beta)
            else:put('r',4*i+2,get('p',2*i)+i)
        else:put('p',2*i,get('q',1)*alpha+beta)
    return ' '.join(map(str,args+[max(start,n)]+[x for row in zip(*arrays) for x in row]))+'\n'

def full_inputs():
    result=[[w,k,0,n,-7,11] for w in range(6) for k in range(5) for n in [0,1,2,9,33,129,257,343]]
    for w in range(6):
        result += [[w,0,1,33,-2147483648,2147483647],[w,0,0,129,-2147483648,2147483647],
                   [w,5,0,0,3,-7],[w,5,0,-2147483648,3,-7]]
    return result


def check_build():
    stamp=json.loads((COMPILER.parent/'.guard-build.json').read_text())
    assert stamp['proved_entrypoint']=='GuardMemoryUnifiedCompiler.compile_memory_unified_regions'
    assert stamp['compiler_sha256']==hashlib.sha256(COMPILER.read_bytes()).hexdigest()
    for path,digest in (stamp['proof_sources']|stamp['native_sources']).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    proof=json.loads((ROOT/'build/guard-memory-proof-report.json').read_text())
    assert proof['affine_loop_alias_guard_clight_execution_proved']
    assert proof['affine_loop_alias_guard_csem_asm_route_proved']
    assert proof['stateful_core_instantiated_in_clight_projected_region_contract']
    assert proof['stateful_core_global_axioms']==[]
    return stamp

def resource_model(reads,kind,n):
    a,b=[3*i+1 for i in range(1024)],[5*i+7 for i in range(1024)]
    q=a if kind else b
    for i in range(n): a[2*i]=word(reads*q[3*i+1])
    return ' '.join(map(str,[reads,kind,n,n]+[x for row in zip(a,b) for x in row]))+'\n'

def resource_inputs():
    return [(reads,kind,n) for reads in [31,32,64] for kind in range(2) for n in [0,1,129]]

def reference_output():
    return ''.join(output_model(a) for a in full_inputs())+'undefined 0 0\nundefined -2147483648 0\n'

def checked_reference(source,work,expected):
    work.mkdir(parents=True,exist_ok=True)
    subprocess.run(['gcc','-O0','-fwrapv',str(source),'-o',str(work/'reference')],check=True)
    actual=subprocess.check_output([str(work/'reference')],text=True)
    assert actual==expected,source
    (work/'reference-output.txt').write_text(actual)
    return actual

def compile_run(source,work,syntax,extra,reference):
    work.mkdir(parents=True,exist_ok=True)
    candidate=work/'candidate.sexp';candidate.write_text(syntax+'\n')
    result=subprocess.run([str(COMPILER),'-conf',str(COMPILER.parent/'compcert.ini'),
        '-stdlib',str(COMPILER.parent/'runtime'),'-dclight','-S','-o',str(work/'affine.s'),str(source)],
        cwd=work,env=os.environ|{'GUARDCERT_LOOP_CANDIDATE':str(candidate)}|extra,
        text=True,capture_output=True,check=True,timeout=600)
    (work/'compiler-output.txt').write_text(result.stdout+result.stderr)
    subprocess.run(['gcc',str(work/'affine.s'),'-o',str(work/'affine')],check=True)
    actual=subprocess.check_output([str(work/'affine')],text=True,timeout=120)
    assert actual==reference,work
    (work/'output.txt').write_text(actual)
    dump=work/(source.stem+'.light.c')
    return dump.read_text(),dump.stat().st_size,(work/'affine.s').stat().st_size

def observed_functions(dump,names):
    observed={}
    for fn in names:
        body=function_body(dump,fn)
        if 'switch (0)' not in body:continue
        # Finite guards also test activation thresholds. The maximum n threshold
        # is the common count window which precedes every address check.
        caps=re.findall(r'\$n <= (\d+)',body)
        assert caps,(fn,body)
        observed[fn]={'count_guard_cap':max(map(int,caps)),'body_bytes':len(body.encode())}
    return observed

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cases');parser.add_argument('--reference-only',action='store_true')
    args=parser.parse_args()
    reference=checked_reference(SOURCE,WORK,reference_output())
    resource_reference=checked_reference(RESOURCE_SOURCE,WORK/'resources',
        ''.join(resource_model(*a) for a in resource_inputs()))
    if args.reference_only:
        print('GCC and independent models agree:',len(full_inputs())+2,'affine calls and',len(resource_inputs()),'resource calls')
        return
    stamp=check_build()
    templates={
        'schedule-identity':'(schedule ((coordinate 0) ordinal) ())',
        'schedule-fission':'(schedule (ordinal (coordinate 0)) ())',
        'schedule-reflect':'(schedule ((negative-coordinate 0) ordinal) ((reflect 0)))',
        'direct-identity':loop_template(1),'direct-reflect':loop_template(1,reverse=True),
        'constant-coordinate':'(loop (constant 0) (var 0) (each (instr current ((constant 0)))))',
        'wrong-reflect':'(map-index ((reflect 0)) '+loop_template(1)+')',
        'invalid-coordinate':'(schedule ((coordinate 1) ordinal) ())'}
    cases=[(name,syntax,{}) for name,syntax in templates.items()]
    cases += [(name,templates['schedule-identity'],extra) for name,extra in [
        ('resource-limit',{'GUARDCERT_FM_ROWS':'0'}),('invalid-certificate',{'GUARDCERT_ORACLE_FAULT':'top-certificate'})]]
    selected=set(args.cases.split(',')) if args.cases else {name for name,_,_ in cases}
    assert selected<={name for name,_,_ in cases}
    configurations={}
    for name,syntax,extra in cases:
        if name not in selected:continue
        dump,clight_bytes,assembly_bytes=compile_run(SOURCE,WORK/name,syntax,extra,reference)
        observed=observed_functions(dump,NAMES+['affine_undefined'])
        if extra or name=='invalid-coordinate':assert not observed,(name,observed)
        elif name in {'constant-coordinate','wrong-reflect'}:
            assert all(v['count_guard_cap']<=1 for v in observed.values()),(name,observed)
        else:
            assert set(observed)==set(NAMES+['affine_undefined']),(name,observed)
            for fn,v in observed.items():
                if fn=='affine_chain' and name in {'schedule-reflect','direct-reflect','schedule-fission'}:
                    assert v['count_guard_cap']==1,(name,fn,v)
                else:assert v['count_guard_cap']>8,(name,fn,v)
        configurations[name]={'guarded_functions':observed,'actual_calls':len(full_inputs())+2,
            'full_arrays_and_public_counters_match_model_and_gcc':True,
            'clight_bytes':clight_bytes,'assembly_bytes':assembly_bytes,
            'template_sha256':hashlib.sha256((WORK/name/'candidate.sexp').read_bytes()).hexdigest()}
        (WORK/'partial-report.json').write_text(json.dumps(configurations,indent=2)+'\n')
        print(name,{fn:v['count_guard_cap'] for fn,v in observed.items()},flush=True)
    resources={}
    for name in ['schedule-identity','schedule-reflect']:
        if args.cases and name not in selected:continue
        dump,clight_bytes,assembly_bytes=compile_run(RESOURCE_SOURCE,WORK/'resources'/name,templates[name],{},resource_reference)
        observed=observed_functions(dump,['alias_reads_31','alias_reads_32','alias_reads_64'])
        assert set(observed)=={'alias_reads_31','alias_reads_32'},(name,observed)
        assert observed['alias_reads_31']['count_guard_cap']>8
        assert observed['alias_reads_32']['count_guard_cap']==1
        resources[name]={'guarded_functions':observed,'actual_calls':len(resource_inputs()),
            'raw_access_limit_boundary_and_safe_finite_fallback_checked':True,
            'too_many_accesses_keeps_original_source':True,'clight_bytes':clight_bytes,'assembly_bytes':assembly_bytes}
        print('resource',name,observed,flush=True)
    result={'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'resource_source_sha256':hashlib.sha256(RESOURCE_SOURCE.read_bytes()).hexdigest(),
        'configurations':configurations,'resource_configurations':resources,'full_configuration_suite':not bool(args.cases),
        'scope':'full CompCert assembly execution; one-axis signed affine strides, decreasing and constant addresses, multi-pointer multi-operation chains, modular source arithmetic, actual address separation and count fallback; branch diagnostics separate'}
    (WORK/('smoke-report.json' if args.cases else 'report.json')).write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':main()
