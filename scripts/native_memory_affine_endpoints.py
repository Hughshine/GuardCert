"""Compare endpoint alias scans with source models and the previous compiler."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import native_memory_affine_alias as common
from native_memory_recursive import loop_template
ROOT=common.ROOT
SOURCE=ROOT/'examples/native_memory_affine_endpoints.c'
WORK=ROOT/'build/native-memory-affine-endpoints'
NAMES=['endpoint_stride','endpoint_negative','endpoint_constant','endpoint_unit']
SIZE=4600

def full_inputs():
    counts=[0,1,2,9,33,129,257,511,512,513,1024,1025]
    result=[[w,k,0,n,-7,11] for w in range(4) for k in range(5) for n in counts[:9 if w==1 else 12]]
    for w in range(4):
        result += [[w,0,1,33,-2147483648,2147483647],[w,0,0,129,-2147483648,2147483647],
                   [w,5,0,0,3,-7],[w,5,0,-2147483648,3,-7]]
    return result

def indices(which,i):
    if which==0:return 2*i,2*i+1
    if which==1:return 1023-2*i,1022-2*i
    if which==2:return 2,3
    return i,i

def physical(kind):
    return (1,0) if kind in [0,5] else (0,{1:1,2:1500,3:0,4:2}[kind])

def separated(args):
    which,kind,start,n,_,_=args
    block,base=physical(kind)
    writes={indices(which,i)[0] for i in range(start,n)}
    reads={indices(which,i)[1]+base for i in range(start,n)}
    return block!=0 or not writes&reads

def output_model(args,reverse=False):
    which,kind,start,n,alpha,beta=args
    a,b=[3*i+1 for i in range(SIZE)],[5*i+7 for i in range(SIZE)]
    block,base=physical(kind);q=[a,b][block]
    for i in (reversed(range(start,n)) if reverse else range(start,n)):
        write,read=indices(which,i)
        assert 0<=write<SIZE and 0<=base+read<SIZE,args
        a[write]=common.word(q[base+read]+i*alpha+beta if which==2 else q[base+read]*alpha+beta)
    return ' '.join(map(str,args+[max(start,n)]+[x for row in zip(a,b) for x in row]))+'\n'

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--reference-only',action='store_true')
    parser.add_argument('--previous-compiler',type=Path)
    parser.add_argument('--cases')
    args=parser.parse_args()
    expected=''.join(output_model(a) for a in full_inputs())
    reference=common.checked_reference(SOURCE,WORK,expected)
    if args.reference_only:
        print('GCC and independent model agree:',len(full_inputs()),'calls');return
    templates={'schedule-identity':'(schedule ((coordinate 0) ordinal) ())',
        'schedule-reflect':'(schedule ((negative-coordinate 0) ordinal) ((reflect 0)))',
        'direct-identity':loop_template(1),'direct-reflect':loop_template(1,reverse=True),
        'wrong-reflect':'(map-index ((reflect 0)) '+loop_template(1)+')'}
    if args.previous_compiler:
        previous=args.previous_compiler.resolve()
        recorded=json.loads((previous.parent/'guard-build.json').read_text())
        assert recorded['compiler_sha256']==hashlib.sha256(previous.read_bytes()).hexdigest()
        original=common.COMPILER
        # The copied executable uses the same target and unchanged runtime headers.
        config=common.COMPILER.parent
        for name in ['compcert.ini','runtime']:
            link=previous.parent/name
            if not link.exists():link.symlink_to(config/name,target_is_directory=name=='runtime')
        common.COMPILER=previous
        dump,cb,ab=common.compile_run(SOURCE,WORK/'before',templates['schedule-identity'],{},reference)
        common.COMPILER=original
        observed=common.observed_functions(dump,NAMES)
        result={'status':'passed','compiler_sha256':recorded['compiler_sha256'],
            'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'actual_calls':len(full_inputs()),
            'full_arrays_and_public_counters_match_model_and_gcc':True,
            'guarded_functions':observed,'clight_bytes':cb,'assembly_bytes':ab}
        (WORK/'before-report.json').write_text(json.dumps(result,indent=2)+'\n')
        print('previous compiler',recorded['compiler_sha256'],observed);return
    stamp=common.check_build()
    proof=json.loads((ROOT/'build/guard-memory-proof-report.json').read_text())
    assert proof['affine_loop_alias_guard_linear_strategy_proved']
    assert proof['affine_pair_strategy_math_global_axioms']==[]
    cases=[(name,syntax,{}) for name,syntax in templates.items()]
    cases += [(name,templates['schedule-identity'],extra) for name,extra in [
        ('resource-limit',{'GUARDCERT_FM_ROWS':'0'}),('invalid-certificate',{'GUARDCERT_ORACLE_FAULT':'top-certificate'})]]
    selected=set(args.cases.split(',')) if args.cases else {name for name,_,_ in cases}
    assert selected<={name for name,_,_ in cases}
    configs={}
    for name,syntax,extra in cases:
        if name not in selected:continue
        dump,cb,ab=common.compile_run(SOURCE,WORK/name,syntax,extra,reference)
        observed=common.observed_functions(dump,NAMES)
        if extra:assert not observed,(name,observed)
        elif name=='wrong-reflect':
            # Reflection and the unchanged iterator can coincide on a singleton.
            assert all(v['count_guard_cap']<=1 for v in observed.values()),(name,observed)
        else:
            assert set(observed)==set(NAMES),(name,observed)
            for fn,v in observed.items():
                if fn=='endpoint_constant' and 'reflect' in name:assert v['count_guard_cap']==1
                else:assert v['count_guard_cap']>8,(name,fn,v)
        configs[name]={'guarded_functions':observed,'actual_calls':len(full_inputs()),
            'full_arrays_and_public_counters_match_model_and_gcc':True,'clight_bytes':cb,'assembly_bytes':ab}
        print(name,{fn:v['count_guard_cap'] for fn,v in observed.items()},flush=True)
    result={'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'configurations':configs,
        'full_configuration_suite':not bool(args.cases),
        'scope':'complete CompCert assembly execution; equal positive and negative strides, interleaved same-block accesses, constant-address dependence and guarded reversal; branch counts and check costs separate'}
    (WORK/('smoke-report.json' if args.cases else 'report.json')).write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':main()
