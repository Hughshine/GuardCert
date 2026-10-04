"""Exercise independently guarded axis limits with complete C-to-assembly execution."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import native_memory_affine_alias as common
import native_memory_axis_alias as original
from native_zero_trip import function_body

ROOT=common.ROOT
SOURCE=ROOT/'examples/native_memory_axis_bounds.c'
WORK=ROOT/'build/native-memory-axis-bounds'
NAMES=original.NAMES
DIMENSIONS=original.DIMENSIONS
BOUND_NAMES=['n','m','s','t']

def full_inputs():
    result=original.full_inputs()
    extra=[[[62,1],[63,15],[64,1],[64,15],[1,16],[65,1],[64,16]],
           [[62,1],[63,15],[64,1],[64,15],[1,16]],
           [[62,1],[63,15],[64,1],[64,15],[1,16],[65,1],[64,16]],
           [[16,8,8],[17,1,1],[1,9,1],[1,1,9]],
           [[8,4,8,4],[9,1,1,1],[1,5,1,1],[1,1,9,1],[1,1,1,5]]]
    for which,counts_set in enumerate(extra):
        for kind in range(5):
            for counts in counts_set:
                result.append([which,kind,0]+counts+[1]*(4-len(counts))+[-7,11])
    return result

output_model=original.output_model
separated=original.separated
source_points=original.source_points

def observed_functions(dump):
    found={}
    for which,fn in enumerate(NAMES):
        body=function_body(dump,fn)
        if 'switch (0)' not in body:continue
        begin=body.index('switch (0)');end=body.index('continue;',begin)
        guard=body[begin:end]
        caps=[]
        for bound in BOUND_NAMES[:DIMENSIONS[which]]:
            matches=re.findall(r'\$'+bound+r'\s*<=\s*(\d+)',guard)
            assert matches and len(set(matches))==1,(fn,bound,matches)
            caps.append(int(matches[0]))
        found[fn]={'count_guard_caps':caps,'body_bytes':len(body.encode())}
    return found


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--reference-only',action='store_true')
    parser.add_argument('--previous-compiler',type=Path);parser.add_argument('--cases');args=parser.parse_args()
    reference=common.checked_reference(SOURCE,WORK,''.join(output_model(a) for a in full_inputs()))
    if args.reference_only:print('axis bounds fixture:',len(full_inputs()),'GCC calls match the word model');return
    if args.previous_compiler:
        common.COMPILER=args.previous_compiler.resolve()
        stamp=json.loads((common.COMPILER.parent/'.guard-build.json').read_text())
        assert hashlib.sha256(common.COMPILER.read_bytes()).hexdigest()==stamp['compiler_sha256']
    else:
        stamp=common.check_build()
        proof=json.loads((ROOT/'build/guard-memory-proof-report.json').read_text())
        assert proof['multi_axis_per_axis_bounds_csem_asm_proved']
    options=[(name,syntax,{}) for name,syntax in original.templates().items()]
    options+=[(name,original.templates()['schedule-interchange-2'],extra) for name,extra in [
        ('resource-limit',{'GUARDCERT_FM_ROWS':'0'}),('invalid-certificate',{'GUARDCERT_ORACLE_FAULT':'top-certificate'})]]
    selected=set(args.cases.split(',')) if args.cases else {name for name,_,_ in options}
    assert selected<={name for name,_,_ in options}
    configurations={}
    for name,syntax,extra in options:
        if name not in selected:continue
        if not args.previous_compiler:syntax='(per-axis '+syntax+')'
        dump,cb,ab=common.compile_run(SOURCE,WORK/('before' if args.previous_compiler else 'after')/name,syntax,extra,reference)
        found=observed_functions(dump)
        if extra or name=='invalid-coordinate':assert not found,(name,found)
        else:
            expected=set(NAMES) if name.startswith('tile') else {fn for fn,d in zip(NAMES,DIMENSIONS) if d==int(name[-1])}
            assert expected<=set(found),(name,found)
            if not args.previous_compiler:
                assert any(len(set(v['count_guard_caps']))>1 for v in found.values()),(name,found)
        configurations[name]={'guarded_functions':found,'actual_calls':len(full_inputs()),
            'full_arrays_and_public_counters_match_model_and_gcc':True,'clight_bytes':cb,'assembly_bytes':ab}
        print(name,{fn:v['count_guard_caps'] for fn,v in found.items()},flush=True)
    report={'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'configurations':configurations,
        'full_configuration_suite':not bool(args.cases),'previous_compiler':bool(args.previous_compiler),
        'scope':'complete CompCert assembly execution; independent source-order word model, complete buffers and public cursor exits; per-axis bounds and actual aliases, fallback, empty dimensions and extreme values'}
    (WORK/('before-report.json' if args.previous_compiler else 'smoke-report.json' if args.cases else 'report.json')).write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':main()
