"""Run checked started fragments through CompCert and compare complete outputs."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import native_memory_address_parameters as fixture
from native_zero_trip import function_body

ROOT=fixture.ROOT
SOURCE=ROOT/'examples/native_memory_started_regions.c'
WORK=ROOT/'build/native-memory-started-regions'
NAMES=fixture.NAMES
DIMENSIONS=fixture.DIMENSIONS
BOUND_NAMES=['n','m','s']
output_model=fixture.output_model
accesses=fixture.accesses
locations=fixture.locations
separated=fixture.separated


def full_inputs():
    result=fixture.full_inputs()
    for which,dims in enumerate(DIMENSIONS):
        for kind in range(5):
            for start in [1,2]:
                result.append([which,kind,start,3,2,2,3,7,-2147483648,2147483647])
            result.append([which,kind,-1,3,2,2,3,7,-7,11])
        for start,n in [(2,2),(3,2),(-2147483648,-2147483648)]:
            result.append([which,5,start,n,2,2,-2147483648,2147483647,-7,11])
        if dims>=2:
            result.append([which,5,1,3,0,2,-2147483648,2147483647,-7,11])
        if dims>=3:
            result.append([which,5,1,3,2,0,-2147483648,2147483647,-7,11])
            for kind in range(5):
                for start in [1,2]:
                    result.append([which,kind,start,3,1,1,3,7,-2147483648,2147483647])
    result.append([6,5,-1,0,0,2,-2147483648,2147483647,-7,11])
    # Keep each executable input once, so aggregate call counts are unambiguous.
    return list(dict.fromkeys(map(tuple,result)))


def c_literal(value):
    return '(-2147483647-1)' if value==-2147483648 else str(value)


def observed_functions(dump):
    found={}
    for which,fn in enumerate(NAMES):
        body=function_body(dump,fn)
        if 'switch (0)' not in body:continue
        begin=body.index('switch (0)');end=body.index('continue;',begin);guard=body[begin:end]
        active=re.search(r'\bif\s*\(\$(\w+)\s*<\s*\$(\w+)\)',guard)
        assert active,(fn,guard)
        root,bound=active.groups()
        counts=re.findall(r'\bif\s*\(0\s*<\s*\$(\w+)\)',guard)
        parameters=[identifier for identifier in re.findall(r'\bif\s*\(0\s*<=\s*\$(\w+)\)',guard) if identifier!=root]
        assert counts and counts==BOUND_NAMES[DIMENSIONS[which]-len(counts):DIMENSIONS[which]],(fn,counts)
        assert bound==counts[0],(fn,bound,counts)
        limits={}
        for identifier in counts+parameters+[root]:
            caps=re.findall(r'\$'+identifier+r'\s*<=\s*(\d+)',guard)
            assert caps and len(set(caps))==1,(fn,identifier,caps)
            limits[identifier]=int(caps[0])
        found[fn]={'count_guard_caps':[limits[x] for x in counts],
            'count_identifiers':counts,'root_iterator':root,'root_entry_cap':limits[root]+1,
            'address_parameter_identifiers':parameters,'address_parameter_caps':[limits[x]+1 for x in parameters],
            'whole_source_region':len(counts)==DIMENSIONS[which],'body_bytes':len(body.encode()),'scan_strategy':'full-started-domain'}
    return found


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--reference-only',action='store_true');parser.add_argument('--cases')
    args=parser.parse_args();inputs=full_inputs();common=fixture.common
    reference=common.checked_reference(SOURCE,WORK,''.join(output_model(list(values)) for values in inputs))
    if args.reference_only:
        print('started fixture:',len(inputs),'complete GCC outputs match the word model');return
    stamp=common.check_build();proof=json.loads((ROOT/'build/guard-memory-proof-report.json').read_text())
    assert proof['memory_started_fragment_csem_asm_proved']
    templates=fixture.templates();options=[(name,syntax,{}) for name,syntax in templates.items()]
    options += [(name,templates['schedule-interchange-2'],extra) for name,extra in [
        ('resource-limit',{'GUARDCERT_FM_ROWS':'0'}),('invalid-certificate',{'GUARDCERT_ORACLE_FAULT':'top-certificate'})]]
    selected=set(args.cases.split(',')) if args.cases else {name for name,_,_ in options}
    assert selected<={name for name,_,_ in options}
    configurations={}
    for name,syntax,extra in options:
        if name not in selected:continue
        dump,cb,ab=common.compile_run(SOURCE,WORK/name,'(started (per-axis '+syntax+'))',extra,reference)
        found=observed_functions(dump)
        if extra or name=='invalid-coordinate':assert not found,(name,found)
        else:
            expected={fn for fn,d in zip(NAMES,DIMENSIONS) if d>=2} if name.startswith('tile') else {fn for fn,d in zip(NAMES,DIMENSIONS) if d==int(name[-1])}
            assert expected<=set(found),(name,expected,found)
            assert all(found[fn]['whole_source_region'] for fn in expected),(name,found)
        configurations[name]={'guarded_functions':found,'actual_calls':len(inputs),
            'full_arrays_and_public_counters_match_model_and_gcc':True,'clight_bytes':cb,'assembly_bytes':ab}
        print(name,{fn:v['count_guard_caps'] for fn,v in found.items()},flush=True)
    report={'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'configurations':configurations,
        'full_configuration_suite':not bool(args.cases),
        'scope':'complete CompCert assembly output; nonzero entry roots, negative-root fallback, empty null and undefined operands, real aliases, address parameters, signed RHS scalars, complete arrays and public source exits'}
    (WORK/('smoke-report.json' if args.cases else 'report.json')).write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':main()
