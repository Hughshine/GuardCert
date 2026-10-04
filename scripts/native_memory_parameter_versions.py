"""Execute parameter-profile guard families in complete CompCert programs."""
import argparse
import hashlib
import json
import re
from pathlib import Path
import native_memory_address_parameters as fixture
from native_zero_trip import function_body
import native_memory_affine_alias as common

ROOT=fixture.ROOT
SOURCE=fixture.SOURCE
WORK=ROOT/'build/native-memory-parameter-versions'


def observed_versions(dump):
    found={}
    for which,fn in enumerate(fixture.NAMES):
        body=function_body(dump,fn)
        starts=[m.start() for m in re.finditer(r'switch \(0\)',body)]
        versions=[]
        for start in starts:
            end=body.index('continue;',start);guard=body[start:end]
            counts=re.findall(r'\bif\s*\(0\s*<\s*\$(\w+)\)',guard)
            parameters=re.findall(r'\bif\s*\(0\s*<=\s*\$(\w+)\)',guard)
            root=re.search(r'\bif\s*\(\$(\w+)\s*==\s*0U?\)',guard)
            assert counts and parameters and root,(fn,guard)
            assert counts==fixture.BOUND_NAMES[fixture.DIMENSIONS[which]-len(counts):fixture.DIMENSIONS[which]]
            limits={}
            for identifier in counts+parameters:
                matches=re.findall(r'\$'+identifier+r'\s*<=\s*(\d+)',guard)
                assert matches and len(set(matches))==1,(fn,identifier,matches)
                limits[identifier]=int(matches[0])
            versions.append({'count_guard_caps':[limits[x] for x in counts],
                'count_identifiers':counts,'root_iterator':root[1],
                'address_parameter_identifiers':parameters,
                'address_parameter_caps':[limits[x]+1 for x in parameters],
                'whole_source_region':len(counts)==fixture.DIMENSIONS[which],
                'coordinate_coefficient_vectors_equal':which!=7})
        if versions:
            assert len(versions)<=5
            found[fn]={'versions':versions}
    return found


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cases')
    args=parser.parse_args()
    stamp=common.check_build()
    proof=json.loads((ROOT/'build/guard-memory-proof-report.json').read_text())
    assert proof['memory_parameter_version_families_csem_asm_proved']
    inputs=fixture.full_inputs()
    reference=common.checked_reference(SOURCE,WORK,''.join(fixture.output_model(a) for a in inputs))
    options=[(name,syntax,{}) for name,syntax in fixture.templates().items()]
    options += [(name,fixture.templates()['schedule-interchange-2'],extra) for name,extra in [
        ('resource-limit',{'GUARDCERT_FM_ROWS':'0'}),('invalid-certificate',{'GUARDCERT_ORACLE_FAULT':'top-certificate'})]]
    selected=set(args.cases.split(',')) if args.cases else {name for name,_,_ in options}
    assert selected<={name for name,_,_ in options}
    configurations={}
    for name,syntax,extra in options:
        if name not in selected:continue
        dump,cb,ab=common.compile_run(SOURCE,WORK/name,'(versions (per-axis '+syntax+'))',extra,reference)
        found=observed_versions(dump)
        if extra or name=='invalid-coordinate':assert not found,(name,found)
        else:
            expected={fn for fn,d in zip(fixture.NAMES,fixture.DIMENSIONS) if d>=2} if name.startswith('tile') else {fn for fn,d in zip(fixture.NAMES,fixture.DIMENSIONS) if d==int(name[-1])}
            assert expected<=set(found),(name,found)
            assert all(found[fn]['versions'][0]['whole_source_region'] for fn in expected),(name,found)
            assert all(len(found[fn]['versions'])>1 for fn in found),(name,found)
            for fn,metadata in found.items():
                first=metadata['versions'][0]
                for version in metadata['versions']:
                    for key in ['count_identifiers','root_iterator','address_parameter_identifiers','whole_source_region']:
                        assert version[key]==first[key],(name,fn,key)
                caps=[version['address_parameter_caps'][0] for version in metadata['versions']]
                assert caps==sorted(set(caps),reverse=True),(name,fn,caps)
        configurations[name]={'guarded_functions':found,'actual_calls':len(inputs),
            'full_arrays_and_public_counters_match_model_and_gcc':True,'clight_bytes':cb,'assembly_bytes':ab}
        print(name,{fn:[v['address_parameter_caps'][0] for v in m['versions']] for fn,m in found.items()},flush=True)
    result={'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'configurations':configurations,
        'full_configuration_suite':not bool(args.cases),
        'scope':'complete CompCert assembly execution; checked parameter-profile guard families with original-source fallback, real arrays and public exits; branch and version choice instrumentation reported separately'}
    (WORK/('smoke-report.json' if args.cases else 'report.json')).write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
