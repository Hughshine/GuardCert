"""Observe the checked condition chosen for an external fission candidate."""
import json,subprocess
import native_affine_nest_condition_search as fixture
import native_affine_nest_fission_paths as fission
import native_affine_nest_multiple_pointers_paths as paths


def diagnostic(name,row):
    work=fixture.WORK/name
    names=[fn for fn,facts in row['functions'].items() if facts['guarded']]
    source=paths.marked_source((work/'condition-search.light.c').read_text(),names)
    calls,expected,observations=[],[],[]
    fast=fallback=singleton_future=wide_future_fallback=overlap_fallback=0
    for slot,fn in enumerate(names):
        which=fixture.fixture.NAMES.index(fn)
        for args in [row for row in fixture.inputs() if row[0]==which]:
            numeric,alias=fission.accepts(args)
            if name=='searched-fission' and which==2:
                numeric=numeric and args[2]==0 and args[3]==1
            hit=int(numeric and alias)
            fast+=hit;fallback+=1-hit;overlap_fallback+=int(numeric and not alias)
            singleton_future+=int(name=='searched-fission' and which==2 and hit)
            wide_future_fallback+=int(name=='searched-fission' and which==2 and args[3]>1 and not hit)
            calls.append(f'guard_fast[{slot}]=0;guard_fallback[{slot}]=0;multi_case('
                         +','.join(fixture.fixture.literal(x) for x in args)+');'
                         +f'if(guard_fast[{slot}]!={hit} || guard_fallback[{slot}]!={1-hit})return 1;')
            expected.append(fixture.fixture.output_model(args))
            observations.append({'input':list(args),'selected_numeric_guard':numeric,
                                 'cross_pointer_disjoint':alias,'actual_fast':bool(hit)})
    assert fast and fallback and overlap_fallback
    if name=='searched-fission':assert singleton_future and wide_future_fallback
    path=work/'branch-diagnostic.c'
    path.write_text(source+'\nint main(void){\n'+'\n'.join(calls)+'\nreturn 0;}\n')
    subprocess.run(['gcc','-O0','-fwrapv','-Wno-builtin-declaration-mismatch',str(path),
                    '-o',str(work/'branch-diagnostic')],check=True,capture_output=True)
    with (work/'branch-output.txt').open('w') as output:
        subprocess.run([str(work/'branch-diagnostic')],check=True,text=True,stdout=output,timeout=180)
    assert (work/'branch-output.txt').read_text()==''.join(expected),name
    return {'instrumented_clight_calls':len(calls),'fast':fast,'fallback':fallback,
            'singleton_future_fast':singleton_future,'wider_future_fallback':wide_future_fallback,
            'overlapping_access_fallback':overlap_fallback,'observations':observations,
            'diagnostic_source_sha256':fixture.fixture.memory.sha(path),
            'diagnostic_output_sha256':fixture.fixture.memory.sha(work/'branch-output.txt')}


def main():
    stamp=fixture.check_build()
    report=json.loads((fixture.WORK/'report.json').read_text())
    assert report['status']=='passed' and report['compiler_sha256']==stamp['compiler_sha256']
    rows={}
    for name in ['identity','wide-fission','searched-fission','searched-reverse']:
        rows[name]=diagnostic(name,report['configurations'][name])
        print(name,{k:v for k,v in rows[name].items() if k!='observations'},flush=True)
    (fixture.WORK/'branch-report.json').write_text(json.dumps({
        'status':'passed','compiler_sha256':stamp['compiler_sha256'],'configurations':rows,
        'scope':'GCC instrumentation of actual emitted Clight; actual assembly checked separately'},indent=2)+'\n')

if __name__=='__main__':main()
