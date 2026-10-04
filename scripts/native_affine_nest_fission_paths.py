"""Observe actual guards around imported multi-statement fission candidates."""
import json,subprocess
import native_affine_nest_fission as fixture
import native_affine_nest_multiple_pointers_paths as paths


def accepts(args):
    which,mode,start,n,m,p,_=args
    numeric=(start<n and fixture.word(start+m)>0 and 1<=n<=8 and -4<=start<=7 and -8<=m<=8
             and (fixture.DEPTHS[which]==2 or (p>0 and -8<=p<=8)))
    cells=[set(),set(),set()]
    for point in fixture.source_points(args)[0]:
        i,j=point[:2];k=point[2] if len(point)==3 else 0;index=512*i+32*j+k
        cells[0].add(index);cells[1].add(index);cells[2].add(index)
        if which==2:cells[0].add(index+480)
    views=fixture.memory.pointer_views(mode)
    physical=[{(block,offset+index) for index in locations} for (block,offset),locations in zip(views,cells)]
    alias=all(not(a&b) for i,a in enumerate(physical) for b in physical[i+1:])
    return numeric,alias


def diagnostic(name,row):
    work=fixture.WORK/name;names=[fn for fn,facts in row['functions'].items() if facts['guarded']]
    source=paths.marked_source((work/(fixture.SOURCE.stem+'.light.c')).read_text(),names)
    calls,expected,observations=[],[],[];fast=fallback=shared_fast=overlap_fallback=negative=0
    for slot,fn in enumerate(names):
        which=fixture.NAMES.index(fn)
        for args in [row for row in fixture.full_inputs() if row[0]==which]:
            numeric,alias=accepts(args);hit=int(numeric and alias)
            fast+=hit;fallback+=1-hit;shared_fast+=int(hit and args[1] in [2,3,4])
            overlap_fallback+=int(numeric and not alias);negative+=int(hit and args[2]<0)
            calls.append(f'guard_fast[{slot}]=0;guard_fallback[{slot}]=0;multi_case('
                         +','.join(fixture.literal(x) for x in args)+');'
                         +f'if(guard_fast[{slot}]!={hit} || guard_fallback[{slot}]!={1-hit})return 1;')
            expected.append(fixture.output_model(args));observations.append({'input':list(args),'numeric_guard':numeric,'alias_guard':alias,'actual_fast':bool(hit)})
    assert fast and fallback and shared_fast and overlap_fallback and negative
    path=work/'branch-diagnostic.c';path.write_text(source+'\nint main(void){\n'+'\n'.join(calls)+'\nreturn 0;}\n')
    subprocess.run(['gcc','-O0','-fwrapv','-Wno-builtin-declaration-mismatch',str(path),'-o',str(work/'branch-diagnostic')],check=True,capture_output=True)
    with (work/'branch-output.txt').open('w') as output:subprocess.run([str(work/'branch-diagnostic')],check=True,text=True,stdout=output,timeout=180)
    assert (work/'branch-output.txt').read_text()==''.join(expected),name
    return {'instrumented_clight_calls':len(calls),'fast':fast,'fallback':fallback,'shared_storage_disjoint_fast':shared_fast,
            'overlapping_access_fallback':overlap_fallback,'negative_start_fast':negative,'observations':observations,
            'diagnostic_source_sha256':fixture.memory.sha(path),'diagnostic_output_sha256':fixture.memory.sha(work/'branch-output.txt')}


def main():
    stamp=fixture.memory.unified.check_build();report=json.loads((fixture.WORK/'report.json').read_text())
    assert report['status']=='passed' and report['compiler_sha256']==stamp['compiler_sha256']
    rows={}
    for name in ['identity','fission','reverse-fission']:
        rows[name]=diagnostic(name,report['configurations'][name]);print(name,rows[name]['fast'],rows[name]['fallback'],flush=True)
    (fixture.WORK/'branch-report.json').write_text(json.dumps({'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'configurations':rows,'scope':'GCC instrumentation of actual emitted fission Clight; actual assembly checked separately'},indent=2)+'\n')

if __name__=='__main__':main()
