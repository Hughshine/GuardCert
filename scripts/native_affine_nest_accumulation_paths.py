"""Observe actual accumulation guards separately from CompCert assembly."""
import json,subprocess
import native_affine_nest_accumulation as fixture
from native_affine_nest_multiple_pointers_paths import marked_source

def accepts(args):
    _,start,n,m,p=args
    numeric=(start<n and fixture.word(start+m)>0 and p>0 and 1<=n<=8
             and -4<=start<=7 and -8<=m<=8 and -8<=p<=8)
    cells=[set(),set(),set()]
    for i,j,k in fixture.points_and_exit(args)[0]:
        cells[0].add(32*i+j);cells[1].add(32*i+k);cells[2].add(32*k+j)
    physical=[{(block,offset+index) for index in locations}
              for (block,offset),locations in zip(fixture.views(args[0]),cells)]
    alias=all(not(first&second) for axis,first in enumerate(physical) for second in physical[axis+1:])
    return numeric,alias

def main():
    stamp=fixture.compiler.check_build();report=json.loads((fixture.WORK/'report.json').read_text())
    assert report['status']=='passed' and report['compiler_sha256']==stamp['compiler_sha256']
    rows={}
    for name in ['identity','inner-interchange','inner-interchange-parametric','interchange-tile','partition-interchange-tile',
                 'parametric-tile','partition-parametric-tile']:
        work=fixture.WORK/name
        source=marked_source((work/(fixture.SOURCE.stem+'.light.c')).read_text(),['affine_accumulation'])
        calls=[];fast=fallback=shared=overlap=negative=0;observations=[]
        for args in fixture.inputs():
            numeric,alias=accepts(args);hit=int(numeric and alias)
            fast+=hit;fallback+=1-hit;shared+=int(hit and args[0] in [2,3,4])
            overlap+=int(numeric and not alias);negative+=int(hit and args[1]<0)
            calls.append('guard_fast[0]=0;guard_fallback[0]=0;accumulation_case('
                +','.join(map(fixture.literal,args))+');'
                +f'if(guard_fast[0]!={hit} || guard_fallback[0]!={1-hit})return 1;')
            observations.append({'input':list(args),'numeric_guard':numeric,'alias_guard':alias,'actual_fast':bool(hit)})
        assert fast and fallback and shared and overlap and negative
        diagnostic=work/'branch-diagnostic.c'
        diagnostic.write_text(source+'\nint main(void){\n'+'\n'.join(calls)+'\nreturn 0;}\n')
        subprocess.run(['gcc','-O0','-fwrapv','-Wno-builtin-declaration-mismatch',str(diagnostic),'-o',str(work/'branch-diagnostic')],check=True,capture_output=True)
        with (work/'branch-output.txt').open('w') as output:
            subprocess.run([str(work/'branch-diagnostic')],check=True,stdout=output,timeout=180)
        assert (work/'branch-output.txt').read_text()==''.join(fixture.model(row) for row in fixture.inputs())
        rows[name]={'instrumented_clight_calls':len(calls),'fast':fast,'fallback':fallback,
            'shared_storage_disjoint_fast':shared,'overlapping_access_fallback':overlap,'negative_start_fast':negative,
            'diagnostic_source_sha256':fixture.compiler.sha(diagnostic),'diagnostic_output_sha256':fixture.compiler.sha(work/'branch-output.txt'),
            'observations':observations}
        print(name,fast,fallback,flush=True)
    (fixture.WORK/'branch-report.json').write_text(json.dumps({'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'configurations':rows,'scope':'GCC instrumentation of emitted Clight; unmodified assembly verified separately'},indent=2)+'\n')

if __name__=='__main__':main()
