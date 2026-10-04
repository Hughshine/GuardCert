"""Observe emitted multi-pointer Clight branches; separate from assembly evidence."""
import json,re,subprocess
import native_affine_nest_multiple_pointers as fixture
import native_affine_nest_paths as paths
from native_zero_trip import function_body
from native_memory_layout_sequence_paths import printer_for_gcc


def numeric_accepts(args):
    return paths.guard_accepts(args)


def alias_accepts(args):
    which,mode,*_=args
    points,_=fixture.source_points(args)
    logical=[set(),set(),set()]
    for point in points:
        i,j=point[:2]; k=point[2] if len(point)==3 else 0
        index=512*i+32*j+k
        logical[0].add(index);logical[1].add(index)
        if fixture.DEPTHS[which]==3:logical[2].add(index)
        if which==2:logical[0].add(index+480)
    physical=[{(slot,offset+index) for index in cells}
              for (slot,offset),cells in zip(fixture.pointer_views(mode),logical)]
    return all(not(first&second) for i,first in enumerate(physical) for second in physical[i+1:])


def marked_source(dump,names):
    source=printer_for_gcc(dump)
    source=source[:source.index('\nint guard_original_main(void)\n{')]
    for slot,name in enumerate(names):
        body=function_body(source,name)
        conditions=list(re.finditer(r'if \(\$[0-9]+\) \{',body)); assert conditions,name
        selection=conditions[-1]; opening=selection.end()-1
        end=paths.closing_brace(body,opening)
        fallback=re.match(r'\s*else\s*\{',body[end+1:]); assert fallback,name
        fallback_open=end+1+fallback.end()-1
        prefix=body[:selection.start()]
        guard_begin=prefix.index('$n;',prefix.index('$L = 83;'))
        guard_begin=prefix.rfind('\n',0,guard_begin)
        before,guard=prefix[:guard_begin],prefix[guard_begin:]
        for variable,counter in [('local_p','guard_p_reads'),('local_alpha','guard_alpha_reads')]:
            guard=re.sub(r'\$'+variable+r'\b','('+counter+'['+str(slot)+']++, $'+variable+')',guard)
        changed=(before+guard+body[selection.start():opening+1]+f'guard_fast[{slot}]++;'
                 +body[opening+1:fallback_open+1]+f'guard_fallback[{slot}]++;'+body[fallback_open+1:])
        source=source.replace(body,changed,1)
    declarations=''.join('int '+name+'['+str(len(names))+'];\n'
                         for name in ['guard_fast','guard_fallback','guard_p_reads','guard_alpha_reads'])
    return declarations+source


def diagnostic(name,configuration,directory=fixture.WORK):
    work=directory/name
    names=[fn for fn,facts in configuration['functions'].items() if facts['guarded']]
    source=marked_source((work/(fixture.SOURCE.stem+'.light.c')).read_text(),names)
    calls,expected,observations=[],[],[]
    fast=fallback=shared_fast=overlap_fallback=undefined_p=undefined_alpha=negative=0
    for slot,function in enumerate(names):
        which=fixture.NAMES.index(function)
        for args in [row for row in fixture.full_inputs() if row[0]==which]:
            numeric=numeric_accepts(args);alias=alias_accepts(args);hit=int(numeric and alias)
            fast+=hit;fallback+=1-hit;negative+=int(hit and args[2]<0)
            shared_fast+=int(hit and args[1] in [2,3,4]);overlap_fallback+=int(numeric and not alias)
            checks=[]
            if which==3:
                _,_,start,n,m,p,_=args
                p_defined=start<n and fixture.word(n-1+m)>0
                alpha_defined=p_defined and fixture.word(n-2+m+p)>0
                if not p_defined:checks.append(f'guard_p_reads[{slot}]!=0');undefined_p+=1
                if not alpha_defined:checks.append(f'guard_alpha_reads[{slot}]!=0');undefined_alpha+=1
            calls.append(''.join(f'{counter}[{slot}]=0;' for counter in ['guard_fast','guard_fallback','guard_p_reads','guard_alpha_reads'])
                         +'multi_case('+','.join(fixture.literal(x) for x in args)+');'
                         +f'if(guard_fast[{slot}]!={hit} || guard_fallback[{slot}]!={1-hit}'
                         +''.join(' || '+check for check in checks)+')return 1;')
            expected.append(fixture.output_model(args))
            observations.append({'input':list(args),'numeric_guard':numeric,'cross_pointer_disjoint':alias,'actual_fast_branch':bool(hit)})
    assert fast and fallback and shared_fast and overlap_fallback and undefined_p and undefined_alpha and negative
    diagnostic_source=work/'branch-diagnostic.c'
    diagnostic_source.write_text(source+'\nint main(void){\n'+'\n'.join(calls)+'\nreturn 0;}\n')
    subprocess.run(['gcc','-O0','-fwrapv','-Wno-builtin-declaration-mismatch',str(diagnostic_source),'-o',str(work/'branch-diagnostic')],check=True,capture_output=True)
    with (work/'branch-output.txt').open('w') as output:
        subprocess.run([str(work/'branch-diagnostic')],check=True,text=True,stdout=output,timeout=180)
    assert (work/'branch-output.txt').read_text()==''.join(expected),name
    return {'instrumented_clight_calls':len(calls),'fast':fast,'fallback':fallback,
            'shared_storage_disjoint_fast':shared_fast,'overlapping_access_fallback':overlap_fallback,
            'undefined_p_zero_guard_reads':undefined_p,'undefined_alpha_zero_guard_reads':undefined_alpha,
            'negative_start_fast':negative,'observations':observations,
            'diagnostic_source_sha256':fixture.sha(diagnostic_source),'diagnostic_output_sha256':fixture.sha(work/'branch-output.txt')}


def main():
    fixture.unified.check_build()
    report=json.loads((fixture.WORK/'report.json').read_text());assert report['status']=='passed'
    rows={}
    for name in ['identity','interchange','tile-2-3']:
        rows[name]=diagnostic(name,report['configurations'][name]);print(name,{k:v for k,v in rows[name].items() if k!='observations'},flush=True)
    (fixture.WORK/'branch-report.json').write_text(json.dumps({'status':'passed','compiler_sha256':report['compiler_sha256'],
        'scope':'GCC instrumentation of actual emitted Clight; distinct from CompCert assembly runs','configurations':rows},indent=2)+'\n')

if __name__=='__main__':main()
