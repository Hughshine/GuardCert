"""Observe distinct runtime versions in the emitted Clight fallback chain."""
import json,re,subprocess
import native_affine_nest_runtime_versions as fixture
import native_affine_nest_fission_paths as model
from native_zero_trip import function_body
from native_affine_nest_paths import closing_brace
from native_memory_layout_sequence_paths import printer_for_gcc

def installed_profiles(name,which):
    if name=='wide-fission':return [] if which==2 else [0]
    if name=='single-identity':return [0]
    if name=='versioned-fission':return [1] if which==2 else [0,1]
    if name=='versioned-reverse':return [] if which==1 else [0,1]
    return [0,1]

def selected_profile(name,args):
    which,_,start,n,m,p,_=args;wide,alias=model.accepts(args)
    narrow=(start==0 and n==1 and 0<m<=12 and
            (fixture.fixture.DEPTHS[which]==2 or 0<p<=12))
    for profile in installed_profiles(name,which):
        if alias and (wide if profile==0 else narrow):return profile
    return None

def instrument(dump,name):
    source=printer_for_gcc(dump).split('\nint guard_original_main(void)',1)[0]
    for which,fn in enumerate(fixture.fixture.NAMES):
        body=function_body(source,fn);selections=[]
        for match in re.finditer(r'if \(\$[0-9]+\) \{',body):
            opening=match.end()-1;end=closing_brace(body,opening)
            if '*($a' not in body[opening:end]:continue
            fallback=re.match(r'\s*else\s*\{',body[end+1:]);assert fallback,fn
            fallback_open=end+fallback.end()
            selections.append((opening,fallback_open))
        profiles=installed_profiles(name,which);assert len(selections)==len(profiles),(name,fn,selections,profiles)
        insertions=[]
        for profile,(opening,fallback) in zip(profiles,selections):
            insertions.extend([(opening+1,f'guard_fast[{which}][{profile}]++;'),
                               (fallback+1,f'guard_refusal[{which}][{profile}]++;')])
        changed=body
        for position,text in sorted(insertions,reverse=True):changed=changed[:position]+text+changed[position:]
        source=source.replace(body,changed,1)
    return 'int guard_fast[4][2],guard_refusal[4][2];\n'+source

def diagnostic(name,row):
    work=fixture.WORK/name
    dump=work/'runtime-versions.light.c';source=instrument(dump.read_text(),name)
    calls=[];expected=[];counts={'wide':0,'narrow':0,'source':0};observations=[]
    for args in fixture.inputs():
        which=args[0];selected=selected_profile(name,args)
        counts['source' if selected is None else ['wide','narrow'][selected]]+=1
        profiles=installed_profiles(name,which);checks=[]
        for profile in range(2):
            reached=profile in profiles and not any(p<profile and selected==p for p in profiles)
            checks.extend([f'guard_fast[{which}][{profile}]!={int(selected==profile)}',
                           f'guard_refusal[{which}][{profile}]!={int(reached and selected!=profile)}'])
        calls.append(''.join(f'guard_fast[{which}][{p}]=guard_refusal[{which}][{p}]=0;' for p in range(2))+
            'multi_case('+','.join(map(fixture.fixture.literal,args))+');if('+ ' || '.join(checks)+')return 1;')
        expected.append(fixture.fixture.output_model(args))
        observations.append({'input':list(args),'selected_profile':selected})
    if name in ['identity','versioned-fission','versioned-reverse']:
        assert counts['wide'] and counts['narrow'] and counts['source'],(name,counts)
    path=work/'branch-diagnostic.c';path.write_text(source+'\nint main(void){\n'+'\n'.join(calls)+'\nreturn 0;}\n')
    subprocess.run(['gcc','-O0','-fwrapv','-Wno-builtin-declaration-mismatch',str(path),
        '-o',str(work/'branch-diagnostic')],check=True,capture_output=True)
    with(work/'branch-output.txt').open('w') as output:
        subprocess.run([str(work/'branch-diagnostic')],check=True,stdout=output,timeout=180)
    assert(work/'branch-output.txt').read_text()==''.join(expected),name
    return {'instrumented_clight_calls':len(calls),'selected':counts,'observations':observations,
            'diagnostic_source_sha256':fixture.fixture.memory.sha(path),
            'diagnostic_output_sha256':fixture.fixture.memory.sha(work/'branch-output.txt')}

def main():
    stamp=fixture.check_build();report=json.loads((fixture.WORK/'report.json').read_text())
    assert report['status']=='passed' and report['compiler_sha256']==stamp['compiler_sha256']
    rows={}
    for name in ['identity','single-identity','wide-fission','versioned-fission','versioned-reverse']:
        rows[name]=diagnostic(name,report['configurations'][name]);print(name,rows[name]['selected'],flush=True)
    (fixture.WORK/'branch-report.json').write_text(json.dumps({'status':'passed',
        'compiler_sha256':stamp['compiler_sha256'],'configurations':rows,
        'scope':'GCC execution of emitted nested guards; actual assembly checked separately'},indent=2)+'\n')

if __name__=='__main__':main()
