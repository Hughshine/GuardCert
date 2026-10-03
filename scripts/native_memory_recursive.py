"""Validate recursive C source extraction against complete assembly outputs."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
from native_zero_trip import function_body

ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'examples/native_memory_recursive.c'
COMPILER=ROOT/'build/compcert-memory-unified/ccomp'
WORK=ROOT/'build/native-memory-recursive'
ENTRY='GuardMemoryUnifiedCompiler.compile_memory_unified_regions'
METADATA={name:(4,4) for name in ['deep_four','deep_four_global','deep_four_context','deep_four_wrap',
    'deep_four_chain','deep_four_recurrence','deep_four_nonlinear','deep_four_unanchored','deep_four_undef']}
METADATA|={'deep_five':(5,3),'deep_six':(6,3),'deep_eight':(8,2),'deep_nine':(9,2)}
REFUSED={'deep_four_nonlinear','deep_four_unanchored','deep_nine'}
FOUR={name for name in METADATA if METADATA[name][0]==4}-REFUSED
ZERO_ONLY={'deep_four_undef'}
INITIAL=[99,55,44,33,22,11,8,7]
IDENTIFIERS=['i','j','k','t','u','v','w','x','y']
BOUNDS=['n','m','p','q','r','s','h','z','g']


def word(value):
    return (value+2**31)%2**32-2**31


def execute(name,start,counts,order=None):
    dimensions,base=METADATA[name]
    extent=base**dimensions
    overflow=name.endswith('_wrap')
    a=[2147483647-x if overflow else 3*x+1 for x in range(extent)]
    b=[2147483647-2*x if overflow else 5*x+2 for x in range(extent)]
    c=[2147483647-3*x if overflow else -777 for x in range(extent)]
    counters=[start]+INITIAL[:dimensions-1]
    for _ in range(2 if name.endswith('_context') else 1):
        if name.endswith('_context'):counters[0]=start
        points=[]

        def visit(axis):
            while counters[axis]<counts[axis]:
                if axis+1<dimensions:
                    counters[axis+1]=0
                    visit(axis+1)
                else:
                    points.extend((tuple(counters),site) for site in range(3 if name.endswith('_chain') else 1))
                counters[axis]+=1

        visit(0)
        if order is not None:points.sort(key=order)
        for coordinates,site in points:
            index=sum(value*base**(dimensions-1-axis) for axis,value in enumerate(coordinates))
            scalar=sum(coordinates[axis]*coordinates[axis+1] for axis in range(0,dimensions-1,2))
            if dimensions%2:scalar+=coordinates[-1]
            if name.endswith('_chain'):
                if site==0:b[index]=word(a[index]+scalar)
                elif site==1:c[index]=word(b[index]+b[index+1])
                else:b[index]=c[index]
            elif name.endswith('_recurrence'):b[index]=word(b[index]+b[index+1])
            elif name.endswith('_nonlinear'):c[index]=word(a[coordinates[0]*coordinates[1]+coordinates[2]*4+coordinates[3]]+b[index])
            else:c[index]=word(a[index+int(name.endswith('_unanchored'))]+b[index]+scalar)
    return (a,b,c),counters


def model(name,start,counts,order=None):
    counts=list(counts)
    if name in ZERO_ONLY:
        assert counts[0]<=start or counts[1]<=0 or counts[2]<=0
        arrays,counters=execute(name,start,counts[:3]+[0],order)
        counts[3]=9
    else:arrays,counters=execute(name,start,counts,order)
    prefix=' '.join(map(str,counters+counts))
    return ''.join(f'{name}-{suffix} {prefix} '+' '.join(map(str,values))+'\n'
        for suffix,values in zip(['a','b','c'],arrays))


def fixture_calls():
    main=SOURCE.read_text().split('int main(void)',1)[1]
    return [(name,*map(int,args.split(','))) for name,args in re.findall(r'(deep_\w+)\(([-\d,]+)\);',main)]


def expected_output():
    return ''.join(model(name,start,counts) for name,start,*counts in fixture_calls())


def loop_template(dimensions,permutation=None,reverse=False):
    permutation=permutation or list(range(dimensions))
    arguments=[]
    for axis in range(dimensions):
        position=dimensions-1-permutation.index(axis)
        arguments.append(f'(scale -1 (var {position}))' if reverse and axis==dimensions-1 else f'(var {position})')
    code='(each (instr current ('+' '.join(arguments)+')))'
    for depth in reversed(range(dimensions)):
        if reverse and depth==dimensions-1:
            lower=f'(sum (constant 1) (scale -1 (var {2*depth})))'; upper='(constant 1)'
        else:lower='(constant 0)';upper=f'(var {depth+permutation[depth]})'
        code=f'(loop {lower} {upper} {code})'
    if reverse:
        code=f'(map-index ((reflect {dimensions-1})) {code})'
    elif permutation!=list(range(dimensions)):code=f'(reindex (0) {code})'
    return code


def schedule_template(dimensions,swap=False,fission=False):
    rows=[]
    for axis in range(dimensions):
        coefficients=[0]*dimensions+[int(position==axis) for position in range(dimensions)]
        rows.append('(affine ('+' '.join(map(str,coefficients))+') 0)')
    if swap:rows[0],rows[1]=rows[1],rows[0]
    rows=['ordinal']+rows if fission else rows+['ordinal']
    return '(schedule ('+' '.join(rows)+') '+('((swap 0))' if swap else '()')+')'


def templates():
    result={f'identity-{depth}':loop_template(depth) for depth in [4,5,6,8,9]}
    for depth in [4,5,6]:result[f'interchange-{depth}']=loop_template(depth,[1,0]+list(range(2,depth)))
    result|={'reverse-last-4':loop_template(4,reverse=True),
        'schedule-identity-4':schedule_template(4),'schedule-interchange-4':schedule_template(4,swap=True),
        'schedule-fission-4':schedule_template(4,fission=True),
        'tile-2-3':'(tile 2 3)','tile-4-4':'(tile 4 4)','tile-17-13':'(tile 17 13)'}
    return result


def main():
    stamp=json.loads((COMPILER.parent/'.guard-build.json').read_text())
    assert stamp['proved_entrypoint']==ENTRY and stamp['compiler_sha256']==hashlib.sha256(COMPILER.read_bytes()).hexdigest()
    for path,expected in (stamp['proof_sources']|stamp['native_sources']).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==expected,path
    WORK.mkdir(parents=True,exist_ok=True)
    subprocess.run(['gcc','-O0','-fwrapv',str(SOURCE),'-o',str(WORK/'gcc-reference')],capture_output=True,check=True)
    reference=subprocess.check_output([str(WORK/'gcc-reference')],text=True)
    assert reference==expected_output();(WORK/'gcc-output.txt').write_text(reference)
    cases=[]
    for name,syntax in templates().items():
        path=WORK/(name+'.sexp');path.write_text(syntax+'\n');cases.append((name,path,{}))
    cases.extend((name,WORK/'interchange-4.sexp',extra) for name,extra in [
        ('resource-limit',{'GUARDCERT_FM_ROWS':'0'}),('invalid-certificate',{'GUARDCERT_ORACLE_FAULT':'top-certificate'})])
    configurations={}
    for name,path,extra in cases:
        work=WORK/name;work.mkdir(parents=True,exist_ok=True)
        result=subprocess.run([str(COMPILER),'-conf',str(COMPILER.parent/'compcert.ini'),
            '-stdlib',str(COMPILER.parent/'runtime'),'-dclight','-S','-o',str(work/'recursive.s'),str(SOURCE)],
            cwd=work,env=os.environ|{'GUARDCERT_LOOP_CANDIDATE':str(path)}|extra,
            capture_output=True,text=True,check=True,timeout=600)
        (work/'compiler-output.txt').write_text(result.stdout+result.stderr)
        subprocess.run(['gcc',str(work/'recursive.s'),'-o',str(work/'recursive')],capture_output=True,check=True)
        output=subprocess.check_output([str(work/'recursive')],text=True);assert output==reference,name
        (work/'output.txt').write_text(output)
        dump=(work/(SOURCE.stem+'.light.c')).read_text()
        observed={fn for fn in METADATA if 'switch (0)' in function_body(dump,fn)}
        assert not observed&REFUSED,(name,observed&REFUSED)
        if name in {'identity-4','interchange-4'}:assert observed==FOUR,(name,observed)
        elif name in {'schedule-identity-4','schedule-interchange-4'}:
            # Schedule rows are zero extended for a larger source context.
            # They do not prescribe the source rank, unlike explicit Loop ASTs.
            assert FOUR<=observed<=FOUR|{'deep_five','deep_six','deep_eight'},(name,observed)
        elif name=='reverse-last-4':assert observed==FOUR-{'deep_four_chain','deep_four_recurrence'},(name,observed)
        elif name=='schedule-fission-4':
            assert FOUR-{'deep_four_chain'}<=observed<=(FOUR-{'deep_four_chain'})|{'deep_five','deep_six','deep_eight'},(name,observed)
        elif name in {'identity-5','interchange-5'}:assert observed=={'deep_five'},(name,observed)
        elif name in {'identity-6','interchange-6'}:assert observed=={'deep_six'},(name,observed)
        elif name=='identity-8':assert observed=={'deep_eight'},(name,observed)
        elif name.startswith('tile-'):assert observed==FOUR|{'deep_five','deep_six'},(name,observed)
        else:assert not observed,(name,observed)
        limits={}
        for fn in observed:
            body=function_body(dump,fn);start=body.index('switch (0)');fast=body[start:body.index('continue;',start)]
            dimensions,_=METADATA[fn]
            for identifier,bound in zip(IDENTIFIERS[:dimensions],BOUNDS):
                assert f'${identifier} = ${bound};' in fast,(name,fn,'public exit',identifier)
            values=re.findall(r'\$(?:n|m|p|q|r|s|h|z|g)\s*<=\s*(\d+)',fast)
            assert len(values)>=dimensions,(name,fn,'complete bound guard')
            limits[fn]=min(map(int,values))
        configurations[name]={'guarded_functions':sorted(observed),'common_guard_cap':limits,
            'full_output_lines':len(reference.splitlines()),'gcc_and_independent_model_match':True,
            'template_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
        (WORK/'partial-report.json').write_text(json.dumps(configurations,indent=2)+'\n')
        print(name,sorted(observed),limits,flush=True)
    (WORK/'report.json').write_text(json.dumps({'status':'passed','proved_entrypoint':ENTRY,
        'compiler_sha256':stamp['compiler_sha256'],'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'configurations':configurations,'machine_signed_wrap_model':True,
        'scope':'recursive counted C loops; four, five, six and eight source dimensions; nine-axis and eight-axis tiled candidates exceed current fresh pool'},indent=2)+'\n')


if __name__=='__main__':main()
