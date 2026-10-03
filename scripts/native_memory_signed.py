"""Development checks for signed affine source accesses in the proved compiler."""
from pathlib import Path
import argparse
import hashlib
import itertools
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
from native_zero_trip import function_body
from native_memory_recursive import loop_template
from native_memory_pointer import word

SOURCE = ROOT/'examples/native_memory_signed.c'
COMPILER = ROOT/'build/compcert-memory-unified/ccomp'
WORK = ROOT/'build/native-memory-signed'
ENTRY = 'GuardMemoryUnifiedCompiler.compile_memory_unified_regions'
NAMES = ['signed_read','signed_write','signed_chain','signed_context','signed_three',
    'signed_undef','signed_mixed','signed_address_wrap','signed_array','signed_array_no_zero_anchor']
RANK = {name: 3 if name=='signed_three' else 2 for name in NAMES}
SUPPORTED = set(NAMES)-{'signed_array_no_zero_anchor'}
SIZE = 256


def execute(name, offset, start, n, m, p, alpha, beta, order=None):
    buffers = [[3*x+1 for x in range(SIZE)] for _ in range(3 if name=='signed_array' else
        2 if name=='signed_array_no_zero_anchor' else 1)]
    counters = [start,77]+([55] if RANK[name]==3 else [])
    counts = [n,m]+([p] if RANK[name]==3 else [])
    for repeat in range(2 if name=='signed_context' else 1):
        if name=='signed_context': counters[0]=start
        points=[]
        def visit(axis):
            while counters[axis]<counts[axis]:
                if axis+1<len(counters):
                    counters[axis+1]=0
                    visit(axis+1)
                else:
                    points.extend((tuple(counters),site) for site in
                        range(2 if name in {'signed_chain','signed_array'} else 1))
                counters[axis]+=1
        visit(0)
        if order is not None: points.sort(key=order)
        if name=='signed_undef': assert not points
        for coordinates, site in points:
            i,j=coordinates[:2]
            positive=8*i+j
            reflected=(56-8*i+j if name=='signed_mixed' else 63-positive)
            if name.startswith('signed_array'):
                a,b=buffers[:2]
                if name=='signed_array_no_zero_anchor':
                    b[reflected]=word(a[reflected]*alpha+beta)
                else:
                    c=buffers[2]
                    if site==0: c[reflected]=word(a[positive]*alpha+b[positive]*beta)
                    else: c[positive]=word(c[positive]+a[reflected]*beta)
                continue
            assert offset>=0, 'zero-trip execution must not dereference NULL'
            buf=buffers[0]
            positive+=offset;reflected+=offset
            if name in {'signed_read','signed_context','signed_mixed','signed_address_wrap'}:
                buf[positive]=word(buf[reflected]*alpha+buf[positive]+beta+i*j)
            elif name=='signed_write':
                buf[reflected]=word(buf[positive]*alpha+beta)
            elif name=='signed_chain':
                if site==0: buf[reflected]=word(buf[reflected]*alpha+beta)
                else: buf[reflected-1]=word(buf[reflected]+buf[reflected-1]*beta)
            elif name=='signed_three':
                k=coordinates[2];positive=offset+32*i+4*j+k;reflected=offset+111-32*i-4*j-k
                buf[positive]=word(buf[reflected]*alpha+beta+i*k+j)
            else: raise AssertionError(name)
    return buffers,counters


def model(name,args,order=None):
    if name.startswith('signed_array'):
        start,n,m,alpha,beta=args
        buffers,counters=execute(name,0,start,n,m,1,alpha,beta,order)
        values=[value for column in zip(*buffers) for value in column]
        return name+' '+' '.join(map(str,args+counters+values))+'\n'
    buffers,counters=execute(name,*args,order=order)
    return name+' '+' '.join(map(str,args+counters+buffers[0]))+'\n'


def fixture_calls():
    main=SOURCE.read_text().split('int main(void)',1)[1]
    return [(name,list(map(int,args.split(',')))) for name,args in
        re.findall(r'(?:run_)?(signed_\w+)\(([-\d,]+)\);',main)]


def templates():
    result={f'identity-{d}':loop_template(d) for d in [2,3]}
    result|={f'interchange-{d}':loop_template(d,[1,0]+list(range(2,d))) for d in [2,3]}
    result|={'reverse-last-2':loop_template(2,reverse=True),
        'schedule-identity-2':'(schedule ((coordinate 0) (coordinate 1) ordinal) ())',
        'schedule-interchange-2':'(schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0)))',
        'schedule-fission-2':'(schedule (ordinal (coordinate 0) (coordinate 1)) ())',
        'tile-2-3':'(tile 2 3)','tile-4-4':'(tile 4 4)','tile-17-13':'(tile 17 13)'}
    return result


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cases');options=parser.parse_args()
    stamp=json.loads((COMPILER.parent/'.guard-build.json').read_text())
    assert stamp['proved_entrypoint']==ENTRY
    assert stamp['compiler_sha256']==hashlib.sha256(COMPILER.read_bytes()).hexdigest()
    for path,digest in (stamp['proof_sources']|stamp['native_sources']).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    WORK.mkdir(parents=True,exist_ok=True)
    subprocess.run(['gcc','-O0','-fwrapv',str(SOURCE),'-o',str(WORK/'gcc-reference')],check=True)
    reference=subprocess.check_output([str(WORK/'gcc-reference')],text=True)
    expected=''.join(model(name,args) for name,args in fixture_calls())
    assert reference==expected,'GCC and independent word model disagree'
    (WORK/'gcc-output.txt').write_text(reference)
    cases=[]
    for name,syntax in templates().items():
        path=WORK/(name+'.sexp');path.write_text(syntax+'\n');cases.append((name,path,{}))
    cases.extend((name,WORK/'interchange-2.sexp',extra) for name,extra in [
        ('resource-limit',{'GUARDCERT_FM_ROWS':'0'}),
        ('invalid-certificate',{'GUARDCERT_ORACLE_FAULT':'top-certificate'})])
    selected=set(options.cases.split(',')) if options.cases else {name for name,_,_ in cases}
    assert selected<={name for name,_,_ in cases}
    configurations={}
    for name,path,extra in cases:
        if name not in selected:continue
        work=WORK/name;work.mkdir(exist_ok=True)
        result=subprocess.run([str(COMPILER),'-conf',str(COMPILER.parent/'compcert.ini'),
            '-stdlib',str(COMPILER.parent/'runtime'),'-dclight','-S','-o',str(work/'signed.s'),str(SOURCE)],
            cwd=work,env=os.environ|{'GUARDCERT_LOOP_CANDIDATE':str(path)}|extra,
            capture_output=True,text=True,check=True,timeout=600)
        (work/'compiler-output.txt').write_text(result.stdout+result.stderr)
        subprocess.run(['gcc',str(work/'signed.s'),'-o',str(work/'signed')],check=True)
        output=subprocess.check_output([str(work/'signed')],text=True)
        assert output==reference,name
        (work/'output.txt').write_text(output)
        dump=(work/(SOURCE.stem+'.light.c')).read_text()
        observed={fn for fn in NAMES if 'switch (0)' in function_body(dump,fn)}
        if name.startswith(('identity-','interchange-')):
            rank=int(name.rsplit('-',1)[1]);assert observed=={fn for fn in SUPPORTED if RANK[fn]==rank},(name,observed)
        elif name=='reverse-last-2':assert observed=={fn for fn in SUPPORTED if RANK[fn]==2},(name,observed)
        elif name.startswith('schedule-'):assert {fn for fn in SUPPORTED if RANK[fn]==2}<=observed<=SUPPORTED,(name,observed)
        elif name.startswith('tile-'):assert observed==SUPPORTED,(name,observed)
        else:assert not observed,(name,observed)
        caps={}
        for fn in observed:
            body=function_body(dump,fn);begin=body.index('switch (0)');fast=body[begin:body.index('continue;',begin)]
            caps[fn]=min(map(int,re.findall(r'\$(?:n|m|p)\s*<=\s*(\d+)',fast)))
            for iterator,bound in zip(['i','j','k'],['n','m','p']):
                if iterator in ['i','j','k'][:RANK[fn]]:assert f'${iterator} = ${bound};' in fast,(name,fn,iterator)
            first_assignment=re.search(r'\$\d+\s*=',fast);assert first_assignment,(name,fn)
            guard=fast[:first_assignment.start()]
            assert not any('$'+parameter in guard for parameter in ['alpha','beta','unused_alpha']),(name,fn,guard)
        configurations[name]={'guarded_functions':sorted(observed),'common_guard_cap':caps,
            'full_output_lines':len(reference.splitlines()),'actual_calls':len(fixture_calls()),
            'gcc_and_word_model_match':True,'template_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
        (WORK/'partial-report.json').write_text(json.dumps(configurations,indent=2)+'\n')
        print(name,sorted(observed),caps,flush=True)
    report={'status':'passed','proved_entrypoint':ENTRY,'compiler_sha256':stamp['compiler_sha256'],
        'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'configurations':configurations,
        'full_configuration_suite':not bool(options.cases),'machine_signed_wrap_model':True,
        'scope':'actual signed affine array and pointer source accesses, schedules, tiles, full memory and public counters through complete Csem-to-Asm compilation'}
    (WORK/('smoke-report.json' if options.cases else 'report.json')).write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':main()
