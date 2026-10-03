"""Exercise explicit source metadata in untrusted coordinate schedule proposals."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
from native_zero_trip import function_body

SOURCE = ROOT/'examples/native_memory_source_metadata.c'
COMPILER = ROOT/'build/compcert-memory-unified/ccomp'
WORK = ROOT/'build/native-memory-source-metadata'
NAMES = ['unused_inner', 'unused_all', 'context_three']


def word(value):
    return (value+2**31) % 2**32-2**31


def reference_model():
    result = ''
    for n in range(6):
        for m in range(6):
            for name in ['inner', 'all']:
                a, b = [3*i+1 for i in range(64)], [5*i+7 for i in range(64)]
                for i in range(n):
                    for j in range(m):
                        index = i if name == 'inner' else 0
                        a[index] = word(b[index]*-7+(j*11 if name == 'inner' else 11))
                values = [name, n, m, n, m if n else 77]+[x for pair in zip(a,b) for x in pair]
                result += ' '.join(map(str,values))+'\n'
    for n in range(5):
        for m in range(4):
            a, b = [3*i+1 for i in range(64)], [5*i+7 for i in range(64)]
            for i in range(n):
                for j in range(max(0,i+m-1)):
                    index = 8*i+j
                    a[index] = word(a[index]+b[index]+i*j+7)
            k = n+m-2 if n else 55
            values = ['context',n,m,n,max(0,k) if n else 77,k]+[x for pair in zip(a,b) for x in pair]
            result += ' '.join(map(str,values))+'\n'
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--reference-only', action='store_true')
    parser.add_argument('--cases')
    options = parser.parse_args()
    WORK.mkdir(parents=True, exist_ok=True)
    subprocess.run(['gcc','-O0','-fwrapv',str(SOURCE),'-o',str(WORK/'reference')],check=True)
    reference = subprocess.check_output([str(WORK/'reference')],text=True)
    assert reference == reference_model()
    (WORK/'reference-output.txt').write_text(reference)
    if options.reference_only:
        print('GCC and model agree:',len(reference.splitlines()),'calls')
        return
    stamp = json.loads((COMPILER.parent/'.guard-build.json').read_text())
    assert stamp['proved_entrypoint'] == 'GuardMemoryUnifiedCompiler.compile_memory_unified_regions'
    assert stamp['compiler_sha256'] == hashlib.sha256(COMPILER.read_bytes()).hexdigest()
    for path,digest in (stamp['proof_sources']|stamp['native_sources']).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest,path
    templates = {
        'schedule-identity': '(schedule ((coordinate 0) (coordinate 1) ordinal) ())',
        'schedule-interchange': '(schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0)))',
        'schedule-fission': '(schedule (ordinal (coordinate 0) (coordinate 1)) ())',
        'tile-2-3': '(tile 2 3)', 'tile-4-4': '(tile 4 4)', 'tile-17-13': '(tile 17 13)',
        'invalid-coordinate': '(schedule ((coordinate 2) ordinal) ())'}
    cases = [(name,syntax,{}) for name,syntax in templates.items()]
    cases += [(name,templates['schedule-interchange'],extra) for name,extra in [
        ('resource-limit',{'GUARDCERT_FM_ROWS':'0'}),
        ('invalid-certificate',{'GUARDCERT_ORACLE_FAULT':'top-certificate'})]]
    selected = set(options.cases.split(',')) if options.cases else {name for name,_,_ in cases}
    assert selected <= {name for name,_,_ in cases}
    configurations = {}
    for name,syntax,extra in cases:
        if name not in selected:
            continue
        work = WORK/name
        work.mkdir(exist_ok=True)
        template = work/'candidate.sexp'
        template.write_text(syntax+'\n')
        compiled = subprocess.run([str(COMPILER),'-conf',str(COMPILER.parent/'compcert.ini'),
            '-stdlib',str(COMPILER.parent/'runtime'),'-dclight','-S','-o',str(work/'metadata.s'),str(SOURCE)],
            cwd=work,env=os.environ|{'GUARDCERT_LOOP_CANDIDATE':str(template)}|extra,
            capture_output=True,text=True,check=True,timeout=600)
        (work/'compiler-output.txt').write_text(compiled.stdout+compiled.stderr)
        subprocess.run(['gcc',str(work/'metadata.s'),'-o',str(work/'metadata')],check=True)
        output = subprocess.check_output([str(work/'metadata')],text=True)
        assert output == reference,name
        (work/'output.txt').write_text(output)
        dump = (work/(SOURCE.stem+'.light.c')).read_text()
        guarded = {fn for fn in NAMES if 'switch (0)' in function_body(dump,fn)}
        expected = set() if extra or name == 'invalid-coordinate' else set(NAMES)
        assert guarded == expected,(name,guarded)
        configurations[name] = {'guarded_functions':sorted(guarded),'actual_calls':len(reference.splitlines()),
            'full_outputs_match_gcc_and_model':True,
            'template_sha256':hashlib.sha256(template.read_bytes()).hexdigest()}
        (WORK/'partial-report.json').write_text(json.dumps(configurations,indent=2)+'\n')
        print(name,sorted(guarded),flush=True)
    report = {'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'configurations':configurations,'full_configuration_suite':not bool(options.cases),
        'scope':'full CompCert assembly execution, unused source coordinates and three context parameters; branch diagnostics separate'}
    (WORK/('smoke-report.json' if options.cases else 'report.json')).write_text(json.dumps(report,indent=2)+'\n')


if __name__ == '__main__':
    main()
