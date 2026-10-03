"""Execute complete programs with loop-based guards over pointer access ranges."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
from native_zero_trip import function_body

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'examples/native_memory_loop_alias.c'
COMPILER = ROOT/'build/compcert-memory-unified/ccomp'
WORK = ROOT/'build/native-memory-loop-alias'
NAMES = ['scan_copy', 'scan_chain', 'scan_undefined']
SIZE = 2300


def word(value):
    return (value+2**31) % 2**32-2**31


def output_model(args, reverse=False):
    which, kind, start, n, alpha, beta = args
    a, b = [3*i+1 for i in range(SIZE)], [5*i+7 for i in range(SIZE)]
    q = b if kind == 0 else a
    offset = {0: 0, 1: 1, 2: 1024, 3: 0, 4: max(0,n), 5: 0}[kind]
    order = list(range(start,n))
    if reverse:
        order.reverse()
    for i in order:
        a[i] = word(q[offset+i]*alpha+beta)
        if which:
            q[offset+i] = word(a[i]+i)
    values = args+[max(start,n)]+[x for pair in zip(a,b) for x in pair]
    return ' '.join(map(str,values))+'\n'


def full_inputs():
    result = [[which,kind,0,n,-7,11]
              for which in range(2) for kind in range(5)
              for n in [0,1,2,9,33,129,511,1024,1025]]
    for which in range(2):
        result += [[which,0,1,33,-2147483648,2147483647],
                   [which,0,0,129,-2147483648,2147483647],
                   [which,5,0,0,3,-7], [which,5,0,-2147483648,3,-7]]
    return result


def reference_model():
    return ''.join(output_model(args) for args in full_inputs())+'undefined 0 0\nundefined -2147483648 0\n'


def check_build():
    stamp = json.loads((COMPILER.parent/'.guard-build.json').read_text())
    assert stamp['proved_entrypoint'] == 'GuardMemoryUnifiedCompiler.compile_memory_unified_regions'
    assert stamp['compiler_sha256'] == hashlib.sha256(COMPILER.read_bytes()).hexdigest()
    for path,digest in (stamp['proof_sources']|stamp['native_sources']).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest,path
    proof = json.loads((ROOT/'build/guard-memory-proof-report.json').read_text())
    assert proof['loop_based_alias_guard_clight_execution_proved']
    assert proof['loop_based_alias_guard_csem_asm_route_proved']
    return stamp


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--reference-only', action='store_true')
    parser.add_argument('--cases')
    options = parser.parse_args()
    WORK.mkdir(parents=True,exist_ok=True)
    subprocess.run(['gcc','-O0','-fwrapv',str(SOURCE),'-o',str(WORK/'reference')],check=True)
    reference = subprocess.check_output([str(WORK/'reference')],text=True)
    assert reference == reference_model()
    (WORK/'reference-output.txt').write_text(reference)
    if options.reference_only:
        print('GCC and model agree: 100 complete source calls')
        return
    stamp = check_build()
    templates = {
        'schedule-identity': '(schedule ((coordinate 0) ordinal) ())',
        'schedule-fission': '(schedule (ordinal (coordinate 0)) ())',
        'schedule-reverse': '(schedule ((affine (0 0 0 -1) 0) ordinal) ())',
        'direct-identity': '(loop (constant 0) (var 0) (each (instr current ((var 0)))))',
        'direct-reverse': '(loop (sum (constant 1) (scale -1 (var 0))) (constant 1) (each (instr current ((scale -1 (var 0))))))',
        'schedule-reflect': '(schedule ((affine (0 0 0 -1) 0) ordinal) ((reflect 0)))',
        'direct-reflect': '(map-index ((reflect 0)) (loop (sum (constant 1) (scale -1 (var 0))) (constant 1) (each (instr current ((scale -1 (var 0)))))))',
        'shift-reflect': '(map-index ((reflect 0) (shift 0 3)) (loop (sum (constant 4) (scale -1 (var 0))) (constant 4) (each (instr current ((sum (constant 3) (scale -1 (var 0))))))))',
        'wrong-reflect': '(map-index ((reflect 0)) (loop (constant 0) (var 0) (each (instr current ((var 0))))))',
        'invalid-coordinate': '(schedule ((coordinate 1) ordinal) ())'}
    cases = [(name,syntax,{}) for name,syntax in templates.items()]
    cases += [(name,templates['schedule-identity'],extra) for name,extra in [
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
        result = subprocess.run([str(COMPILER),'-conf',str(COMPILER.parent/'compcert.ini'),
            '-stdlib',str(COMPILER.parent/'runtime'),'-dclight','-S','-o',str(work/'scan.s'),str(SOURCE)],
            cwd=work,env=os.environ|{'GUARDCERT_LOOP_CANDIDATE':str(template)}|extra,
            capture_output=True,text=True,check=True,timeout=600)
        (work/'compiler-output.txt').write_text(result.stdout+result.stderr)
        subprocess.run(['gcc',str(work/'scan.s'),'-o',str(work/'scan')],check=True)
        output = subprocess.check_output([str(work/'scan')],text=True,timeout=120)
        assert output == reference,name
        (work/'output.txt').write_text(output)
        dump_path = work/(SOURCE.stem+'.light.c')
        dump = dump_path.read_text()
        guarded = {fn for fn in NAMES if 'switch (0)' in function_body(dump,fn)}
        expected = set() if extra or name in {'invalid-coordinate','schedule-reverse','direct-reverse','wrong-reflect'} else set(NAMES)
        assert guarded == expected,(name,guarded)
        for fn in guarded:
            body = function_body(dump,fn)
            assert '<= 1024' in body,(name,fn)
            assert '!= ' in body,(name,fn)
        configurations[name] = {'guarded_functions':sorted(guarded),'actual_calls':100,
            'full_arrays_and_public_counters_match_gcc_and_model':True,
            'clight_bytes':dump_path.stat().st_size,'assembly_bytes':(work/'scan.s').stat().st_size,
            'runtime_count_guard_cap':1024 if guarded else None,
            'negative_one_dimensional_coordinate_candidate_currently_rejected':name in {'schedule-reverse','direct-reverse'},
            'explicit_reflection_map':name in {'schedule-reflect','direct-reflect','shift-reflect'},
            'template_sha256':hashlib.sha256(template.read_bytes()).hexdigest()}
        (WORK/'partial-report.json').write_text(json.dumps(configurations,indent=2)+'\n')
        print(name,sorted(guarded),flush=True)
    report = {'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'configurations':configurations,'full_configuration_suite':not bool(options.cases),
        'scope':'full CompCert assembly execution; dynamic count 0..1025, two-pointer unit-stride copies and chains, same-block slices, alias fallback, undefined empty-loop operands; branch diagnostics separate'}
    (WORK/('smoke-report.json' if options.cases else 'report.json')).write_text(json.dumps(report,indent=2)+'\n')


if __name__ == '__main__':
    main()
