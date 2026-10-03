"""Full-program checks for guarded source loops with multiple pointer bases."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from native_zero_trip import function_body
from native_memory_recursive import loop_template
from native_memory_pointer import word

SOURCE = ROOT / 'examples/native_memory_multi_pointer.c'
COMPILER = ROOT / 'build/compcert-memory-unified/ccomp'
WORK = ROOT / 'build/native-memory-multi-pointer'
ENTRY = 'GuardMemoryUnifiedCompiler.compile_memory_unified_regions'
NAMES = ['multi_copy', 'multi_combine', 'multi_chain', 'multi_reflected',
         'multi_context', 'multi_undef', 'multi_tiny']


def execute(name, args, order=None):
    tiny = name == 'multi_tiny'
    if tiny:
        start, n, m, alpha, beta = args
        buffers = [[1, 4], [7, 12]]
        p, q, r = (0, 0), (1, 0), None
    else:
        kind, p_offset, q_offset, start, n, m, alpha, beta = args
        buffers = [[3*x+1 for x in range(256)], [5*x+7 for x in range(256)],
                   [7*x+11 for x in range(256)]]
        p = (0, p_offset)
        q = (0 if kind == 1 else 1, q_offset)
        r = (1, q_offset) if kind == 2 else (2, 0)
        if kind == 3:
            p = q = r = None
    counters = [start, 77]
    for _ in range(2 if name == 'multi_context' else 1):
        if name == 'multi_context':
            counters[0] = start
        points = []
        while counters[0] < n:
            counters[1] = 0
            while counters[1] < m:
                points.extend(((tuple(counters), site) for site in range(2 if name == 'multi_chain' else 1)))
                counters[1] += 1
            counters[0] += 1
        if order is not None:
            points.sort(key=order)
        if name == 'multi_undef':
            assert not points
        for (i, j), site in points:
            assert p is not None and q is not None
            index = (2 if tiny else 8)*i+j
            def read(pointer, address):
                assert pointer is not None
                return buffers[pointer[0]][pointer[1]+address]
            def write(pointer, address, value):
                assert pointer is not None
                buffers[pointer[0]][pointer[1]+address] = word(value)
            if name in {'multi_copy', 'multi_tiny'}:
                write(p, index, read(q, index)*alpha+beta)
            elif name == 'multi_combine':
                write(p, index, read(q, index)*alpha+read(r, index)*beta+i*j)
            elif name == 'multi_reflected':
                write(p, index, read(q, 63-8*i-j)*alpha+beta)
            elif name == 'multi_context':
                write(p, index, read(q, index)*alpha+read(p, index)+beta)
            elif name == 'multi_chain':
                if site == 0:
                    write(p, index, read(q, index)*alpha+beta)
                else:
                    write(q, index+1, read(p, index)+read(q, index+1)*beta)
            else:
                raise AssertionError(name)
    return buffers, counters


def model(name, args, order=None):
    buffers, counters = execute(name, args, order)
    values = [value for row in zip(*buffers) for value in row] if name != 'multi_tiny' else sum(buffers, [])
    return name+' '+' '.join(map(str, args+counters+values))+'\n'


def fixture_calls():
    main = SOURCE.read_text().split('int main(void)', 1)[1]
    calls = [(name, [int(arg.replace('-2147483647-1', '-2147483648')) for arg in args.split(',')])
             for name, args in re.findall(r'run\("(multi_\w+)",multi_\w+,([-\d,]+)\);', main)]
    calls += [('multi_tiny', list(map(int, args.split(','))))
              for args in re.findall(r'run_tiny\(([-\d,]+)\);', main)]
    return calls


def templates():
    return {'identity-2': loop_template(2), 'interchange-2': loop_template(2, [1, 0]),
            'reverse-last-2': loop_template(2, reverse=True),
            'schedule-identity-2': '(schedule ((coordinate 0) (coordinate 1) ordinal) ())',
            'schedule-interchange-2': '(schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0)))',
            'schedule-fission-2': '(schedule (ordinal (coordinate 0) (coordinate 1)) ())',
            'tile-2-3': '(tile 2 3)', 'tile-4-4': '(tile 4 4)', 'tile-17-13': '(tile 17 13)'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cases')
    parser.add_argument('--reference-only', action='store_true')
    options = parser.parse_args()
    WORK.mkdir(parents=True, exist_ok=True)
    subprocess.run(['gcc', '-O0', '-fwrapv', str(SOURCE), '-o', str(WORK/'gcc-reference')], check=True)
    reference = subprocess.check_output([str(WORK/'gcc-reference')], text=True)
    calls = fixture_calls()
    expected = ''.join(model(name, args) for name, args in calls)
    assert reference == expected, 'GCC and independent machine-word model disagree'
    (WORK/'gcc-output.txt').write_text(reference)
    if options.reference_only:
        print('GCC and word model agree:', len(calls), 'calls')
        return
    stamp = json.loads((COMPILER.parent/'.guard-build.json').read_text())
    assert stamp['proved_entrypoint'] == ENTRY
    assert stamp['compiler_sha256'] == hashlib.sha256(COMPILER.read_bytes()).hexdigest()
    for path, digest in (stamp['proof_sources'] | stamp['native_sources']).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    cases = []
    for name, syntax in templates().items():
        path = WORK/(name+'.sexp')
        path.write_text(syntax+'\n')
        cases.append((name, path, {}))
    cases.extend((name, WORK/'interchange-2.sexp', extra) for name, extra in [
        ('resource-limit', {'GUARDCERT_FM_ROWS': '0'}),
        ('invalid-certificate', {'GUARDCERT_ORACLE_FAULT': 'top-certificate'})])
    selected = set(options.cases.split(',')) if options.cases else {name for name, _, _ in cases}
    assert selected <= {name for name, _, _ in cases}
    configurations = {}
    for name, path, extra in cases:
        if name not in selected:
            continue
        work = WORK/name
        work.mkdir(exist_ok=True)
        result = subprocess.run([str(COMPILER), '-conf', str(COMPILER.parent/'compcert.ini'),
            '-stdlib', str(COMPILER.parent/'runtime'), '-dclight', '-S', '-o', str(work/'multi.s'), str(SOURCE)],
            cwd=work, env=os.environ | {'GUARDCERT_LOOP_CANDIDATE': str(path)} | extra,
            capture_output=True, text=True, check=True, timeout=600)
        (work/'compiler-output.txt').write_text(result.stdout+result.stderr)
        subprocess.run(['gcc', str(work/'multi.s'), '-o', str(work/'multi')], check=True)
        output = subprocess.check_output([str(work/'multi')], text=True)
        assert output == reference, name
        (work/'output.txt').write_text(output)
        dump = (work/(SOURCE.stem+'.light.c')).read_text()
        observed = {fn for fn in NAMES if 'switch (0)' in function_body(dump, fn)}
        assert observed == (set() if extra else set(NAMES)), (name, observed)
        caps = {}
        for fn in observed:
            body = function_body(dump, fn)
            begin = body.index('switch (0)')
            fast = body[begin:body.index('continue;', begin)]
            caps[fn] = min(int(re.search(r'\$'+bound+r'\s*<=\s*(\d+)', fast).group(1)) for bound in ['n', 'm'])
            assert '<>' in fast or '!=' in fast, (name, fn, 'no pointer separation tests')
            assert '$i = $n;' in fast and '$j = $m;' in fast, (name, fn)
        configurations[name] = {'guarded_functions': sorted(observed), 'common_guard_cap': caps,
            'actual_calls': len(calls), 'full_output_lines': len(reference.splitlines()),
            'gcc_and_word_model_match': True,
            'template_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
        (WORK/'partial-report.json').write_text(json.dumps(configurations, indent=2)+'\n')
        print(name, sorted(observed), caps, flush=True)
    report = {'status': 'passed', 'proved_entrypoint': ENTRY, 'compiler_sha256': stamp['compiler_sha256'],
        'source_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(), 'configurations': configurations,
        'full_configuration_suite': not bool(options.cases),
        'scope': 'actual multiple-pointer source reads and writes, dynamic separation guards, complete Csem-to-Asm compilation and full outputs'}
    (WORK/('smoke-report.json' if options.cases else 'report.json')).write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
