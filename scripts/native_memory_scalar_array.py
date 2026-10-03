"""Check fixed-array scalar transformations through the complete C compiler."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
from native_zero_trip import function_body
from native_memory_scalar import templates, word

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'examples/native_memory_scalar_array.c'
COMPILER = ROOT/'build/compcert-memory-unified/ccomp'
WORK = ROOT/'build/native-memory-scalar-array'
ENTRY = 'GuardMemoryUnifiedCompiler.compile_memory_unified_regions'
SIZE = 256
METADATA = {name: 2 for name in ['array_scalar_axpy', 'array_scalar_global',
    'array_scalar_context', 'array_scalar_wrap', 'array_scalar_chain',
    'array_scalar_recurrence', 'array_scalar_bound', 'array_scalar_many',
    'array_scalar_undef', 'array_scalar_nonlinear', 'array_scalar_mutated']}
METADATA |= {'array_scalar_three': 3, 'array_scalar_four': 4}
STRIDES = {2: [8, 1], 3: [64, 8, 1], 4: [64, 16, 4, 1]}
REFUSED = {'array_scalar_nonlinear', 'array_scalar_mutated'}
SUPPORTED = set(METADATA)-REFUSED
IDENTIFIERS = ['i', 'j', 'k', 't']
BOUNDS = ['n', 'm', 'p', 'q']


def execute(name, start, counts, parameters, order=None):
    depth = METADATA[name]
    alpha, beta, gamma = parameters
    wrap = name.endswith('_wrap')
    a = [2147483647-x if wrap else 3*x+1 for x in range(SIZE)]
    b = [2147483647-2*x if wrap else 5*x+2 for x in range(SIZE)]
    c = [2147483647-3*x if wrap else -777 for x in range(SIZE)]
    counters = [start]+[77, 55, 33][:depth-1]
    for _ in range(2 if name.endswith('_context') else 1):
        if name.endswith('_context'):
            counters[0] = start
        points = []

        def visit(axis):
            while counters[axis] < counts[axis]:
                if axis+1 < depth:
                    counters[axis+1] = 0
                    visit(axis+1)
                else:
                    points.extend((tuple(counters), site)
                        for site in range(3 if name.endswith('_chain') else 1))
                counters[axis] += 1

        visit(0)
        if order is not None:
            points.sort(key=order)
        if name.endswith('_undef'):
            assert not points, 'an uninitialized scalar must remain unused'
        for coordinates, site in points:
            index = sum(x*s for x, s in zip(coordinates, STRIDES[depth]))
            assert 0 <= index < SIZE
            i, j = coordinates[:2]
            term = (i*j+7 if depth == 2 else i*coordinates[2]+j+9 if depth == 3
                else i*j+coordinates[2]*coordinates[3]+11)
            if name.endswith('_chain'):
                assert index+1 < SIZE
                if site == 0:
                    b[index] = word(a[index]*alpha+beta+term)
                elif site == 1:
                    c[index] = word(b[index]+b[index+1]*alpha)
                else:
                    b[index] = word(c[index]-beta)
            elif name.endswith('_recurrence'):
                assert index+1 < SIZE
                b[index] = word(b[index]+b[index+1]*alpha+beta)
            elif name.endswith('_bound'):
                c[index] = word(a[index]*counts[0]+b[index]*counts[1]+term)
            elif name.endswith('_many'):
                c[index] = word(a[index]*alpha+b[index]*beta*gamma+term)
            elif name.endswith('_nonlinear'):
                c[index] = word(a[i*j]*alpha+b[index]*beta+term)
            else:
                if name.endswith('_mutated'):
                    alpha = word(alpha+1)
                c[index] = word(a[index]*alpha+b[index]*beta+term)
    return (a, b, c), counters, [alpha, beta, gamma]


def model(name, start, counts, parameters, order=None):
    arrays, counters, final_parameters = execute(name, start, counts, parameters, order)
    prefix = ' '.join(map(str, counters+list(counts)+final_parameters))
    return ''.join(f'{name}-{suffix} {prefix} '+' '.join(map(str, values))+'\n'
        for suffix, values in zip('abc', arrays))


def fixture_calls():
    main = SOURCE.read_text().split('int main(void)', 1)[1]
    return [(name, *map(int, args.split(','))) for name, args in
        re.findall(r'(array_scalar_\w+)\(([-\d,]+)\);', main)]


def expected_output():
    return ''.join(model(name, args[0], args[1:1+METADATA[name]], args[-3:])
        for name, *args in fixture_calls())


def expected_acceptance(configuration, observed):
    assert not observed & REFUSED, (configuration, observed & REFUSED)
    if configuration.startswith(('identity-', 'interchange-')):
        rank = int(configuration.rsplit('-', 1)[1])
        assert observed == {fn for fn in SUPPORTED if METADATA[fn] == rank}, (configuration, observed)
    elif configuration == 'reverse-last-2':
        assert observed == {fn for fn in SUPPORTED if METADATA[fn] == 2}, (configuration, observed)
    elif configuration.startswith('schedule-'):
        assert {fn for fn in SUPPORTED if METADATA[fn] == 2} <= observed <= SUPPORTED, (configuration, observed)
    elif configuration.startswith('tile-'):
        assert observed == SUPPORTED, (configuration, observed)
    else:
        assert not observed, (configuration, observed)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cases', help='comma-separated configurations for smoke checks')
    arguments = parser.parse_args()
    stamp = json.loads((COMPILER.parent/'.guard-build.json').read_text())
    assert stamp['proved_entrypoint'] == ENTRY
    assert stamp['compiler_sha256'] == hashlib.sha256(COMPILER.read_bytes()).hexdigest()
    for path, digest in (stamp['proof_sources'] | stamp['native_sources']).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    WORK.mkdir(parents=True, exist_ok=True)
    subprocess.run(['gcc', '-O0', '-fwrapv', str(SOURCE), '-o', str(WORK/'gcc-reference')],
        capture_output=True, check=True)
    reference = subprocess.check_output([str(WORK/'gcc-reference')], text=True)
    assert reference == expected_output(), 'independent word model disagrees with GCC'
    (WORK/'gcc-output.txt').write_text(reference)
    cases = []
    for name, syntax in templates().items():
        path = WORK/(name+'.sexp')
        path.write_text(syntax+'\n')
        cases.append((name, path, {}))
    cases += [(name, WORK/'interchange-2.sexp', extra) for name, extra in [
        ('resource-limit', {'GUARDCERT_FM_ROWS': '0'}),
        ('invalid-certificate', {'GUARDCERT_ORACLE_FAULT': 'top-certificate'})]]
    selected = set(arguments.cases.split(',')) if arguments.cases else {name for name, _, _ in cases}
    assert selected <= {name for name, _, _ in cases}
    configurations = {}
    for name, path, extra in cases:
        if name not in selected:
            continue
        work = WORK/name
        work.mkdir(parents=True, exist_ok=True)
        result = subprocess.run([str(COMPILER), '-conf', str(COMPILER.parent/'compcert.ini'),
            '-stdlib', str(COMPILER.parent/'runtime'), '-dclight', '-S',
            '-o', str(work/'scalar-array.s'), str(SOURCE)], cwd=work,
            env=os.environ | {'GUARDCERT_LOOP_CANDIDATE': str(path)} | extra,
            capture_output=True, text=True, check=True, timeout=600)
        (work/'compiler-output.txt').write_text(result.stdout+result.stderr)
        subprocess.run(['gcc', str(work/'scalar-array.s'), '-o', str(work/'scalar-array')],
            capture_output=True, check=True)
        output = subprocess.check_output([str(work/'scalar-array')], text=True)
        assert output == reference, name
        (work/'output.txt').write_text(output)
        dump = (work/(SOURCE.stem+'.light.c')).read_text()
        observed = {fn for fn in METADATA if 'switch (0)' in function_body(dump, fn)}
        expected_acceptance(name, observed)
        limits = {}
        for fn in observed:
            body = function_body(dump, fn)
            begin = body.index('switch (0)')
            fast = body[begin:body.index('continue;', begin)]
            for iterator, bound in zip(IDENTIFIERS[:METADATA[fn]], BOUNDS):
                assert f'${iterator} = ${bound};' in fast, (name, fn, 'public counter exit', iterator)
            values = re.findall(r'\$(?:n|m|p|q)\s*<=\s*(\d+)', fast)
            assert len(values) >= METADATA[fn], (name, fn, 'complete count guard')
            limits[fn] = min(map(int, values))
            first_assignment = re.search(r'\$\d+\s*=', fast)
            assert first_assignment, (name, fn, 'missing candidate counter initialization')
            guard = fast[:first_assignment.start()]
            assert not any('$'+p in guard for p in ['alpha', 'beta', 'gamma', 'unused_alpha']), (name, fn, guard)
        configurations[name] = {'guarded_functions': sorted(observed), 'common_guard_cap': limits,
            'full_output_lines': len(reference.splitlines()), 'gcc_and_word_model_match': True,
            'template_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
        (WORK/'partial-report.json').write_text(json.dumps(configurations, indent=2)+'\n')
        print(name, sorted(observed), limits, flush=True)
    report = {'status': 'passed', 'proved_entrypoint': ENTRY, 'compiler_sha256': stamp['compiler_sha256'],
        'source_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(), 'configurations': configurations,
        'full_configuration_suite': not bool(arguments.cases), 'machine_signed_wrap_model': True,
        'scope': 'stable RHS scalars in actual local/global fixed arrays, actual dependency checking and complete Csem-to-Asm compilation'}
    (WORK/('smoke-report.json' if arguments.cases else 'report.json')).write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
