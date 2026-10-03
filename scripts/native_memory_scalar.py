"""Exercise stable RHS parameters through the proved complete C compiler."""
from pathlib import Path
import argparse
import hashlib
import itertools
import json
import os
import re
import subprocess
from native_zero_trip import function_body
from native_memory_recursive import loop_template
from native_memory_pointer import word

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'examples/native_memory_scalar.c'
COMPILER = ROOT/'build/compcert-memory-unified/ccomp'
WORK = ROOT/'build/native-memory-scalar'
ENTRY = 'GuardMemoryUnifiedCompiler.compile_memory_unified_regions'
SIZE = 1568
METADATA = {name: 2 for name in ['scalar_axpy', 'scalar_context', 'scalar_wrap', 'scalar_chain',
    'scalar_recurrence', 'scalar_bound', 'scalar_many', 'scalar_undef', 'scalar_nonlinear',
    'scalar_mutated', 'scalar_multi']}
METADATA |= {'scalar_three': 3, 'scalar_four': 4}
STRIDES = {2: [8, 1], 3: [128, 16, 1], 4: [512, 64, 8, 1]}
REFUSED = {'scalar_nonlinear', 'scalar_mutated'}
SUPPORTED = set(METADATA)-REFUSED
IDENTIFIERS = ['i', 'j', 'k', 't']
BOUNDS = ['n', 'm', 'p', 'q']


def execute(name, offset, start, counts, parameters, order=None):
    depth = METADATA[name]
    alpha, beta, gamma = parameters
    values = [2147483647-x if name == 'scalar_wrap' else 3*x+1 for x in range(SIZE)]
    counters = [start]+[77, 55, 33][:depth-1]
    for _ in range(2 if name == 'scalar_context' else 1):
        if name == 'scalar_context':
            counters[0] = start
        points = []

        def visit(axis):
            while counters[axis] < counts[axis]:
                if axis+1 < depth:
                    counters[axis+1] = 0
                    visit(axis+1)
                else:
                    points.extend((tuple(counters), site) for site in range(3 if name == 'scalar_chain' else 1))
                counters[axis] += 1

        visit(0)
        if order is not None:
            points.sort(key=order)
        if name == 'scalar_undef':
            assert not points, 'the uninitialized scalar must remain unused'
        for coordinates, site in points:
            assert offset >= 0, 'zero-trip execution must not dereference NULL'
            index = offset+sum(x*s for x, s in zip(coordinates, STRIDES[depth]))
            assert 0 <= index < SIZE-1
            i, j = coordinates[:2]
            term = (i*j+7 if depth == 2 else i*coordinates[2]+j+9 if depth == 3
                else i*j+coordinates[2]*coordinates[3]+11)
            if name == 'scalar_chain':
                if site == 0:
                    values[index] = word(values[index]*alpha+beta+term)
                elif site == 1:
                    values[index] = word(values[index]+values[index+1]*alpha)
                else:
                    values[index+1] = word(values[index]-beta)
            elif name == 'scalar_recurrence':
                values[index] = word(values[index]+values[index+1]*alpha+beta)
            elif name == 'scalar_bound':
                values[index] = word(values[index]*counts[0]+counts[1]+term)
            elif name == 'scalar_many':
                values[index] = word(values[index]*alpha+beta*gamma+term)
            elif name == 'scalar_nonlinear':
                values[index] = word(values[offset+i*j]*alpha+beta+term)
            elif name == 'scalar_mutated':
                alpha = word(alpha+1)
                values[index] = word(values[index]*alpha+beta+term)
            elif name == 'scalar_multi':
                values[index] = word(values[index]+values[index+1]*alpha+beta+term)
            else:
                values[index] = word(values[index]*alpha+beta+term)
    return values, counters


def model(name, offset, start, counts, parameters, order=None):
    values, counters = execute(name, offset, start, counts, parameters, order)
    return name+' '+' '.join(map(str, [offset]+counters+list(counts)+list(parameters)+values))+'\n'


def fixture_calls():
    main = SOURCE.read_text().split('int main(void)', 1)[1]
    return [(name, *map(int, args.split(','))) for name, args in
        re.findall(r'run_(scalar_\w+)\(([-\d,]+)\);', main)]


def expected_output():
    return ''.join(model(name, args[0], args[1], args[2:2+METADATA[name]], args[-3:])
        for name, *args in fixture_calls())+'scalar_tiny 1 1 2147483535\n'


def templates():
    result = {f'identity-{d}': loop_template(d) for d in [2, 3, 4]}
    result |= {f'interchange-{d}': loop_template(d, [1, 0]+list(range(2, d))) for d in [2, 3, 4]}
    result |= {'reverse-last-2': loop_template(2, reverse=True),
        'schedule-identity-2': '(schedule ((coordinate 0) (coordinate 1) ordinal) ())',
        'schedule-interchange-2': '(schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0)))',
        'schedule-fission-2': '(schedule (ordinal (coordinate 0) (coordinate 1)) ())',
        'tile-2-3': '(tile 2 3)', 'tile-4-4': '(tile 4 4)', 'tile-17-13': '(tile 17 13)'}
    # This has the right scalar arity for the two-scalar AX+Y source, but replaces
    # its alpha by zero. The independent validator must refuse the changed payload.
    result['wrong-scalar-argument'] = ('(loop (constant 0) (var 0) '
        '(loop (constant 0) (var 2) '
        '(each (instr current ((var 1) (var 0) (constant 0) (var 5))))))')
    return result


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
    subprocess.run(['gcc', '-O0', '-fwrapv', str(SOURCE), '-o', str(WORK/'gcc-reference')], capture_output=True, check=True)
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
            '-stdlib', str(COMPILER.parent/'runtime'), '-dclight', '-S', '-o', str(work/'scalar.s'), str(SOURCE)],
            cwd=work, env=os.environ | {'GUARDCERT_LOOP_CANDIDATE': str(path)} | extra,
            capture_output=True, text=True, check=True, timeout=600)
        (work/'compiler-output.txt').write_text(result.stdout+result.stderr)
        subprocess.run(['gcc', str(work/'scalar.s'), '-o', str(work/'scalar')], capture_output=True, check=True)
        output = subprocess.check_output([str(work/'scalar')], text=True)
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
            values = [re.search(r'\$'+bound+r'\s*<=\s*(\d+)', fast) for bound in BOUNDS[:METADATA[fn]]]
            assert all(values), (name, fn, 'complete count guard')
            limits[fn] = min(int(value.group(1)) for value in values)
            # Only counter/count temporaries appear in the entry guard. Parameters
            # may be used later by the candidate, after all count tests have passed.
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
        'scope': 'stable RHS scalar parameters through actual pointer source, independent candidate checking, schedules, tiles and complete Csem-to-Asm compilation'}
    (WORK/('smoke-report.json' if arguments.cases else 'report.json')).write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
