"""Run pointer-parameter C programs through the proved guarded compiler."""
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

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'examples/native_memory_pointer.c'
COMPILER = ROOT / 'build/compcert-memory-unified/ccomp'
WORK = ROOT / 'build/native-memory-pointer'
ENTRY = 'GuardMemoryUnifiedCompiler.compile_memory_unified_regions'
SIZE = 1568
METADATA = {name: 2 for name in ['pointer_two', 'pointer_context', 'pointer_wrap',
    'pointer_chain', 'pointer_recurrence', 'pointer_nonlinear', 'pointer_scalar', 'pointer_multi']}
METADATA |= {'pointer_three': 3, 'pointer_four': 4, 'pointer_undef': 3}
STRIDES = {2: [8, 1], 3: [128, 16, 1], 4: [512, 64, 8, 1]}
REFUSED = {'pointer_nonlinear'}
SUPPORTED = set(METADATA) - REFUSED
IDENTIFIERS = ['i', 'j', 'k', 't']
BOUNDS = ['n', 'm', 'p', 'q']


def word(value):
    return (value + 2**31) % 2**32 - 2**31


def execute(name, offset, start, counts, order=None):
    depth = METADATA[name]
    values = [2147483647-x if name == 'pointer_wrap' else 3*x+1 for x in range(SIZE)]
    counters = [start] + [77, 55, 33][:depth-1]
    for _ in range(2 if name == 'pointer_context' else 1):
        if name == 'pointer_context':
            counters[0] = start
        points = []

        def visit(axis):
            while counters[axis] < counts[axis]:
                if axis+1 < depth:
                    counters[axis+1] = 0
                    visit(axis+1)
                else:
                    points.extend((tuple(counters), site)
                        for site in range(3 if name == 'pointer_chain' else 1))
                counters[axis] += 1

        visit(0)
        if order is not None:
            points.sort(key=order)
        for coordinates, site in points:
            assert offset >= 0, 'a zero-trip path must not dereference NULL'
            index = offset + sum(x*s for x, s in zip(coordinates, STRIDES[depth]))
            assert 0 <= index < SIZE-1
            i, j = coordinates[:2]
            scalar = (i*j+7 if depth == 2 else i*coordinates[2]+j+9 if depth == 3
                else i*j+coordinates[2]*coordinates[3]+11)
            if name == 'pointer_chain':
                if site == 0:
                    values[index] = word(values[index]+scalar)
                elif site == 1:
                    values[index] = word(values[index]+values[index+1])
                else:
                    values[index+1] = values[index]
            elif name == 'pointer_recurrence':
                values[index] = word(values[index]+values[index+1])
            elif name == 'pointer_nonlinear':
                values[index] = word(values[offset+i*j]+scalar)
            elif name == 'pointer_scalar':
                values[index] = word(values[index]*19+scalar)
            elif name == 'pointer_multi':
                values[index] = word(values[index]+values[index+1]+scalar)
            else:
                values[index] = word(values[index]+scalar)
    return values, counters


def model(name, offset, start, counts, order=None):
    counts = list(counts)
    if name == 'pointer_undef':
        assert counts[0] <= start or counts[1] <= 0
        values, counters = execute(name, offset, start, counts[:2]+[0], order)
        counts[2] = 9
    else:
        values, counters = execute(name, offset, start, counts, order)
    return name+' '+ ' '.join(map(str, [offset]+counters+counts+values))+'\n'


def fixture_calls():
    main = SOURCE.read_text().split('int main(void)', 1)[1]
    return [(name, *map(int, args.split(','))) for name, args in
        re.findall(r'run_(pointer_\w+)\(([-\d,]+)\);', main)]


def expected_output():
    return ''.join(model(name, offset, start, counts)
        for name, offset, start, *counts in fixture_calls())+'pointer_tiny 1 1 24\n'


def templates():
    result = {f'identity-{depth}': loop_template(depth) for depth in [2, 3, 4]}
    result |= {f'interchange-{depth}': loop_template(depth, [1, 0]+list(range(2, depth)))
        for depth in [2, 3, 4]}
    result |= {'reverse-last-2': loop_template(2, reverse=True),
        'schedule-identity-2': '(schedule ((coordinate 0) (coordinate 1) ordinal) ())',
        'schedule-interchange-2': '(schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0)))',
        'schedule-fission-2': '(schedule (ordinal (coordinate 0) (coordinate 1)) ())',
        'tile-2-3': '(tile 2 3)', 'tile-4-4': '(tile 4 4)', 'tile-17-13': '(tile 17 13)'}
    return result


def expected_acceptance(configuration, observed):
    assert not observed & REFUSED, (configuration, observed & REFUSED)
    if configuration.startswith(('identity-', 'interchange-')):
        rank = int(configuration.rsplit('-', 1)[1])
        assert observed == {name for name in SUPPORTED if METADATA[name] == rank}, (configuration, observed)
    elif configuration == 'reverse-last-2':
        assert observed == {name for name in SUPPORTED if METADATA[name] == 2}, (configuration, observed)
    elif configuration.startswith('schedule-'):
        assert {name for name in SUPPORTED if METADATA[name] == 2} <= observed <= SUPPORTED, (configuration, observed)
    elif configuration.startswith('tile-'):
        assert observed == SUPPORTED, (configuration, observed)
    else:
        assert not observed, (configuration, observed)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cases', help='comma-separated configurations for a smoke check')
    arguments = parser.parse_args()
    stamp = json.loads((COMPILER.parent/'.guard-build.json').read_text())
    assert stamp['proved_entrypoint'] == ENTRY
    assert stamp['compiler_sha256'] == hashlib.sha256(COMPILER.read_bytes()).hexdigest()
    for path, expected in (stamp['proof_sources'] | stamp['native_sources']).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == expected, path
    WORK.mkdir(parents=True, exist_ok=True)
    subprocess.run(['gcc', '-O0', '-fwrapv', str(SOURCE), '-o', str(WORK/'gcc-reference')],
        capture_output=True, check=True)
    reference = subprocess.check_output([str(WORK/'gcc-reference')], text=True)
    assert reference == expected_output()
    (WORK/'gcc-output.txt').write_text(reference)
    cases = []
    for name, syntax in templates().items():
        path = WORK/(name+'.sexp')
        path.write_text(syntax+'\n')
        cases.append((name, path, {}))
    cases.extend((name, WORK/'interchange-2.sexp', extra) for name, extra in [
        ('resource-limit', {'GUARDCERT_FM_ROWS': '0'}),
        ('invalid-certificate', {'GUARDCERT_ORACLE_FAULT': 'top-certificate'})])
    selected = set(arguments.cases.split(',')) if arguments.cases else {name for name, _, _ in cases}
    assert selected <= {name for name, _, _ in cases}
    configurations = {}
    for name, path, extra in cases:
        if name not in selected:
            continue
        work = WORK/name
        work.mkdir(parents=True, exist_ok=True)
        result = subprocess.run([str(COMPILER), '-conf', str(COMPILER.parent/'compcert.ini'),
            '-stdlib', str(COMPILER.parent/'runtime'), '-dclight', '-S', '-o', str(work/'pointer.s'), str(SOURCE)],
            cwd=work, env=os.environ | {'GUARDCERT_LOOP_CANDIDATE': str(path)} | extra,
            capture_output=True, text=True, check=True, timeout=600)
        (work/'compiler-output.txt').write_text(result.stdout+result.stderr)
        subprocess.run(['gcc', str(work/'pointer.s'), '-o', str(work/'pointer')], capture_output=True, check=True)
        output = subprocess.check_output([str(work/'pointer')], text=True)
        assert output == reference, name
        (work/'output.txt').write_text(output)
        dump = (work/(SOURCE.stem+'.light.c')).read_text()
        observed = {fn for fn in METADATA if 'switch (0)' in function_body(dump, fn)}
        expected_acceptance(name, observed)
        limits = {}
        for fn in observed:
            body = function_body(dump, fn)
            start = body.index('switch (0)')
            fast = body[start:body.index('continue;', start)]
            dimensions = METADATA[fn]
            for identifier, bound in zip(IDENTIFIERS[:dimensions], BOUNDS):
                actualbound = 'unused_bound' if fn == 'pointer_undef' and identifier == 'k' else bound
                assert f'${identifier} = ${actualbound};' in fast, (name, fn, 'public counter exit', identifier)
            values = [re.search(r'\$'+('unused_bound' if fn == 'pointer_undef' and bound == 'p' else bound)
                       +r'\s*<=\s*(\d+)', fast) for bound in BOUNDS[:dimensions]]
            assert all(values), (name, fn, 'complete entry guard')
            limits[fn] = min(int(value.group(1)) for value in values)
        configurations[name] = {'guarded_functions': sorted(observed), 'common_guard_cap': limits,
            'full_output_lines': len(reference.splitlines()), 'gcc_and_independent_model_match': True,
            'template_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
        (WORK/'partial-report.json').write_text(json.dumps(configurations, indent=2)+'\n')
        print(name, sorted(observed), limits, flush=True)
    report = {'status': 'passed', 'proved_entrypoint': ENTRY, 'compiler_sha256': stamp['compiler_sha256'],
        'source_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(), 'configurations': configurations,
        'full_configuration_suite': not bool(arguments.cases), 'machine_signed_wrap_model': True,
        'scope': 'actual pointer parameters with arbitrary nonzero base, one-element allocation, complete caller buffers and public counters; no allocation-extent premise'}
    (WORK/('smoke-report.json' if arguments.cases else 'report.json')).write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
