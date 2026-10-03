"""Exercise affine C bounds through the proved complete-program compiler."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
from native_zero_trip import function_body

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'examples/native_memory_parametric.c'
COMPILER = ROOT / 'build/compcert-memory-unified/ccomp'
WORK = ROOT / 'build/native-memory-parametric'
ENTRY = 'GuardMemoryUnifiedCompiler.compile_memory_unified_regions'
KINDS = {
    'affine_growing': 'write', 'affine_scaled_right': 'write',
    'affine_descending': 'write', 'affine_bound_parameter': 'write',
    'affine_constant': 'write', 'affine_copy': 'copy', 'affine_chain': 'chain',
    'affine_prefix': 'prefix', 'affine_global': 'global', 'affine_context': 'context',
    'affine_nonlinear': 'write', 'affine_unsigned': 'write',
}
ACCEPTED = set(KINDS) - {'affine_nonlinear', 'affine_unsigned'}
REFUSED = {'affine_nonlinear', 'affine_unsigned', 'affine_counter_coupled'}


def upper(name, i, n, m, p):
    if name in {'affine_descending', 'affine_global'}:
        return m - 2*i + p
    if name == 'affine_bound_parameter':
        return 2*i + m - p + n
    if name == 'affine_constant':
        return m + p
    if name == 'affine_nonlinear':
        return i*i + m - p
    return 2*i + m - p


def model(name, start, n, m, p):
    kind = KINDS[name]
    a, b, c = [-999]*200, [-777]*200, [-555]*200
    if kind == 'copy':
        a = [2147483647 if x % 3 == 0 else -2147483648 if x % 3 == 1 else x*3+1 for x in range(200)]
    i, j, k = start, 99, 55
    for _ in range(2 if kind == 'context' else 1):
        if kind == 'context':
            i = start
        while i < n:
            k, j = upper(name, i, n, m, p), 0
            while j < k:
                index = i*20+j
                assert 0 <= index < 200, (name, start, n, m, p, i, j)
                if kind == 'copy':
                    b[index] = a[index]
                else:
                    a[index] = i*37+j+7
                    if kind == 'chain':
                        b[index] = a[index]+i*11+j+19
                        c[index] = b[index]
                    elif kind == 'global':
                        b[index] = a[index]
                    elif kind == 'prefix':
                        a[index] = a[i*20]+i*17+j+11
                        b[index] = a[index]
                    elif kind == 'context':
                        b[index] += i*11+j+19
                        a[index] += i*23+j+3
                j += 1
            i += 1
    arrays = [('a', a)] + ([('b', b)] if kind in {'copy', 'chain', 'prefix', 'global', 'context'} else [])
    if kind == 'chain':
        arrays += [('c', c)]
    return ''.join(f'{name}-{suffix} {i} {j} {k} {m} {p} ' + ' '.join(map(str, values)) + '\n'
                   for suffix, values in arrays)


def expected_output():
    output = ''.join(model(name, 0, n, m, p) for n in range(6) for m in range(-1, 7)
                     for p in range(-2, 3) for name in KINDS)
    for name in KINDS:
        output += model(name, 2, 4, 5, 1)
        output += model(name, 0, -2, 2147483647, -2147483648)
        output += model(name, 0, 0, -2147483648, 2147483647)
    output += model('affine_growing', 0, 4, 100, 99) + model('affine_copy', 0, 4, 100, 99)
    a = [-999]*200
    for i in range(5):
        a[i*20] = i*37+7
    return output + 'affine_counter_coupled-a 5 1 1 0 0 ' + ' '.join(map(str, a)) + '\n'


def compile_run(name, environment, reference):
    work = WORK/name
    work.mkdir(parents=True, exist_ok=True)
    run = subprocess.run([str(COMPILER), '-conf', str(COMPILER.parent/'compcert.ini'),
        '-stdlib', str(COMPILER.parent/'runtime'), '-dclight', '-S', '-o', str(work/'parametric.s'), str(SOURCE)],
        cwd=work, env=os.environ | environment, text=True, capture_output=True, check=True, timeout=240)
    (work/'compiler-output.txt').write_text(run.stdout+run.stderr)
    subprocess.run(['gcc', str(work/'parametric.s'), '-o', str(work/'parametric')], check=True, capture_output=True)
    output = subprocess.check_output([str(work/'parametric')], text=True)
    assert output == reference, name
    (work/'output.txt').write_text(output)
    dumps = list(work.glob('*.light.c'))
    assert len(dumps) == 1, dumps
    return dumps[0].read_text()


def main():
    stamp = json.loads((COMPILER.parent/'.guard-build.json').read_text())
    assert stamp['proved_entrypoint'] == ENTRY
    assert stamp['compiler_sha256'] == hashlib.sha256(COMPILER.read_bytes()).hexdigest()
    for path, expected in (stamp['proof_sources'] | stamp['native_sources']).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == expected, path
    WORK.mkdir(parents=True, exist_ok=True)
    subprocess.run(['gcc', '-O0', str(SOURCE), '-o', str(WORK/'gcc-reference')], check=True, capture_output=True)
    reference = subprocess.check_output([str(WORK/'gcc-reference')], text=True)
    assert reference == expected_output()
    (WORK/'gcc-output.txt').write_text(reference)
    templates = ROOT/'examples/parametric-candidates'
    cases = [(name, templates/(name+'.sexp'), {}, ACCEPTED) for name in ['identity', 'interchange', 'fission', 'shift', 'skew']]
    cases += [(name, templates/(name+'.sexp'), {}, set()) for name in ['wrong-map', 'wrong-dimension', 'overflow-coefficient']]
    cases += [('missing-site', templates/'missing-site.sexp', {},
               {'affine_growing', 'affine_scaled_right', 'affine_descending', 'affine_bound_parameter', 'affine_constant', 'affine_copy'})]
    for rows, columns in [(1, 1), (2, 3), (4, 4), (17, 13)]:
        name = f'tile-{rows}-{columns}'
        path = WORK/(name+'.sexp')
        path.write_text(f'(tile {rows} {columns})\n')
        cases.append((name, path, {}, ACCEPTED))
    cases += [(name, templates/'identity.sexp', extra, set()) for name, extra in [
        ('resource-limit', {'GUARDCERT_FM_ROWS': '0'}),
        ('invalid-certificate', {'GUARDCERT_ORACLE_FAULT': 'top-certificate'})]]
    configurations = {}
    for name, path, extra, expected in cases:
        dump = compile_run(name, {'GUARDCERT_LOOP_CANDIDATE': str(path)} | extra, reference)
        observed = {function for function in ACCEPTED if 'switch (0)' in function_body(dump, function)}
        if expected is not None:
            assert observed == expected, (name, observed, expected)
        for function in observed:
            body = function_body(dump, function)
            assert '$i = $n;' in body and '$j = $k;' in body, (name, function, 'public exit')
            if KINDS[function] in {'copy', 'chain', 'prefix', 'global', 'context'}:
                assert re.search(r'if \([^\n]* != [^\n]*\)', body), (name, function, 'actual arrays compared safely')
        for function in REFUSED:
            assert 'switch (0)' not in function_body(dump, function), (name, function)
        configurations[name] = {'guarded_functions': sorted(observed), 'full_output_lines': len(reference.splitlines()),
            'gcc_and_independent_model_match': True, 'template_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
        print(name, sorted(observed), flush=True)
    (WORK/'report.json').write_text(json.dumps({'status': 'passed', 'proved_entrypoint': ENTRY,
        'compiler_sha256': stamp['compiler_sha256'], 'configurations': configurations,
        'signed_affine_upper_bounds_and_three_parameters': True,
        'exact_public_exits_and_complete_array_outputs': True,
        'unsupported_grammar_falls_back': sorted(REFUSED)}, indent=2)+'\n')


if __name__ == '__main__':
    main()
