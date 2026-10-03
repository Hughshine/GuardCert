"""Check source parameter layouts and eager reads in complete C programs."""
import hashlib
import json
import subprocess
import native_memory_parametric as core

ROOT = core.ROOT
WORK = ROOT/'build/native-memory-parametric-context'
FUNCTIONS = {'affine_only_bound', 'affine_four_parameters', 'affine_eager_zero_parameter', 'affine_repeated_parameters'}


def model(tag, n, m=0, p=0, q=0):
    a, i, j, k = [-999]*200, 0, 99, 55
    while i < n:
        k = n-i if tag == 'only' else 2*i+m-p+(q if tag != 'zero' else 0)-(m if tag == 'repeated' else 0)
        j = 0
        while j < k:
            assert 0 <= i*20+j < 200
            a[i*20+j] = i*37+j+7
            j += 1
        i += 1
    return f'{tag} {i} {j} {k} {m} {p} {q} '+' '.join(map(str, a))+'\n'


def expected_output():
    output = ''
    for n in range(6):
        output += model('only', n)
        output += ''.join(model(tag, n, m, p, q) for m in range(-1, 6) for p in range(-2, 3)
                          for q in range(-1, 3) for tag in ['four', 'zero', 'repeated'])
    return output+model('only', -2)+model('four', 0, 2147483647, -2147483648, 2147483647)+\
        model('zero', 0, -2147483648, 2147483647, -2147483648)+\
        model('repeated', 0, 2147483647, -2147483648, 2147483647)+model('zero', 4, 5, 1, 2147483647)


def main():
    core.SOURCE = ROOT/'examples/native_memory_parametric_context.c'
    core.WORK = WORK
    WORK.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((core.COMPILER.parent/'.guard-build.json').read_text())
    assert stamp['proved_entrypoint'] == core.ENTRY
    assert stamp['compiler_sha256'] == hashlib.sha256(core.COMPILER.read_bytes()).hexdigest()
    for path, expected in (stamp['proof_sources'] | stamp['native_sources']).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == expected, path
    subprocess.run(['gcc', '-O0', str(core.SOURCE), '-o', str(WORK/'gcc-reference')], check=True, capture_output=True)
    reference = subprocess.check_output([str(WORK/'gcc-reference')], text=True)
    assert reference == expected_output()
    templates = ROOT/'examples/parametric-candidates'
    cases = [('one-parameter-identity', templates/'one-parameter-identity.sexp', {}, FUNCTIONS),
             ('four-parameter-identity', templates/'four-parameter-identity.sexp', {}, FUNCTIONS-{'affine_only_bound'}),
             ('four-parameter-interchange', templates/'four-parameter-interchange.sexp', {}, FUNCTIONS-{'affine_only_bound'})]
    for rows, columns in [(1, 1), (2, 3), (17, 13)]:
        name = f'tile-{rows}-{columns}'
        path = WORK/(name+'.sexp')
        path.write_text(f'(tile {rows} {columns})\n')
        cases.append((name, path, {}, FUNCTIONS))
    cases += [(name, WORK/'tile-2-3.sexp', extra, set()) for name, extra in [
        ('resource-limit', {'GUARDCERT_FM_ROWS': '0'}),
        ('invalid-certificate', {'GUARDCERT_ORACLE_FAULT': 'top-certificate'})]]
    configurations = {}
    for name, path, extra, expected in cases:
        dump = core.compile_run(name, {'GUARDCERT_LOOP_CANDIDATE': str(path)} | extra, reference)
        observed = {function for function in FUNCTIONS if 'switch (0)' in core.function_body(dump, function)}
        assert observed == expected, (name, observed, expected)
        for function in observed:
            body = core.function_body(dump, function)
            assert '$i = $n;' in body and '$j = $k;' in body, (name, function)
        configurations[name] = {'guarded_functions': sorted(observed), 'full_output_lines': len(reference.splitlines()),
            'gcc_and_independent_model_match': True}
        print(name, sorted(observed), flush=True)
    (WORK/'report.json').write_text(json.dumps({'status': 'passed', 'proved_entrypoint': core.ENTRY,
        'compiler_sha256': stamp['compiler_sha256'], 'configurations': configurations,
        'one_and_four_parameter_source_contexts': True, 'repeated_and_zero_scaled_source_reads': True}, indent=2)+'\n')


if __name__ == '__main__':
    main()
