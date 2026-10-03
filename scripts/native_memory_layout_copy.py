"""Check heterogeneous array layouts in the complete guarded C compiler."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
from native_zero_trip import function_body

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'examples/native_memory_layout_copy.c'
COMPILER = ROOT / 'build/compcert-memory-unified/ccomp'
WORK = ROOT / 'build/native-memory-layout-copy'
ENTRY = 'GuardMemoryUnifiedCompiler.compile_memory_unified_regions'
LAYOUTS = {
    'layout_growing': (220, 22, 170, 17),
    'layout_descending': (170, 17, 220, 22),
    'layout_constant': (210, 21, 140, 14),
    'layout_global': (240, 24, 180, 18),
    'layout_context': (150, 15, 200, 20),
    'layout_same_extent': (240, 24, 240, 20),
    'layout_nonlinear': (220, 22, 170, 17),
    'layout_neighbor': (220, 22, 170, 17),
    'layout_alias': (240, 24, 240, 20),
    'layout_alias_descending': (240, 20, 240, 24),
}
REFUSED = {'layout_nonlinear', 'layout_neighbor'}
ALIASED = {'layout_alias', 'layout_alias_descending'}
ACCEPTED = set(LAYOUTS) - REFUSED
CONDITION_CAPS = {'interchange': 2, 'tile-2-3': 2, 'tile-4-4': 2, 'tile-17-13': 2}


def model(name, start, n, m, p):
    read_extent, read_stride, write_extent, write_stride = LAYOUTS[name]
    a = [2147483647 if x % 3 == 0 else -2147483648 if x % 3 == 1 else x*3+1
         for x in range(read_extent)]
    b = [x*5+2 for x in range(write_extent)] if name in ALIASED else [-777] * write_extent
    i, j, k = start, 99, 55
    for _ in range(2 if name == 'layout_context' else 1):
        if name == 'layout_context':
            i = start
        while i < n:
            k = m-2*i+p if name in {'layout_descending', 'layout_alias_descending'} else m+p if name == 'layout_constant' else i*i+m-p if name == 'layout_nonlinear' else 2*i+m-p
            j = 0
            while j < k:
                wi = i*write_stride+j
                ri = i*read_stride+j+(name == 'layout_neighbor')
                assert 0 <= wi < write_extent and 0 <= ri < read_extent
                b[wi] = b[ri] if name in ALIASED else a[ri]
                j += 1
            i += 1
    return ''.join(f'{name}-{suffix} {i} {j} {k} {m} {p} ' + ' '.join(map(str, values)) + '\n'
                   for suffix, values in [('a', a), ('b', b)])


def expected_output():
    output = ''.join(model(name, 0, n, m, p) for n in range(6)
                     for m in range(-1, 7) for p in range(-2, 3) for name in LAYOUTS)
    for name in LAYOUTS:
        output += model(name, 2, 4, 5, 1)
        output += model(name, 0, -2, 2147483647, -2147483648)
        output += model(name, 0, 0, -2147483648, 2147483647)
    output += model('layout_alias', 0, 5, 9, 0) + model('layout_alias_descending', 0, 5, 19, 0)
    return output + model('layout_growing', 0, 4, 100, 99) + model('layout_context', 0, 4, 100, 99)


def dependence_counterexamples():
    witnesses = {}
    for name, n, m in [('layout_alias', 5, 9), ('layout_alias_descending', 5, 19)]:
        _, read_stride, _, write_stride = LAYOUTS[name]
        points = [(i, j) for i in range(n) for j in range(
            m-2*i if name.endswith('descending') else 2*i+m)]
        def execute(order):
            values = [x*5+2 for x in range(240)]
            for i, j in order:
                values[write_stride*i+j] = values[read_stride*i+j]
            return values
        source = execute(points)
        orders = {'interchange': sorted(points, key=lambda point: (point[1], point[0]))}
        for rows, columns in [(2, 3), (4, 4), (17, 13)]:
            orders[f'tile-{rows}-{columns}'] = sorted(points, key=lambda point:
                (point[0]//rows, point[1]//columns, point[0], point[1]))
        for candidate, order in orders.items():
            different = [index for index, (before, after) in enumerate(zip(source, execute(order)))
                         if before != after]
            assert different, (name, candidate, 'expected actual dependency violation')
            witnesses[name+'/'+candidate] = {'n': n, 'm': m, 'p': 0, 'different_cells': different}
    return witnesses


def compile_run(name, environment, reference):
    work = WORK/name
    work.mkdir(parents=True, exist_ok=True)
    result = subprocess.run([str(COMPILER), '-conf', str(COMPILER.parent/'compcert.ini'),
        '-stdlib', str(COMPILER.parent/'runtime'), '-dclight', '-S', '-o', str(work/'layouts.s'), str(SOURCE)],
        cwd=work, env=os.environ | environment, text=True, capture_output=True, check=True, timeout=240)
    (work/'compiler-output.txt').write_text(result.stdout+result.stderr)
    subprocess.run(['gcc', str(work/'layouts.s'), '-o', str(work/'layouts')], check=True, capture_output=True)
    output = subprocess.check_output([str(work/'layouts')], text=True)
    assert output == reference, name
    (work/'output.txt').write_text(output)
    dumps = list(work.glob('*.light.c'))
    assert len(dumps) == 1
    return dumps[0].read_text()


def diagnose_fast_paths(name, dump):
    """Diagnostic only: repair printer conventions and count successful branches.

    The actual CompCert assembly is checked separately against GCC and the model.
    This GCC build of an instrumented pretty-print is not a proof endpoint.
    """
    cap = CONDITION_CAPS[name]
    instrumented = dump
    for index, function in enumerate(sorted(ALIASED)):
        body = function_body(dump, function)
        assert re.search(rf'if \(\$n <= {cap}\)', body), (name, function, cap, 'synthesized count interval')
        assert 'continue;' in body
        marked = body.replace('continue;', f'guard_branch_hits[{index}]++; continue;', 1)
        assert instrumented.count(body) == 1
        instrumented = instrumented.replace(body, marked, 1)
    def repair_parameters(match):
        prefix, parameters = match.group(1).split('(', 1)
        parameters = parameters[:-1]
        names = []
        for parameter in parameters.split(','):
            found = re.search(r'([a-zA-Z_][a-zA-Z_0-9]*)\s*$', parameter)
            if found and found.group(1) != 'void':
                names.append(found.group(1))
        for identifier in names:
            parameters = re.sub(r'\b'+re.escape(identifier)+r'\b', '$'+identifier, parameters)
        return prefix+'('+parameters+')\n{'
    instrumented = re.sub(r'^([^;\n]+\([^;\n]*\))\n\{', repair_parameters, instrumented, flags=re.M)
    instrumented = instrumented.replace('for (; 1; ({ break; }))',
        'for (int guard_once=0; guard_once<1; ++guard_once)')
    instrumented, renamed = re.subn(r'int main\(void\)(\s*\{)', r'int guard_original_main(void)\1', instrumented)
    assert renamed == 1
    calls, reference = [], ''
    for index, function in enumerate(sorted(ALIASED)):
        m = 19 if function.endswith('descending') else 9
        for start, n, expected_hit in [(0, cap, 1), (0, 5, 0), (0, 0, 0), (2, 4, 0)]:
            calls.append(f'guard_branch_hits[{index}]=0; {function}({start},{n},{m},0); '
                         f'if (guard_branch_hits[{index}]!={expected_hit}) return {20+len(calls)};')
            reference += model(function, start, n, m, 0)
    instrumented = 'int guard_branch_hits[2];\n'+instrumented+'\nint main(void) {\n'+'\n'.join(calls)+'\nreturn 0; }\n'
    work = WORK/name
    source = work/'branch-diagnostic.c'; source.write_text(instrumented)
    subprocess.run(['gcc', '-Wno-builtin-declaration-mismatch', '-Wno-discarded-qualifiers', str(source),
                    '-o', str(work/'branch-diagnostic')], check=True, capture_output=True)
    output = subprocess.check_output([str(work/'branch-diagnostic')], text=True)
    assert output == reference, (name, 'instrumented pretty-print diagnostic')
    (work/'branch-diagnostic-output.txt').write_text(output)
    return {'outer_count_upper': cap, 'successful_branch_hits_checked': True,
            'unsafe_count_zero_trip_and_nonzero_start_fallback_checked': True,
            'scope': 'GCC execution of instrumented Clight pretty-print; actual CompCert assembly checked separately'}


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
    cases = [(name, templates/(name+'.sexp'), {}, ACCEPTED)
             for name in ['identity', 'interchange', 'fission', 'shift', 'skew']]
    cases += [(name, templates/(name+'.sexp'), {}, set())
              for name in ['wrong-map', 'wrong-dimension', 'overflow-coefficient']]
    for rows, columns in [(1, 1), (1, 3), (2, 3), (4, 4), (17, 13)]:
        name = f'tile-{rows}-{columns}'
        path = WORK/(name+'.sexp'); path.write_text(f'(tile {rows} {columns})\n')
        cases.append((name, path, {}, ACCEPTED))
    cases += [(name, templates/'identity.sexp', extra, set()) for name, extra in [
        ('resource-limit', {'GUARDCERT_FM_ROWS': '0'}),
        ('invalid-certificate', {'GUARDCERT_ORACLE_FAULT': 'top-certificate'})]]
    witnesses = dependence_counterexamples()
    configurations = {}
    for name, path, extra, expected in cases:
        dump = compile_run(name, {'GUARDCERT_LOOP_CANDIDATE': str(path)} | extra, reference)
        observed = {function for function in ACCEPTED if 'switch (0)' in function_body(dump, function)}
        assert observed == expected, (name, observed, expected)
        for function in observed:
            body = function_body(dump, function)
            assert '$i = $n;' in body and '$j = $k;' in body, (name, function, 'public exit')
            if function not in ALIASED:
                assert re.search(r'if \([^\n]* != [^\n]*\)', body), (name, function, 'safe comparison')
            start = body.index('switch (0)')
            fast = body[start:body.index('continue;', start)]
            _, read_stride, _, write_stride = LAYOUTS[function]
            for stride in [read_stride, write_stride]:
                assert re.search(rf'\*\s*{stride}\b', fast), (name, function, stride, 'candidate physical layout')
        branch_diagnostic = diagnose_fast_paths(name, dump) if name in CONDITION_CAPS else None
        for function in REFUSED:
            assert 'switch (0)' not in function_body(dump, function), (name, function)
        configurations[name] = {'guarded_functions': sorted(observed), 'full_output_lines': len(reference.splitlines()),
            'gcc_and_independent_model_match': True, 'conditioned_branch_diagnostic': branch_diagnostic, 'template_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
        print(name, sorted(observed), flush=True)
    (WORK/'report.json').write_text(json.dumps({'status': 'passed', 'proved_entrypoint': ENTRY,
        'compiler_sha256': stamp['compiler_sha256'], 'source_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'configurations': configurations, 'separate_read_and_write_array_layouts': True,
        'both_physical_strides_checked_in_generated_fast_path': True,
        'same_array_remapping_uses_one_registry_entry': True,
        'actual_cross_iteration_dependencies_checked': True,
        'candidate_execution_counterexamples_outside_synthesized_condition': witnesses,
        'parameterized_affine_bound_and_exact_public_exits': True,
        'arbitrary_source_accesses_supported': False}, indent=2)+'\n')


if __name__ == '__main__':
    main()
