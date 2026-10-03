"""Observe scalar fixed-array guard selection in the generated Clight program."""
import json
import subprocess
from native_zero_trip import function_body
from native_memory_layout_sequence_paths import printer_for_gcc
from native_memory_scalar_array import WORK, METADATA, model, execute


def dependence_witnesses():
    parameters = [19, -7, 3]
    source = execute('array_scalar_chain', 0, [1, 3], parameters)[0]
    reverse = execute('array_scalar_chain', 0, [1, 3], parameters,
        lambda p: (p[0][0], -p[0][1], p[1]))[0]
    fission = execute('array_scalar_chain', 0, [1, 3], parameters,
        lambda p: (p[1], *p[0]))[0]
    assert source[1][0] != reverse[1][0] and source[1][0] != fission[1][0]
    return {'input': [0, 1, 3]+parameters, 'source_b0': source[1][0],
        'unprotected_reverse_b0': reverse[1][0], 'unprotected_fission_b0': fission[1][0]}


def main():
    report = json.loads((WORK/'report.json').read_text())
    assert report['status'] == 'passed' and report['full_configuration_suite']
    diagnostics = {}
    parameters = [[19, -7, 3], [-2147483648, 2147483647, -1],
        [2147483647, -2147483648, 2147483647], [0, 0, 0]]
    for configuration in ['identity-2', 'interchange-2', 'interchange-3', 'interchange-4',
            'reverse-last-2', 'schedule-interchange-2', 'schedule-fission-2',
            'tile-2-3', 'tile-4-4', 'tile-17-13']:
        work = WORK/configuration
        dump = (work/'native_memory_scalar_array.light.c').read_text()
        functions = sorted(report['configurations'][configuration]['guarded_functions'])
        instrumented = dump
        for index, function in enumerate(functions):
            body = function_body(dump, function)
            guard = body.index('switch (0)')
            end = body.index('continue;', guard)
            marked = body[:end]+f'guard_branch_hits[{index}]++; '+body[end:]
            instrumented = instrumented.replace(body, marked, 1)
        instrumented = printer_for_gcc(instrumented)
        calls, expected = [], ''
        for index, function in enumerate(functions):
            depth = METADATA[function]
            cap = report['configurations'][configuration]['common_guard_cap'][function]
            repeats = 2 if function.endswith('_context') else 1
            if function.endswith('_undef'):
                inputs = [(0, [0, -2147483648], 0), (0, [2, 0], 0),
                    (1, [0, 2147483647], 0)]
            else:
                inputs = [(0, [1]*depth, repeats),
                    (0, [2]*depth, repeats if cap >= 2 else 0),
                    (1, [2]*depth, 0), (0, [1]*(depth-1)+[cap+1], 0)]
                inputs += [(0, [2]*axis+[0]+[-2147483648]*(depth-axis-1), 0)
                    for axis in range(depth)]
                unequal = [[1, 2], [2, 1]] if depth == 2 else [[1, 2, 3], [3, 1, 2]] if depth == 3 else [[1, 2, 1, 2], [2, 1, 2, 1]]
                inputs += [(0, counts, repeats if max(counts) <= cap else 0) for counts in unequal]
            for start, counts, hits in inputs:
                for values in parameters:
                    calls.append(f'guard_branch_hits[{index}]=0; {function}('
                        + ','.join(map(str, [start]+counts+values))+'); '
                        + f'if (guard_branch_hits[{index}]!={hits}) return 31;')
                    expected += model(function, start, counts, values)
        if configuration in {'reverse-last-2', 'schedule-fission-2'}:
            index = functions.index('array_scalar_chain')
            assert report['configurations'][configuration]['common_guard_cap']['array_scalar_chain'] == 1
            calls.append(f'guard_branch_hits[{index}]=0; array_scalar_chain(0,1,3,19,-7,3); '
                f'if (guard_branch_hits[{index}]!=0) return 18;')
            expected += model('array_scalar_chain', 0, [1, 3], [19, -7, 3])
        instrumented = f'int guard_branch_hits[{len(functions)}];\n'+instrumented
        instrumented += '\nint main(void) {\n'+'\n'.join(calls)+'\nreturn 0; }\n'
        source = work/'branch-diagnostic.c'
        source.write_text(instrumented)
        subprocess.run(['gcc', '-fwrapv', '-Wno-builtin-declaration-mismatch',
            '-Wno-discarded-qualifiers', str(source), '-o', str(work/'branch-diagnostic')],
            capture_output=True, check=True)
        output = subprocess.check_output([str(work/'branch-diagnostic')], text=True)
        assert output == expected, configuration
        (work/'branch-diagnostic-output.txt').write_text(output)
        diagnostics[configuration] = {'negative_and_extreme_scalar_fast_branches_checked': True,
            'zero_trip_each_dimension_checked': True,
            'uninitialized_scalar_on_zero_trip_checked': 'array_scalar_undef' in functions,
            'nonzero_start_and_above_cap_fallback_checked': True,
            'local_and_global_fixed_arrays_checked': 'array_scalar_global' in functions,
            'complete_caller_arrays_and_public_counters_checked': True,
            'unequal_axis_counts_checked': True,
            'source_function_calls': len(calls)}
        print(configuration, 'scalar fixed-array branch selection checked', len(calls), flush=True)
    (WORK/'branch-report.json').write_text(json.dumps({'status': 'passed',
        'compiler_sha256': report['compiler_sha256'], 'configurations': diagnostics,
        'unprotected_dependency_witness': dependence_witnesses(),
        'scope': 'GCC execution of instrumented Clight pretty-print; complete CompCert assembly outputs checked separately'},
        indent=2)+'\n')


if __name__ == '__main__':
    main()
