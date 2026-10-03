"""Check actual pointer fast branches, conditional acceptance and fallback."""
import json
import subprocess
from native_zero_trip import function_body
from native_memory_layout_sequence_paths import printer_for_gcc
from native_memory_pointer import WORK, METADATA, model, execute


def dependence_witnesses():
    source, _ = execute('pointer_chain', 9, 0, [1, 3])
    reverse, _ = execute('pointer_chain', 9, 0, [1, 3], lambda p: (p[0][0], -p[0][1], p[1]))
    fission, _ = execute('pointer_chain', 9, 0, [1, 3], lambda p: (p[1], *p[0]))
    assert source[9] != reverse[9] and source[9] != fission[9]
    return {'input': [9, 0, 1, 3], 'source_first_cell': source[9],
        'unprotected_reverse_first_cell': reverse[9], 'unprotected_fission_first_cell': fission[9]}


def main():
    report = json.loads((WORK/'report.json').read_text())
    assert report['status'] == 'passed' and report['full_configuration_suite']
    witness = dependence_witnesses()
    diagnostics = {}
    for configuration in ['identity-2', 'interchange-2', 'interchange-3', 'interchange-4',
            'reverse-last-2', 'schedule-interchange-2', 'schedule-fission-2',
            'tile-2-3', 'tile-4-4', 'tile-17-13']:
        work = WORK/configuration
        dump = (work/'native_memory_pointer.light.c').read_text()
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
            repeats = 2 if function == 'pointer_context' else 1
            if function == 'pointer_undef':
                inputs = [(-1, 0, [0, -2147483648, 2147483647], 0),
                    (-1, 0, [2, 0, -2147483648], 0), (9, 1, [0, 2147483647, -2147483648], 0)]
            else:
                inputs = [(9, 0, [1]*depth, repeats), (0, 0, [1]*depth, repeats),
                    (9, 0, [2]*depth, repeats if cap >= 2 else 0),
                    (9, 1, [2]*depth, 0), (9, 0, [1]*(depth-1)+[cap+1], 0)]
                inputs.extend((-1, 0, [2]*axis+[0]+[-2147483648]*(depth-axis-1), 0)
                    for axis in range(depth))
                unequal = [[1, 2], [2, 1]] if depth == 2 else [[1, 2, 3], [3, 1, 2]] if depth == 3 else [[1, 2, 1, 2], [2, 1, 2, 1]]
                inputs.extend((9, 0, counts, repeats if max(counts) <= cap else 0) for counts in unequal)
            for offset, start, counts, hits in inputs:
                calls.append(f'guard_branch_hits[{index}]=0; run_{function}('
                    + ','.join(map(str, [offset, start]+counts))+'); '
                    + f'if (guard_branch_hits[{index}]!={hits}) return {20+len(calls)};')
                expected += model(function, offset, start, counts)
        tiny_checked = 'pointer_two' in functions
        if tiny_checked:
            index = functions.index('pointer_two')
            calls.append(f'guard_branch_hits[{index}]=0; run_pointer_tiny(); '
                f'if (guard_branch_hits[{index}]!=1) return 19;')
            expected += 'pointer_tiny 1 1 24\n'
        if configuration in {'reverse-last-2', 'schedule-fission-2'}:
            index = functions.index('pointer_chain')
            cap = report['configurations'][configuration]['common_guard_cap']['pointer_chain']
            assert cap == 1, (configuration, cap)
            calls.append(f'guard_branch_hits[{index}]=0; run_pointer_chain(9,0,1,3); '
                f'if (guard_branch_hits[{index}]!=0) return 18;')
            expected += model('pointer_chain', 9, 0, [1, 3])
        instrumented = f'int guard_branch_hits[{len(functions)}];\n'+instrumented
        instrumented += '\nint main(void) {\n'+'\n'.join(calls)+'\nreturn 0; }\n'
        source = work/'branch-diagnostic.c'
        source.write_text(instrumented)
        subprocess.run(['gcc', '-fwrapv', '-Wno-builtin-declaration-mismatch', '-Wno-discarded-qualifiers',
            str(source), '-o', str(work/'branch-diagnostic')], capture_output=True, check=True)
        output = subprocess.check_output([str(work/'branch-diagnostic')], text=True)
        assert output == expected, configuration
        (work/'branch-diagnostic-output.txt').write_text(output)
        diagnostics[configuration] = {'nonzero_base_actual_fast_paths_checked': bool(set(functions)-{'pointer_undef'}),
            'null_zero_trip_each_dimension_checked': bool(functions),
            'nonzero_start_and_above_cap_fallback_checked': bool(functions),
            'one_element_allocation_fast_path_checked': tiny_checked,
            'uninitialized_deep_bound_short_circuit_checked': 'pointer_undef' in functions,
            'complete_caller_buffers_and_public_counters_checked': True,
            'unequal_axis_counts_checked': True,
            'source_function_calls': len(calls)}
        print(configuration, 'pointer branch selection checked', flush=True)
    (WORK/'branch-report.json').write_text(json.dumps({'status': 'passed',
        'compiler_sha256': report['compiler_sha256'], 'configurations': diagnostics,
        'unprotected_dependency_witness': witness,
        'scope': 'GCC execution of instrumented Clight pretty-print; complete CompCert assembly outputs checked separately'},
        indent=2)+'\n')


if __name__ == '__main__':
    main()
