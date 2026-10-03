"""Observe address separation guards independently of full assembly results."""
import json
import re
import subprocess
from native_zero_trip import function_body
from native_memory_layout_sequence_paths import printer_for_gcc
from native_memory_multi_pointer import WORK, NAMES, execute, model


def printer_for_multi_pointer_gcc(dump):
    # Preserve the indirect-call wrapper's nested declarator while repairing
    # parameter temporary names in this diagnostic copy of the Clight output.
    signature = re.search(r'^void run\([^\n]*\)\n\{', dump, re.M).group(0)
    placeholder = 'void guard_run_signature(void)\n{'
    dump = printer_for_gcc(dump.replace(signature, placeholder, 1))
    fixed = re.sub(r'\b(name|kernel|kind|p_offset|q_offset|start|n|m|alpha|beta)\b',
                   lambda match: '$'+match.group(1), signature)
    return dump.replace(placeholder, fixed, 1)


def alias_separated(name, args):
    if name == 'multi_tiny':
        return True
    kind, p_offset, q_offset, start, n, m, _, _ = args
    pointers = {'p': (0, p_offset), 'q': (0 if kind == 1 else 1, q_offset),
                'r': (1, q_offset) if kind == 2 else (2, 0)}
    cells = set()
    for i in range(start, n):
        for j in range(m):
            index = 8*i+j
            cells.add(('p', index))
            cells.add(('q', 63-index if name == 'multi_reflected' else index))
            if name == 'multi_combine':
                cells.add(('r', index))
            elif name == 'multi_chain':
                cells.add(('q', index+1))
    locations = [(pointers[pointer][0], pointers[pointer][1]+index) for pointer, index in cells]
    return len(set(locations)) == len(cells)


def expected_hits(name, args, cap):
    if name == 'multi_tiny':
        start, n, m, _, _ = args
    else:
        _, _, _, start, n, m, _, _ = args
    return ((2 if name == 'multi_context' else 1) if start == 0 and 0 < n <= cap
            and 0 < m <= cap and alias_separated(name, args) else 0)


def inputs(name, cap):
    if name == 'multi_tiny':
        return [[0, 1, 2, -7, 11], [0, 1, 1, -2147483648, 2147483647],
                [0, 0, 2, 3, -7], [0, 1, 0, 3, -7], [1, 1, 2, 3, -7]]
    if name == 'multi_undef':
        return [[3, 0, 0, 0, 0, -2147483648, 3, -7],
                [3, 0, 0, 0, 2, 0, -2147483648, 2147483647]]
    result = []
    for kind, p_offset, q_offset in [(0, 0, 0), (0, 3, 17), (1, 0, 0),
                                    (1, 0, 1), (1, 0, 4), (1, 3, 40), (2, 0, 0)]:
        for n, m in [(1, 1), (1, 2), (2, 1), (2, 3), (3, 2), (3, 3), (4, 4), (cap+1, 1)]:
            for alpha, beta in [(-7, 11), (-2147483648, 2147483647)]:
                result.append([kind, p_offset, q_offset, 0, n, m, alpha, beta])
    result += [[3, 0, 0, 0, 0, -2147483648, 3, -7],
               [3, 0, 0, 0, 2, 0, -2147483648, 2147483647],
               [0, 0, 0, 1, 3, 2, 3, -7]]
    if name == 'multi_chain':
        result.append([0, 0, 0, 0, 1, 3, 3, -7])
    elif name == 'multi_copy':
        result.append([1, 0, 1, 0, 1, 3, 3, -7])
    return result


def dependence_witnesses():
    chain_args = [0, 0, 0, 0, 1, 3, 3, -7]
    reverse_order = lambda point: (point[0][0], -point[0][1], point[1])
    fission_order = lambda point: (point[1], *point[0])
    chain_source = execute('multi_chain', chain_args)[0]
    chain_reverse = execute('multi_chain', chain_args, reverse_order)[0]
    chain_fission = execute('multi_chain', chain_args, fission_order)[0]
    assert chain_source != chain_reverse and chain_source != chain_fission
    overlap_args = [1, 0, 1, 0, 1, 3, 3, -7]
    overlap_source = execute('multi_copy', overlap_args)[0]
    overlap_reverse = execute('multi_copy', overlap_args, reverse_order)[0]
    assert overlap_source != overlap_reverse
    assert not alias_separated('multi_copy', overlap_args)
    return {'chain': {'input': chain_args, 'source_first_buffer': chain_source[0][:4],
                     'unprotected_reverse': chain_reverse[0][:4], 'unprotected_fission': chain_fission[0][:4]},
            'overlapping_copy': {'input': overlap_args, 'source_first_buffer': overlap_source[0][:4],
                                 'unprotected_reverse': overlap_reverse[0][:4]}}


def main():
    report = json.loads((WORK/'report.json').read_text())
    assert report['status'] == 'passed'
    witnesses = dependence_witnesses()
    diagnostics = {}
    for configuration in ['identity-2', 'interchange-2', 'reverse-last-2',
                          'schedule-identity-2', 'schedule-interchange-2', 'schedule-fission-2',
                          'tile-2-3', 'tile-4-4', 'tile-17-13']:
        work = WORK/configuration
        dump = (work/'native_memory_multi_pointer.light.c').read_text()
        instrumented = dump
        functions = sorted(report['configurations'][configuration]['guarded_functions'])
        for index, function in enumerate(functions):
            body = function_body(dump, function)
            marked = body
            cursor = 0
            while 'switch (0)' in marked[cursor:]:
                begin = marked.index('switch (0)', cursor)
                end = marked.index('continue;', begin)
                addition = f'guard_branch_hits[{index}]++; '
                marked = marked[:end]+addition+marked[end:]
                cursor = end+len(addition)+len('continue;')
            assert body != marked
            instrumented = instrumented.replace(body, marked, 1)
        instrumented = printer_for_multi_pointer_gcc(instrumented)
        calls, expected = [], ''
        fast, fallback = 0, 0
        for index, function in enumerate(functions):
            cap = report['configurations'][configuration]['common_guard_cap'][function]
            if function == 'multi_chain' and configuration in {'reverse-last-2', 'schedule-fission-2'}:
                assert cap == 1
            for args in inputs(function, cap):
                hits = expected_hits(function, args, cap)
                fast += bool(hits)
                fallback += not hits
                arguments = ','.join(map(str, args))
                invocation = ('run_tiny('+arguments+')' if function == 'multi_tiny' else
                              f'run("{function}",{function},'+arguments+')')
                calls.append(f'guard_branch_hits[{index}]=0; {invocation}; '
                             f'if (guard_branch_hits[{index}]!={hits}) return {20+len(calls)};')
                expected += model(function, args)
        assert fast and fallback
        instrumented = f'int guard_branch_hits[{len(functions)}];\n'+instrumented
        instrumented += '\nint main(void) {\n'+'\n'.join(calls)+'\nreturn 0; }\n'
        source = work/'branch-diagnostic.c'
        source.write_text(instrumented)
        result = subprocess.run(['gcc', '-fwrapv', '-Wno-builtin-declaration-mismatch', '-Wno-discarded-qualifiers',
                         str(source), '-o', str(work/'branch-diagnostic')], capture_output=True, text=True)
        (work/'branch-gcc-output.txt').write_text(result.stdout+result.stderr)
        result.check_returncode()
        output = subprocess.check_output([str(work/'branch-diagnostic')], text=True)
        assert output == expected, configuration
        (work/'branch-diagnostic-output.txt').write_text(output)
        diagnostics[configuration] = {'actual_fast_path_calls': fast, 'fallback_calls': fallback,
            'source_function_calls': len(calls), 'same_block_disjoint_and_overlapping_slices_checked': True,
            'interleaved_disjoint_accesses_checked': True, 'read_read_alias_fallback_checked': True,
            'two_element_allocations_checked': True, 'null_and_undefined_scalar_zero_trips_checked': True,
            'unequal_axes_and_extreme_scalar_values_checked': True,
            'dependence_witness_inputs_executed': True}
        print(configuration, 'branches:', fast, 'fast,', fallback, 'fallback', flush=True)
    (WORK/'branch-report.json').write_text(json.dumps({'status': 'passed',
        'compiler_sha256': report['compiler_sha256'], 'configurations': diagnostics,
        'unprotected_dependence_witnesses': witnesses,
        'scope': 'GCC execution of instrumented Clight pretty-print; full CompCert assembly outputs checked separately'}, indent=2)+'\n')


if __name__ == '__main__':
    main()
