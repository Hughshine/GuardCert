"""Check branch reachability separately from proved compiler assembly outputs."""
from pathlib import Path
import json
import re
import subprocess
from native_zero_trip import function_body
from native_memory_layout_sequence import WORK, ACCEPTED, SPECS, model


def printer_for_gcc(dump):
    def repair(match):
        prefix, parameters = match.group(1).split('(', 1)
        parameters = parameters[:-1]
        for parameter in parameters.split(','):
            identifier = re.search(r'([a-zA-Z_][a-zA-Z_0-9]*)\s*$', parameter)
            if identifier and identifier.group(1) != 'void':
                name = identifier.group(1)
                parameters = re.sub(r'\b'+re.escape(name)+r'\b', '$'+name, parameters)
        return prefix+'('+parameters+')\n{'
    dump = re.sub(r'^([^;\n]+\([^;\n]*\))\n\{', repair, dump, flags=re.M)
    dump = dump.replace('for (; 1; ({ break; }))',
        'for (int guard_once=0; guard_once<1; ++guard_once)')
    dump, count = re.subn(r'int main\(void\)(\s*\{)', r'int guard_original_main(void)\1', dump)
    assert count == 1
    return dump


def dependence_witnesses(configuration):
    witnesses = {}
    for function, n, m in [('mixed_alias_chain', 4, 9), ('mixed_alias_reverse', 6, 15)]:
        _, _, be, stride, ce, cs = SPECS[function][0]
        read_stride = 24 if function.endswith('chain') else 20
        points = [(i, j) for i in range(n) for j in range(
            2*i+m if function.endswith('chain') else m-2*i)]
        source_order = [(i, j, site) for i, j in points for site in range(3)]
        if configuration == 'fission':
            candidate_order = sorted(source_order, key=lambda x: (x[2], x[0], x[1]))
        elif configuration == 'interchange':
            candidate_order = sorted(source_order, key=lambda x: (x[1], x[0], x[2]))
        else:
            _, rows, columns = configuration.split('-')
            rows, columns = int(rows), int(columns)
            candidate_order = sorted(source_order, key=lambda x: (x[0]//rows, x[1]//columns, x[0], x[1], x[2]))
        def execute(order):
            b, c = [x*5+2 for x in range(be)], [-777]*ce
            for i, j, site in order:
                if site == 0: b[i*stride+j] = b[i*read_stride+j]
                elif site == 1: c[i*cs+j] = b[i*stride+j]
                else: b[i*stride+j] += i*11+j+19
            return b+c
        source, candidate = execute(source_order), execute(candidate_order)
        different = [i for i, (x, y) in enumerate(zip(source, candidate)) if x != y]
        if different:
            witnesses[function] = {'n': n, 'm': m, 'p': 0, 'different_combined_cells': different}
    return witnesses


def main():
    report = json.loads((WORK/'report.json').read_text())
    assert report['status'] == 'passed'
    diagnostics = {}
    for configuration in ['interchange', 'fission', 'tile-2-3', 'tile-4-4', 'tile-17-13']:
        work = WORK/configuration
        dumps = list(work.glob('*.light.c')); assert len(dumps) == 1
        dump = dumps[0].read_text()
        instrumented = dump
        functions = sorted(ACCEPTED)
        for index, function in enumerate(functions):
            body = function_body(dump, function)
            marked = body.replace('continue;', f'guard_branch_hits[{index}]++; continue;', 1)
            assert body != marked and instrumented.count(body) == 1
            instrumented = instrumented.replace(body, marked, 1)
        instrumented = printer_for_gcc(instrumented)
        calls, expected_output = [], ''
        for index, function in enumerate(functions):
            hits = 2 if SPECS[function][1] == 'context' else 1
            inputs = [(0, 1, 1, 0, hits), (0, 0, 2147483647, -2147483648, 0), (2, 4, 5, 1, 0)]
            if function in {'mixed_alias_chain', 'mixed_alias_reverse'}:
                cap = report['configurations'][configuration]['outer_count_guard_upper'][function]
                if cap < 5:
                    inputs.append((0, 6, 3 if function.endswith('chain') else 15, 0, 0))
            for start, n, m, p, expected_hit in inputs:
                calls.append(f'guard_branch_hits[{index}]=0; {function}({start},{n},{m},{p}); '
                    f'if (guard_branch_hits[{index}]!={expected_hit}) return {20+len(calls)};')
                expected_output += model(function, start, n, m, p)
        instrumented = f'int guard_branch_hits[{len(functions)}];\n'+instrumented
        instrumented += '\nint main(void) {\n'+'\n'.join(calls)+'\nreturn 0; }\n'
        source = work/'branch-diagnostic.c'; source.write_text(instrumented)
        subprocess.run(['gcc', '-Wno-builtin-declaration-mismatch', '-Wno-discarded-qualifiers', str(source),
            '-o', str(work/'branch-diagnostic')], check=True, capture_output=True)
        output = subprocess.check_output([str(work/'branch-diagnostic')], text=True)
        assert output == expected_output, configuration
        (work/'branch-diagnostic-output.txt').write_text(output)
        diagnostics[configuration] = {'actual_fast_branch_hits_checked_for_all_supported_functions': True,
            'zero_trip_nonzero_start_and_conditioned_count_fallback_checked': True,
            'source_execution_calls': len(calls), 'independent_dependency_counterexamples': dependence_witnesses(configuration)}
        print(configuration, 'branch selection checked', flush=True)
    (WORK/'branch-report.json').write_text(json.dumps({'status': 'passed',
        'compiler_sha256': report['compiler_sha256'], 'configurations': diagnostics,
        'scope': 'GCC execution of instrumented Clight pretty-print; proved CompCert assembly checked separately'}, indent=2)+'\n')


if __name__ == '__main__': main()
