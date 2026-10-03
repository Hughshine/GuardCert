"""Observe affine address guards in Clight, separately from assembly results."""
import hashlib
import json
import subprocess
from native_zero_trip import function_body
from native_memory_layout_sequence_paths import printer_for_gcc
from native_memory_affine_alias import (
    COMPILER, SOURCE, RESOURCE_SOURCE, WORK, NAMES, check_build, full_inputs,
    output_model, separated, resource_inputs, resource_model,
)


def mark_functions(dump, functions):
    repaired = printer_for_gcc(dump)
    marker = '\nint guard_original_main(void)\n{'
    assert marker in repaired
    marked = repaired[:repaired.index(marker)]
    for index, fn in enumerate(functions):
        body = function_body(marked, fn)
        assert body.count('switch (0)') == 1, fn
        begin = body.index('switch (0)')
        end = body.index('continue;', begin)
        marked = marked.replace(body, body[:end] +
            f'guard_branch_hits[{index}]++; ' + body[end:], 1)
    return f'int guard_branch_hits[{max(1, len(functions))}];\n' + marked


def run_diagnostic(work, source, calls, expected):
    diagnostic = work/'branch-diagnostic.c'
    diagnostic.write_text(source + '\nint main(void) {\n' +
        '\n'.join(calls) + '\nreturn 0; }\n')
    result = subprocess.run(['gcc', '-fwrapv', '-Wno-builtin-declaration-mismatch',
        '-Wno-discarded-qualifiers', str(diagnostic), '-o', str(work/'branch-diagnostic')],
        capture_output=True, text=True)
    (work/'branch-gcc-output.txt').write_text(result.stdout+result.stderr)
    result.check_returncode()
    output = subprocess.check_output([str(work/'branch-diagnostic')], text=True, timeout=120)
    assert output == expected, work
    (work/'branch-diagnostic-output.txt').write_text(output)


def primary_diagnostic(name, configuration):
    work = WORK/name
    functions = configuration['guarded_functions']
    source = mark_functions((work/(SOURCE.stem+'.light.c')).read_text(), functions)
    calls, expected = [], ''
    fast, fallback, above_old_cap = 0, 0, 0
    for index, fn in enumerate(functions):
        if fn == 'affine_undefined':
            for n in [0, -2147483648]:
                calls.append(f'guard_branch_hits[{index}]=0; affine_undefined({n}); '
                    f'if (guard_branch_hits[{index}]!=0 || affine_out_i!=0) return 1; '
                    f'printf("undefined {n} %d\\n",affine_out_i);')
                expected += f'undefined {n} 0\n'
                fallback += 1
            continue
        which = NAMES.index(fn)
        cap = functions[fn]['count_guard_cap']
        for args in [a for a in full_inputs() if a[0] == which]:
            hits = int(args[2] == 0 and 0 < args[3] <= cap and separated(args))
            fast += hits
            fallback += 1-hits
            above_old_cap += int(hits and args[3] > 8)
            calls.append(f'guard_branch_hits[{index}]=0; affine_run({",".join(map(str,args))}); '
                f'if (guard_branch_hits[{index}]!={hits}) return 1;')
            expected += output_model(args)
    assert calls and fallback
    if name not in {'constant-coordinate', 'wrong-reflect'}:
        assert fast and above_old_cap
    run_diagnostic(work, source, calls, expected)
    print(name, 'branches:', fast, 'fast,', fallback, 'fallback;',
        above_old_cap, 'fast calls above old cap', flush=True)
    return {'source_function_calls': len(calls), 'actual_fast_path_calls': fast,
        'fallback_calls': fallback, 'actual_fast_calls_above_old_cap': above_old_cap,
        'actual_affine_addresses_determine_alias_decision': True,
        'same_block_disjoint_slices_and_partial_overlap_checked': True,
        'undefined_empty_loop_operands_and_public_counter_checked': True,
        'full_arrays_and_public_counters_match_model': True}


def resource_diagnostic(name, configuration):
    work = WORK/'resources'/name
    functions = configuration['guarded_functions']
    source = mark_functions((work/(RESOURCE_SOURCE.stem+'.light.c')).read_text(), functions)
    calls, expected = [], ''
    fast, fallback = 0, 0
    indices = {fn: index for index, fn in enumerate(functions)}
    for reads, kind, n in resource_inputs():
        fn = f'alias_reads_{reads}'
        cells = {(pointer, stride*i+bias) for i in range(n)
            for pointer, stride, bias in [('p',2,0), ('q',3,1)]}
        addresses = {(int(pointer == 'q' and kind == 0), index) for pointer,index in cells}
        disjoint = len(addresses) == len(cells)
        hits = int(fn in functions and 0 < n <= functions[fn]['count_guard_cap'] and disjoint)
        fast += hits
        fallback += 1-hits
        invoke = f'resource_run({reads},{kind},{n});'
        if fn in indices:
            index = indices[fn]
            invoke = f'guard_branch_hits[{index}]=0; ' + invoke + \
                f' if (guard_branch_hits[{index}]!={hits}) return 1;'
        calls.append(invoke)
        expected += resource_model(reads,kind,n)
    assert fast and fallback
    run_diagnostic(work, source, calls, expected)
    print('resources', name, 'branches:', fast, 'fast,', fallback, 'fallback', flush=True)
    return {'source_function_calls': len(calls), 'actual_fast_path_calls': fast,
        'fallback_calls': fallback, 'raw_access_limit_boundary_checked': True,
        'finite_guard_fallback_and_unchanged_source_checked': True,
        'full_arrays_and_public_counters_match_model': True}


def main():
    stamp = check_build()
    report = json.loads((WORK/'report.json').read_text())
    assert report['status'] == 'passed' and report['full_configuration_suite']
    assert report['compiler_sha256'] == stamp['compiler_sha256']
    assert report['source_sha256'] == hashlib.sha256(SOURCE.read_bytes()).hexdigest()
    assert report['resource_source_sha256'] == hashlib.sha256(RESOURCE_SOURCE.read_bytes()).hexdigest()
    witness = [3,0,0,33,-7,11]
    assert separated(witness)
    assert output_model(witness) != output_model(witness,reverse=True)
    assert output_model(witness) != output_model(witness,fission=True)
    diagnostics = {}
    for name in ['schedule-identity', 'schedule-fission', 'schedule-reflect',
                 'direct-identity', 'direct-reflect', 'constant-coordinate', 'wrong-reflect']:
        configuration = report['configurations'][name]
        if configuration['guarded_functions']:
            diagnostics[name] = primary_diagnostic(name, configuration)
    resources = {name: resource_diagnostic(name, configuration)
        for name, configuration in report['resource_configurations'].items()}
    (WORK/'branch-report.json').write_text(json.dumps({'status':'passed',
        'compiler_sha256':stamp['compiler_sha256'], 'configurations':diagnostics,
        'resource_configurations':resources,
        'dependence_witness':{'input':witness,'nonalias_alone_does_not_allow_reverse_or_fission':True},
        'scope':'GCC execution of instrumented Clight pretty-print; complete CompCert assembly execution checked separately'},
        indent=2)+'\n')


if __name__ == '__main__':
    main()
