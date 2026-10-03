"""Observe loop guard acceptance separately from complete assembly execution."""
import hashlib
import json
import subprocess
from native_zero_trip import function_body
from native_memory_layout_sequence_paths import printer_for_gcc
from native_memory_loop_alias import COMPILER, SOURCE, WORK, NAMES, check_build, full_inputs, output_model


def expected_hits(args):
    _,kind,start,n,_,_ = args
    separated = kind in {0,2,4} or (kind == 1 and n == 1)
    return int(start == 0 and 0 < n <= 1024 and separated)


def main():
    stamp = check_build()
    report = json.loads((WORK/'report.json').read_text())
    assert report['status'] == 'passed' and report['full_configuration_suite']
    assert report['compiler_sha256'] == stamp['compiler_sha256']
    assert report['source_sha256'] == hashlib.sha256(SOURCE.read_bytes()).hexdigest()
    witness = [0,1,0,33,-7,11]
    assert output_model(witness) != output_model(witness,reverse=True)
    diagnostics = {}
    for name in ['schedule-identity','schedule-fission','direct-identity',
                 'schedule-reflect','direct-reflect','shift-reflect']:
        work = WORK/name
        dump = printer_for_gcc((work/(SOURCE.stem+'.light.c')).read_text())
        marker = '\nint guard_original_main(void)\n{'
        assert marker in dump
        instrumented = dump[:dump.index(marker)]
        functions = report['configurations'][name]['guarded_functions']
        assert sorted(functions) == sorted(NAMES)
        for index,fn in enumerate(functions):
            body = function_body(instrumented,fn)
            assert body.count('switch (0)') == 1,(name,fn)
            begin = body.index('switch (0)')
            end = body.index('continue;',begin)
            marked = body[:end]+f'guard_branch_hits[{index}]++; '+body[end:]
            instrumented = instrumented.replace(body,marked,1)
        calls,expected = [],''
        fast,fallback,above_old_cap = 0,0,0
        for index,fn in enumerate(functions):
            if fn == 'scan_undefined':
                for n in [0,-2147483648]:
                    calls.append(f'guard_branch_hits[{index}]=0; scan_undefined({n}); '
                                 f'if (guard_branch_hits[{index}]!=0 || scan_out_i!=0) return {30+len(calls)}; '
                                 f'printf("undefined {n} %d\\n",scan_out_i);')
                    expected += f'undefined {n} 0\n'
                    fallback += 1
                continue
            which = int(fn == 'scan_chain')
            for args in [a for a in full_inputs() if a[0] == which]:
                hits = expected_hits(args)
                fast += bool(hits)
                fallback += not hits
                above_old_cap += bool(hits and args[3]>8)
                arguments = ','.join(map(str,args))
                calls.append(f'guard_branch_hits[{index}]=0; scan_run({arguments}); '
                             f'if (guard_branch_hits[{index}]!={hits}) return {30+len(calls)};')
                expected += output_model(args)
        assert fast and fallback and above_old_cap
        instrumented = f'int guard_branch_hits[{len(functions)}];\n'+instrumented
        instrumented += '\nint main(void) {\n'+'\n'.join(calls)+'\nreturn 0; }\n'
        diagnostic = work/'branch-diagnostic.c'
        diagnostic.write_text(instrumented)
        result = subprocess.run(['gcc','-fwrapv','-Wno-builtin-declaration-mismatch','-Wno-discarded-qualifiers',
            str(diagnostic),'-o',str(work/'branch-diagnostic')],capture_output=True,text=True)
        (work/'branch-gcc-output.txt').write_text(result.stdout+result.stderr)
        result.check_returncode()
        output = subprocess.check_output([str(work/'branch-diagnostic')],text=True,timeout=120)
        assert output == expected,name
        (work/'branch-diagnostic-output.txt').write_text(output)
        diagnostics[name] = {'source_function_calls':len(calls),'actual_fast_path_calls':fast,
            'fallback_calls':fallback,'actual_fast_calls_above_old_cap':above_old_cap,
            'logical_window_boundary_and_cap_rejection_checked':True,
            'same_block_disjoint_slices_and_partial_overlap_checked':True,
            'undefined_empty_loop_pointer_and_scalar_operands_checked':True,
            'full_arrays_and_public_counters_match_model':True}
        print(name,'branches:',fast,'fast,',fallback,'fallback;',above_old_cap,'fast calls above old cap',flush=True)
    (WORK/'branch-report.json').write_text(json.dumps({'status':'passed',
        'compiler_sha256':stamp['compiler_sha256'],'configurations':diagnostics,
        'unprotected_reverse_order_witness':{'input':witness,'changes_result_without_guard':True},
        'scope':'GCC execution of instrumented Clight pretty-print; complete CompCert assembly results checked separately'},indent=2)+'\n')


if __name__ == '__main__':
    main()
