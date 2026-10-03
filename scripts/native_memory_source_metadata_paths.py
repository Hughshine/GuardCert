"""Check reachable source-metadata fast paths and genuine fallback calls."""
import json
import subprocess
from native_zero_trip import function_body
from native_memory_layout_sequence_paths import printer_for_gcc
from native_memory_source_metadata import WORK, NAMES


def main():
    report = json.loads((WORK/'report.json').read_text())
    assert report['status'] == 'passed' and report['full_configuration_suite']
    diagnostics = {}
    for configuration in ['schedule-identity','schedule-interchange','schedule-fission',
                          'tile-2-3','tile-4-4','tile-17-13']:
        work = WORK/configuration
        dump = (work/'native_memory_source_metadata.light.c').read_text()
        instrumented = dump
        for index,function in enumerate(NAMES):
            body = function_body(dump,function)
            begin = body.index('switch (0)')
            end = body.index('continue;',begin)
            marked = body[:end]+f'guard_branch_hits[{index}]++; '+body[end:]
            instrumented = instrumented.replace(body,marked,1)
        instrumented = printer_for_gcc(instrumented)
        calls = []
        for index,function in enumerate(NAMES[:2]):
            for alias,start,n,m,hits in [(False,0,1,1,1),(True,0,1,1,0),
                                        (False,0,0,-2147483648,0),(False,0,1,0,0),
                                        (False,1,1,1,0)]:
                initial = 'for (x=0;x<64;x++) {a[x]=3*x+1;b[x]=5*x+7;}'
                invocation = f'{function}(a,{"a" if alias else "b"},{start},{n},{m},-7,11);'
                changed = start < n and m > 0
                result = (-7 if alias else -49) if function == 'unused_inner' else (4 if alias else -38)
                check = f'if (guard_branch_hits[{index}]!={hits} || out_i!={n} || out_j!={m if start<n else 77}) return 1;'
                check += 'for(x=0;x<64;x++) if (a[x]!='+(f'(x==0?{result}:3*x+1)' if changed else '3*x+1')+' || b[x]!=5*x+7) return 2;'
                calls.append(initial+f'guard_branch_hits[{index}]=0;'+invocation+check)
        for n,m,p,hits in [(1,2,1,1),(0,-2147483648,2147483647,0)]:
            initial = 'for(x=0;x<64;x++) {meta_a[x]=3*x+1;meta_b[x]=5*x+7;}'
            invocation = f'context_three(0,{n},{m},{p});'
            check = f'if(guard_branch_hits[2]!={hits} || out_i!={n} || out_j!={1 if n else 77} || out_k!={1 if n else 55}) return 3;'
            check += 'for(x=0;x<64;x++) if(meta_a[x]!='+('(x==0?15:3*x+1)' if n else '3*x+1')+' || meta_b[x]!=5*x+7) return 4;'
            calls.append(initial+'guard_branch_hits[2]=0;'+invocation+check)
        instrumented = 'int guard_branch_hits[3];\n'+instrumented
        instrumented += '\nint main(void) {int a[64],b[64],x;\n'+'\n'.join(calls)+'\nreturn 0;}\n'
        source = work/'branch-diagnostic.c'
        source.write_text(instrumented)
        compiled = subprocess.run(['gcc','-fwrapv','-Wno-builtin-declaration-mismatch','-Wno-discarded-qualifiers',
            str(source),'-o',str(work/'branch-diagnostic')],capture_output=True,text=True)
        (work/'branch-gcc-output.txt').write_text(compiled.stdout+compiled.stderr)
        compiled.check_returncode()
        subprocess.run([str(work/'branch-diagnostic')],check=True)
        diagnostics[configuration] = {'source_function_calls':len(calls),'fast_path_calls':3,
            'fallback_calls':9,'unused_coordinates_and_context_parameters_reachable':True,
            'aliased_pointer_fallback_preserves_results':True,'zero_trip_and_nonzero_start_preserve_counters':True}
        print(configuration,'branches checked:',len(calls),'calls',flush=True)
    (WORK/'branch-report.json').write_text(json.dumps({'status':'passed',
        'compiler_sha256':report['compiler_sha256'],'configurations':diagnostics,
        'scope':'GCC execution of instrumented Clight pretty-print; full CompCert assembly outputs checked separately'},indent=2)+'\n')


if __name__ == '__main__':
    main()
