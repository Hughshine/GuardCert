"""Check branch reachability and fallback in the extracted recursive compiler."""
import json
import subprocess
from native_zero_trip import function_body
from native_memory_layout_sequence_paths import printer_for_gcc
from native_memory_recursive import WORK,METADATA,ZERO_ONLY,model,execute


def dependence_witnesses():
    source,_=execute('deep_four_chain',0,[1,1,1,3])
    reverse,_=execute('deep_four_chain',0,[1,1,1,3],lambda p:(*p[0][:-1],-p[0][-1],p[1]))
    fission,_=execute('deep_four_chain',0,[1,1,1,3],lambda p:(p[1],*p[0]))
    assert source[1][0]!=reverse[1][0] and source[1][0]!=fission[1][0]
    return {'input':[0,1,1,1,3],'source_b0':source[1][0],
        'unprotected_reverse_b0':reverse[1][0],'unprotected_fission_b0':fission[1][0]}


def main():
    report=json.loads((WORK/'report.json').read_text());assert report['status']=='passed'
    witness=dependence_witnesses();diagnostics={}
    configurations=['interchange-4','interchange-5','interchange-6','reverse-last-4',
        'schedule-interchange-4','schedule-fission-4','tile-2-3','tile-4-4','tile-17-13','identity-8','identity-9']
    for configuration in configurations:
        work=WORK/configuration;dump=(work/'native_memory_recursive.light.c').read_text()
        functions=sorted(report['configurations'][configuration]['guarded_functions'])
        instrumented=dump
        for index,function in enumerate(functions):
            body=function_body(dump,function);guard=body.index('switch (0)');end=body.index('continue;',guard)
            marked=body[:end]+f'guard_branch_hits[{index}]++; '+body[end:]
            instrumented=instrumented.replace(body,marked,1)
        instrumented=printer_for_gcc(instrumented)
        calls,expected=[],''
        for index,function in enumerate(functions):
            dimensions,_=METADATA[function]
            if function in ZERO_ONLY:inputs=[(0,[0,0,-2147483648,2147483647],0),
                (0,[2,2,0,-2147483648],0),(0,[1,0,99,2147483647],0)]
            else:
                hits=2 if function.endswith('_context') else 1
                cap=report['configurations'][configuration]['common_guard_cap'][function]
                inputs=[(0,[1]*dimensions,hits),(0,[2]*dimensions,hits),
                    (0,[0]+[-2147483648]*(dimensions-1),0),(1,[2]*dimensions,0),
                    (0,[1]*(dimensions-1)+[cap+1],0)]
                inputs.extend((0,[2]*axis+[0]+[-2147483648]*(dimensions-axis-1),0) for axis in range(1,dimensions))
                unequal=[[1+(axis%2) for axis in range(dimensions)],
                    [2-(axis%2) for axis in range(dimensions)]]
                inputs.extend((0,counts,hits if max(counts)<=cap else 0) for counts in unequal)
            for start,counts,hit in inputs:
                calls.append(f'guard_branch_hits[{index}]=0; {function}({start},'+','.join(map(str,counts))+'); '
                    f'if (guard_branch_hits[{index}]!={hit}) return {20+len(calls)};')
                expected+=model(function,start,counts)
        if configuration in {'reverse-last-4','schedule-fission-4'}:
            calls.append('deep_four_chain(0,1,1,1,3);');expected+=model('deep_four_chain',0,[1,1,1,3])
        if configuration.startswith('tile-'):
            # Eight original axes plus two tile axes exceed the current pool.
            calls.append('deep_eight(0,2,2,2,2,2,2,2,2);');expected+=model('deep_eight',0,[2]*8)
        if configuration=='identity-9':
            calls.append('deep_nine(0,2,2,2,2,2,2,2,2,2);');expected+=model('deep_nine',0,[2]*9)
        instrumented=f'int guard_branch_hits[{max(1,len(functions))}];\n'+instrumented
        instrumented+='\nint main(void) {\n'+'\n'.join(calls)+'\nreturn 0; }\n'
        source=work/'branch-diagnostic.c';source.write_text(instrumented)
        subprocess.run(['gcc','-fwrapv','-Wno-builtin-declaration-mismatch','-Wno-discarded-qualifiers',str(source),
            '-o',str(work/'branch-diagnostic')],capture_output=True,check=True)
        output=subprocess.check_output([str(work/'branch-diagnostic')],text=True);assert output==expected,configuration
        (work/'branch-diagnostic-output.txt').write_text(output)
        diagnostics[configuration]={'all_guarded_nonempty_functions_have_actual_fast_path':bool(set(functions)-ZERO_ONLY),
            'every_zero_trip_dimension_and_nonzero_start_fallback_checked':bool(functions),
            'uninitialized_inner_bound_short_circuit_checked':bool(set(functions)&ZERO_ONLY),
            'insufficient_private_pool_source_result_checked':configuration.startswith('tile-') or configuration=='identity-9',
            'unequal_axis_counts_checked':bool(set(functions)-ZERO_ONLY),
            'source_function_calls':len(calls)}
        print(configuration,'recursive branch selection checked',flush=True)
    (WORK/'branch-report.json').write_text(json.dumps({'status':'passed','compiler_sha256':report['compiler_sha256'],
        'configurations':diagnostics,'unprotected_copy_chain_witness':witness,
        'scope':'GCC execution of instrumented Clight pretty-print; complete CompCert assembly checked separately'},indent=2)+'\n')


if __name__=='__main__':main()
