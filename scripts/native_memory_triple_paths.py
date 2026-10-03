"""Check actual branch selection in printed Clight after assembly validation."""
import json
import subprocess
from native_zero_trip import function_body
from native_memory_layout_sequence_paths import printer_for_gcc
from native_memory_triple import WORK,model,execute,ZERO_ONLY


def reversal_witness():
    source,_=execute('triple_chain',0,1,1,3)
    candidate,_=execute('triple_chain',0,1,1,3,lambda p:(p[0],p[1],-p[2],p[3]))
    differences=[idx for idx,(a,b) in enumerate(zip(source[1],candidate[1])) if a!=b]
    assert differences
    return {'input':[0,1,1,3],'different_b_cells':differences,'source_b0':source[1][0],
        'unprotected_reverse_b0':candidate[1][0]}


def main():
    report=json.loads((WORK/'report.json').read_text()); assert report['status']=='passed'
    witness=reversal_witness(); diagnostics={}
    configurations=['interchange','i-k-j','reverse-k','schedule-fission','tile-2-3','tile-4-4','tile-17-13']
    for configuration in configurations:
        work=WORK/configuration; dump=(work/'native_memory_triple.light.c').read_text()
        functions=sorted(report['configurations'][configuration]['guarded_functions'])
        instrumented=dump
        for index,function in enumerate(functions):
            body=function_body(dump,function); guard=body.index('switch (0)'); end=body.index('continue;',guard)
            marked=body[:end]+f'guard_branch_hits[{index}]++; '+body[end:]
            instrumented=instrumented.replace(body,marked,1)
        instrumented=printer_for_gcc(instrumented)
        calls,expected=[],''
        for index,function in enumerate(functions):
            if function=='triple_uninitialized_outer': inputs=[(0,0,0,0,0),(2,1,0,0,0)]
            elif function=='triple_uninitialized_middle': inputs=[(0,2,0,0,0)]
            else:
                hits=2 if function=='triple_context' else 1
                cap=report['configurations'][configuration]['common_guard_cap'][function]
                inputs=[(0,1,1,1,hits),(0,3,2,2,hits),
                    (0,0,-2147483648,2147483647,0),(0,2,0,-2147483648,0),
                    (0,2,2,0,0),(2,4,3,2,0),(0,1,1,cap+1,0)]
            for start,n,m,l,hit in inputs:
                calls.append(f'guard_branch_hits[{index}]=0; {function}({start},{n},{m},{l}); '
                    f'if (guard_branch_hits[{index}]!={hit}) return {20+len(calls)};')
                expected+=model(function,start,n,m,l)
        # The reversed copy chain is rejected; execute its concrete witness as well.
        if configuration=='reverse-k':
            calls.append('triple_chain(0,1,1,3);'); expected+=model('triple_chain',0,1,1,3)
        instrumented=f'int guard_branch_hits[{len(functions)}];\n'+instrumented
        instrumented+='\nint main(void) {\n'+'\n'.join(calls)+'\nreturn 0; }\n'
        source=work/'branch-diagnostic.c'; source.write_text(instrumented)
        subprocess.run(['gcc','-fwrapv','-Wno-builtin-declaration-mismatch','-Wno-discarded-qualifiers',str(source),
            '-o',str(work/'branch-diagnostic')],capture_output=True,check=True)
        output=subprocess.check_output([str(work/'branch-diagnostic')],text=True); assert output==expected,configuration
        (work/'branch-diagnostic-output.txt').write_text(output)
        diagnostics[configuration]={'positive_three_dimensional_fast_paths_checked':bool(set(functions)-ZERO_ONLY),
            'all_zero_trip_dimensions_nonzero_start_and_extent_condition_fallback_checked':True,
            'uninitialized_bounds_short_circuit_checked':bool(set(functions)&ZERO_ONLY),
            'source_execution_calls':len(calls)}
        print(configuration,'three-level branch selection checked',flush=True)
    (WORK/'branch-report.json').write_text(json.dumps({'status':'passed','compiler_sha256':report['compiler_sha256'],
        'configurations':diagnostics,'unprotected_reverse_copy_chain_witness':witness,
        'scope':'GCC execution of instrumented Clight pretty-print; complete CompCert assembly checked separately'},indent=2)+'\n')


if __name__=='__main__':main()
