"""Diagnose a synthesized width guard and demonstrate why the wider candidate is unsafe."""
import json
import subprocess
from native_zero_trip import function_body
from native_memory_layout_sequence_paths import printer_for_gcc
from native_memory_conditioned_width import WORK, KINDS, model
from native_memory_offset_access_paths import chain_fission_witness


def main():
    report=json.loads((WORK/'report.json').read_text()); assert report['status']=='passed'
    witness=chain_fission_witness()
    assert witness['different_b_cells'],witness
    diagnostics={}
    for configuration in ['identity','interchange','fission','tile-2-3']:
        work=WORK/configuration; dumps=list(work.glob('*.light.c')); assert len(dumps)==1
        dump=dumps[0].read_text(); instrumented=dump; functions=sorted(KINDS)
        for index,function in enumerate(functions):
            body=function_body(dump,function)
            marked=body.replace('continue;',f'guard_branch_hits[{index}]++; continue;',1)
            assert marked!=body and instrumented.count(body)==1
            instrumented=instrumented.replace(body,marked,1)
        instrumented=printer_for_gcc(instrumented)
        calls,expected=[],''
        for index,function in enumerate(functions):
            hits=2 if KINDS[function]=='context' else 1
            # Several outer iterations enter the width-one fast path.
            cap=report['configurations'][configuration]['outer_count_guard_upper'][function]
            if configuration=='fission': assert cap>=4,(function,cap)
            inputs=[(0,1,1,0,hits),(0,4,1,0,hits if cap>=4 else 0),
                (0,0,-2147483648,2147483647,0),(2,4,5,1,0)]
            # Fission's width-two witness must retain the original execution.
            if configuration=='fission': inputs.append((0,1,2,0,0))
            for start,n,m,p,hit in inputs:
                calls.append(f'guard_branch_hits[{index}]=0; {function}({start},{n},{m},{p}); '
                    f'if (guard_branch_hits[{index}]!={hit}) return {20+len(calls)};')
                expected+=model(function,start,n,m,p)
        instrumented=f'int guard_branch_hits[{len(functions)}];\n'+instrumented
        instrumented+='\nint main(void) {\n'+'\n'.join(calls)+'\nreturn 0; }\n'
        source=work/'branch-diagnostic.c'; source.write_text(instrumented)
        subprocess.run(['gcc','-Wno-builtin-declaration-mismatch','-Wno-discarded-qualifiers',str(source),
            '-o',str(work/'branch-diagnostic')],capture_output=True,check=True)
        output=subprocess.check_output([str(work/'branch-diagnostic')],text=True)
        assert output==expected,configuration
        (work/'branch-diagnostic-output.txt').write_text(output)
        diagnostics[configuration]={'multi_outer_iteration_input_branch_checked':True,
            'multi_outer_iteration_fast_path_required':configuration=='fission',
            'zero_trip_nonzero_start_fallback_checked':True,'source_execution_calls':len(calls),
            'width_two_fission_fallback_checked':configuration=='fission'}
        print(configuration,'width guard branches checked',flush=True)
    (WORK/'branch-report.json').write_text(json.dumps({'status':'passed','compiler_sha256':report['compiler_sha256'],
        'configurations':diagnostics,'unprotected_width_two_fission_witness':witness,
        'scope':'GCC execution of instrumented Clight pretty-print; complete CompCert assembly checked separately'},indent=2)+'\n')


if __name__=='__main__':main()
