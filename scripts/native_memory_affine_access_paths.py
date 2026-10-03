"""Diagnose affine-source branch selection after assembly output validation."""
import json
import subprocess
from native_zero_trip import function_body
from native_memory_layout_sequence_paths import printer_for_gcc
from native_memory_affine_access import WORK, ACCEPTED, KINDS, model


def alias_witness(configuration):
    n,m=6,6
    points=[(i,j) for i in range(n) for j in range(2*i+m)]
    if configuration=='interchange': order=sorted(points,key=lambda x:(x[1],x[0]))
    elif configuration=='fission': order=points
    else:
        _,rows,columns=configuration.split('-'); rows,columns=int(rows),int(columns)
        order=sorted(points,key=lambda x:(x[0]//rows,x[1]//columns,x[0],x[1]))
    def execute(order):
        b=[5*x+2 for x in range(500)]
        for i,j in order: b[i*20+j]=b[j*17+i]
        return b
    source,candidate=execute(points),execute(order)
    different=[i for i,(a,b) in enumerate(zip(source,candidate)) if a!=b]
    return {'n':n,'m':m,'p':0,'different_cells':different} if different else None


def main():
    report=json.loads((WORK/'report.json').read_text()); assert report['status']=='passed'
    diagnostics={}
    for configuration in ['interchange','fission','tile-2-3','tile-4-4','tile-17-13']:
        work=WORK/configuration
        dumps=list(work.glob('*.light.c')); assert len(dumps)==1
        dump=dumps[0].read_text(); instrumented=dump
        functions=sorted(ACCEPTED)
        for index,function in enumerate(functions):
            body=function_body(dump,function)
            marked=body.replace('continue;',f'guard_branch_hits[{index}]++; continue;',1)
            assert marked!=body and instrumented.count(body)==1
            instrumented=instrumented.replace(body,marked,1)
        instrumented=printer_for_gcc(instrumented)
        calls,expected=[],''
        for index,function in enumerate(functions):
            hits=2 if KINDS[function]=='context' else 1
            inputs=[(0,1,1,0,hits),(0,0,-2147483648,2147483647,0),(2,4,5,1,0)]
            cap=report['configurations'][configuration]['outer_count_guard_upper'][function]
            if function=='affine_access_alias' and cap<6: inputs.append((0,6,6,0,0))
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
        diagnostics[configuration]={'actual_fast_branch_hits_checked_for_all_supported_functions':True,
            'zero_trip_nonzero_start_and_conditioned_count_fallback_checked':True,
            'source_execution_calls':len(calls),'same_array_transpose_counterexample':alias_witness(configuration)}
        print(configuration,'branch selection checked',flush=True)
    (WORK/'branch-report.json').write_text(json.dumps({'status':'passed','compiler_sha256':report['compiler_sha256'],
        'configurations':diagnostics,'scope':'GCC execution of instrumented Clight pretty-print; proved CompCert assembly checked separately'},indent=2)+'\n')


if __name__=='__main__':main()
