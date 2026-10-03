"""Observe guards for negative affine addresses without widening proof claims."""
import json
import subprocess
from native_zero_trip import function_body
from native_memory_layout_sequence_paths import printer_for_gcc
from native_memory_signed import WORK,RANK,NAMES,model,execute


def dependence_witnesses():
    args=[3,0,1,3,1,3,-7]
    source=execute('signed_chain',*args)[0][0]
    reverse=execute('signed_chain',*args,
        order=lambda point:(point[0][0],-point[0][1],point[1]))[0][0]
    fission=execute('signed_chain',*args,order=lambda point:(point[1],*point[0]))[0][0]
    assert source!=reverse and source!=fission
    return {'input':args,'source_cell_63':source[63],
        'unprotected_reverse_cell_63':reverse[63],
        'unprotected_fission_cell_63':fission[63]}


def inputs(function,cap):
    if function=='signed_undef':
        return [([-1,0,0,-2147483648,1,3,-7],0),
            ([-1,0,2,0,1,-2147483648,2147483647],0)]
    rank=RANK[function]
    counts=[[1,1,1],[1,2,1],[2,1,2],[2,3,2],[3,2,3],[4,4,4]]
    if rank==2 and function!='signed_chain':counts+=[[5,5,1],[8,8,1]]
    parameters=[(3,-7),(-5,11),(2147483647,-2147483648),(-2147483648,2147483647)]
    result=[]
    for n,m,p in counts:
        for alpha,beta in parameters:
            hit=(2 if function=='signed_context' else 1) if max([n,m,p][:rank])<=cap else 0
            if function.startswith('signed_array'):
                result.append(([0,n,m,alpha,beta],hit))
            else:
                for offset in [0,3,17]:result.append(([offset,0,n,m,p,alpha,beta],hit))
    zero_counts=[[0,-2147483648,-2147483648],[2,0,-2147483648]]
    if rank==3:zero_counts+=[[2,2,0]]
    for n,m,p in zero_counts:
        result.append(([0,n,m,3,-7] if function.startswith('signed_array')
            else [-1,0,n,m,p,3,-7],0))
    if function.startswith('signed_array'):
        result.extend([([1,3,2,3,-7],0),([0,1,cap+1,3,-7],0)])
    else:
        result.extend([([3,1,3,2,2,3,-7],0),
            ([3,0,1,cap+1,1,3,-7] if rank==2 else [3,0,1,1,cap+1,3,-7],0)])
    return result


def main():
    report=json.loads((WORK/'report.json').read_text());assert report['status']=='passed'
    witness=dependence_witnesses();diagnostics={}
    selected=['interchange-2','interchange-3','reverse-last-2','schedule-interchange-2',
        'schedule-fission-2','tile-2-3','tile-4-4','tile-17-13','identity-2','identity-3']
    for configuration in selected:
        work=WORK/configuration;dump=(work/'native_memory_signed.light.c').read_text()
        functions=sorted(report['configurations'][configuration]['guarded_functions'])
        instrumented=dump
        for index,function in enumerate(functions):
            body=function_body(dump,function);begin=body.index('switch (0)');end=body.index('continue;',begin)
            marked=body[:end]+f'guard_branch_hits[{index}]++; '+body[end:]
            instrumented=instrumented.replace(body,marked,1)
        instrumented=printer_for_gcc(instrumented)
        calls=[];expected=''
        for index,function in enumerate(functions):
            cap=report['configurations'][configuration]['common_guard_cap'][function]
            for args,hit in inputs(function,cap):
                call=('' if function.startswith('signed_array') else 'run_')+function
                calls.append(f'guard_branch_hits[{index}]=0; {call}('+','.join(map(str,args))+'); '
                    f'if(guard_branch_hits[{index}]!={hit}) return {20+len(calls)};')
                expected+=model(function,args)
        # Missing source base evidence remains a safe refusal, including when
        # every access has a valid reflected index in the full C execution.
        calls.append('signed_array_no_zero_anchor(0,3,2,3,-7);')
        expected+=model('signed_array_no_zero_anchor',[0,3,2,3,-7])
        if configuration in {'reverse-last-2','schedule-fission-2'}:
            args=witness['input'];index=functions.index('signed_chain')
            assert report['configurations'][configuration]['common_guard_cap']['signed_chain']==1
            calls.append(f'guard_branch_hits[{index}]=0; run_signed_chain('+','.join(map(str,args))+
                f'); if(guard_branch_hits[{index}]!=0) return 19;')
            expected+=model('signed_chain',args)
        instrumented=f'int guard_branch_hits[{max(1,len(functions))}];\n'+instrumented
        instrumented+='\nint main(void) {\n'+'\n'.join(calls)+'\nreturn 0; }\n'
        source=work/'branch-diagnostic.c';source.write_text(instrumented)
        subprocess.run(['gcc','-fwrapv','-Wno-builtin-declaration-mismatch','-Wno-discarded-qualifiers',
            str(source),'-o',str(work/'branch-diagnostic')],capture_output=True,check=True)
        output=subprocess.check_output([str(work/'branch-diagnostic')],text=True)
        assert output==expected,configuration
        (work/'branch-diagnostic-output.txt').write_text(output)
        diagnostics[configuration]={'signed_access_actual_fast_path_checked':True,
            'unequal_axis_counts_checked':True,'signed_extreme_scalar_parameters_checked':True,
            'count_cap_and_nonzero_start_fallback_checked':True,
            'null_pointer_all_zero_trip_axes_checked':True,
            'missing_zero_anchor_source_result_checked':True,'source_function_calls':len(calls)}
        print(configuration,'signed access branches checked',flush=True)
    (WORK/'branch-report.json').write_text(json.dumps({'status':'passed',
        'compiler_sha256':report['compiler_sha256'],'configurations':diagnostics,
        'unprotected_signed_dependence_witness':witness,
        'scope':'GCC execution of instrumented Clight pretty-print; complete CompCert assembly checked separately'},indent=2)+'\n')


if __name__=='__main__':main()
