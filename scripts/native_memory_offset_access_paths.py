"""Diagnose anchored offset branch selection after assembly output validation."""
import json
import subprocess
from native_zero_trip import function_body
from native_memory_layout_sequence_paths import printer_for_gcc
from native_memory_offset_access import WORK, ACCEPTED, KINDS, model


def neighbor_witness(configuration):
    n,m=6,6
    points=[(i,j) for i in range(n) for j in range(2*i+m)]
    if configuration=='interchange': order=sorted(points,key=lambda x:(x[1],x[0]))
    elif configuration=='fission': order=points
    else:
        _,rows,columns=configuration.split('-'); rows,columns=int(rows),int(columns)
        order=sorted(points,key=lambda x:(x[0]//rows,x[1]//columns,x[0],x[1]))
    def execute(order):
        b=[5*x+2 for x in range(500)]
        for i,j in order: b[i*20+j]=b[j*17+i+1]
        return b
    source,candidate=execute(points),execute(order)
    different=[i for i,(a,b) in enumerate(zip(source,candidate)) if a!=b]
    return {'n':n,'m':m,'p':0,'different_cells':different} if different else None


def chain_fission_witness():
    points=[(0,j,statement) for j in range(2) for statement in range(4)]
    def execute(order):
        a,b,c=[x*3+1 for x in range(480)],[x*5+2 for x in range(500)],[-777]*600
        for i,j,statement in order:
            w=i*20+j; t=i*24+j
            if statement==0: b[w]=a[j*17+i]
            elif statement==1: c[t+1]=b[w]
            elif statement==2: c[t]=c[t+1]
            else: b[w]=b[w+1]
        return b,c
    source=execute(points); candidate=execute(sorted(points,key=lambda x:(x[2],x[0],x[1])))
    different=[index for index,(a,b) in enumerate(zip(source[0],candidate[0])) if a!=b]
    assert different==[0] and source[0][0]==7 and candidate[0][0]==52
    return {'n':1,'m':2,'p':0,'different_b_cells':different,'source_b0':7,'unprotected_fission_b0':52}


def main():
    report=json.loads((WORK/'report.json').read_text()); assert report['status']=='passed'
    diagnostics={}
    for configuration in ['interchange','fission','tile-2-3','tile-4-4','tile-17-13']:
        work=WORK/configuration
        dumps=list(work.glob('*.light.c')); assert len(dumps)==1
        dump=dumps[0].read_text(); instrumented=dump
        functions=sorted(ACCEPTED)
        guarded=set(report['configurations'][configuration]['guarded_functions'])
        for index,function in enumerate(functions):
            if function not in guarded: continue
            body=function_body(dump,function)
            marked=body.replace('continue;',f'guard_branch_hits[{index}]++; continue;',1)
            assert marked!=body and instrumented.count(body)==1
            instrumented=instrumented.replace(body,marked,1)
        instrumented=printer_for_gcc(instrumented)
        calls,expected=[],''
        for index,function in enumerate(functions):
            hits=(2 if KINDS[function]=='context' else 1) if function in guarded else 0
            inputs=[(0,1,1,0,hits),(0,0,-2147483648,2147483647,0),(2,4,5,1,0)]
            cap=report['configurations'][configuration]['outer_count_guard_upper'].get(function,0)
            if function=='offset_self_transpose' and cap<6: inputs.append((0,6,6,0,0))
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
        diagnostics[configuration]={'branch_hits_and_fallback_checked_for_all_supported_functions':True,
            'zero_trip_nonzero_start_and_conditioned_count_fallback_checked':True,
            'source_execution_calls':len(calls),'guarded_functions':sorted(guarded),'same_array_neighbor_counterexample':neighbor_witness(configuration)}
        if configuration=='fission': diagnostics[configuration]['multi_statement_fission_counterexample']=chain_fission_witness()
        print(configuration,'branch selection checked',flush=True)
    (WORK/'branch-report.json').write_text(json.dumps({'status':'passed','compiler_sha256':report['compiler_sha256'],
        'configurations':diagnostics,'scope':'GCC execution of instrumented Clight pretty-print; proved CompCert assembly checked separately'},indent=2)+'\n')


if __name__=='__main__':main()
