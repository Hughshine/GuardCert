"""Check dynamic whole fusion in repeated sites, continuations and callers."""
import argparse
import json
import os
from pathlib import Path
import re

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from check_piece_factory_contexts import selected_groups
from probe_piece_models import checked, run, PLUTO

BUILD = ROOT/'build/dynamic-piece-factory/standalone-build-v1/report.json'
REPLAY = ROOT/'build/dynamic-piece-factory/runtime-attempts/symbolic-standalone-v1/report.json'
PORTABLE = ROOT/'docs/dynamic-piece-integer-contexts.json'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--attempt', required=True)
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+', args.attempt):
        raise ValueError('Use a fresh simple attempt')
    bindings = {}
    build, replay = [checked(path,bindings) for path in [BUILD,REPLAY]]
    if (replay['status'] != 'passed'
            or not build['integer_coverage_splits_are_untrusted_data_consumed_by_existing_checker']):
        raise ValueError('Require actual independent-bound untiled/tiled installation')
    compiler = permitted(ROOT/build['compiler'])
    source = REPLAY.parent/'variant.c'
    original = permitted(source).read_text()
    start = original.index('#pragma scop')
    end = original.index('#pragma endscop')+len('#pragma endscop')
    region = original[start:end]
    before, after = original[:start], original[end:]
    marker = 'static void guardcert_after(long long tag) { printf("tag=%lld\\n",tag); }\n'

    def finish(text):
        return text.replace('int main(int argc,char **argv)', marker+'\nint main(int argc,char **argv)',1)

    first = region+'\nguardcert_after(1LL);\n'
    variants = [
        ('multiple-marked',finish(before+first+region+'\nguardcert_after(2LL);\n'+after),{},2,None),
        ('marked-and-unmarked',finish(before+first+region.replace('#pragma scop','')
            .replace('#pragma endscop','')+'\nguardcert_after(2LL);\n'+after),{},1,None),
        ('halo-continuation',finish(before+'A[102][2]=3.25;\n'+first
            +'printf("halo=%.17g\\n",A[102][2]+B[101][101]);\n'+after),{},1,None),
        ('enclosing-conditional',finish(before+'if (A[0][0]>-1000.0) {\n'+first+'}\n'+after),{},1,None),
        ('private-pool-refusal',finish(before+first+after),{'GUARDCERT_DOUBLE_PRIVATE_COUNT':'1'},0,None),
    ]
    helper = marker+'\nstatic void guardcert_kernel(long long *px,long long *py) {\n'
    helper += 'long long x=17,y=23;\n'+first+'*px=x; *py=y;\n}\n'
    caller = before+'long long cookie=71;\nguardcert_kernel(&x,&y);\n'
    caller += 'printf("cookie=%lld\\n",cookie);\n'+after
    caller = caller.replace('int main(int argc,char **argv)',helper+'\nint main(int argc,char **argv)',1)
    variants.append(('caller-live-temp-and-stack-exits',caller,{},1,'cookie=71'))
    values = [(100,100),(101,100),(100,101),(33,31),(2,3),
              (0,9223372036854775807),(-1,9223372036854775807)]
    work = ROOT/'build/dynamic-piece-factory/context-attempts'/args.attempt
    work.mkdir(parents=True,exist_ok=False)
    (work/'script.py').write_bytes(Path(__file__).read_bytes())
    rows = []
    for name,text,options,expected_fusions,expected_line in variants:
        case = work/name
        case.mkdir()
        variant = case/'variant.c'
        variant.write_text(text)
        gcc,_,_ = run(['gcc','-O0','-ffp-contract=off',str(variant),'-lm',
                      '-o',str(case/'reference')],case,'gcc')
        references = {}
        if gcc['returncode'] == 0:
            for index,(n,m) in enumerate(values):
                reference,expected,_ = run([str(case/'reference'),str(n),str(m)],case,f'reference-{index}')
                references[index] = reference,expected
        for mode in ['untiled','tiled']:
            directory = case/mode
            directory.mkdir()
            current = directory/'program.c'
            current.write_bytes(variant.read_bytes())
            env = {key:value for key,value in os.environ.items() if not key.startswith('GUARDCERT_')}
            env.update(GUARDCERT_ORIGINAL_MODE='tile',GUARDCERT_DOUBLE_TILING_MODE='tile',
                       GUARDCERT_PHASE_KIND=mode,GUARDCERT_TREE_LOWER='0',GUARDCERT_TREE_UPPER='100',
                       GUARDCERT_PLUTO=str(PLUTO),GUARDCERT_ORIGINAL_OUTPUT=str(directory),GUARDCERT_SCOP_DIAGNOSTICS='1')
            env.update(options)
            compiled,_,_ = run([str(compiler),'-fall','-stdlib',str(compiler.parent/'runtime'),
                               '-dclight','-S','-o',str(directory/'program.s'),str(current)],directory,'compiler',env)
            row = {'case':name,'mode':mode,'input_sha256':sha(current),'options':options,
                   'gcc':gcc,'compiler':compiled,'expected_whole_fusions':expected_fusions,'runs':[]}
            if compiled['returncode'] == 0:
                linked,_,_ = run(['gcc','-no-pie',str(directory/'program.s'),'-lm',
                                  '-o',str(directory/'program')],directory,'link')
                row['link'] = linked
                if linked['returncode'] == 0:
                    groups = selected_groups(directory/'program.light.c')
                    row['selected_store_groups'] = groups
                    row['actual_whole_fusions'] = sum(bool(group['stores']['shared_A_B_loops']) for group in groups)
                    for index,(n,m) in enumerate(values):
                        native,actual,_ = run([str(directory/'program'),str(n),str(m)],directory,f'native-{index}')
                        reference,expected = references[index]
                        row['runs'].append({'N':n,'M':m,'native':native,
                            'complete_output_matches':native['returncode'] == reference['returncode'] == 0 and actual == expected,
                            'public_controls_match':f'controls={max(0,n)},{max(0,m) if n>0 else 23}' in actual.decode().splitlines(),
                            'caller_line_present':expected_line is None or expected_line in actual.decode().splitlines()})
            row['passed'] = bool(row.get('actual_whole_fusions') == expected_fusions
                and len(row['runs']) == len(values) and all(run['complete_output_matches']
                and run['public_controls_match'] and run['caller_line_present'] for run in row['runs']))
            rows.append(row)
            (directory/'row.json').write_text(json.dumps(row,indent=2)+'\n')
            print(json.dumps({key:row.get(key) for key in ['case','mode','passed','actual_whole_fusions']}),flush=True)
    for path in [Path(__file__),ROOT/'scripts/check_piece_factory_contexts.py',PLUTO,
                 *[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status':'passed' if all(row['passed'] for row in rows) else 'rejected',
              'compiler_entrypoint':build['whole_program_entrypoint'],
              'whole_program_theorem':build['actual_source_Csem_to_Asm_theorem'],
              'all_sources_are_disclosed_dynamic_context_variants':True,
              'original_arrays_and_IEEE_kernel_retained':True,'cases':rows,
              'configuration_count':len(rows),'runtime_inputs':values,
              'complete_native_calls':len(rows)*len(values),
              'compile_once_per_configuration':True,'caller_stack_iterator_exits_exercised':True,
              'runtime_guard_refusal_inputs_included':True,
              'controlled_cost_comparison':False,'full_goal_complete':False,'bindings':bindings}
    filename = 'report.json' if report['status'] == 'passed' else 'rejection.json'
    if report['status'] == 'passed':
        portable = {key:value for key,value in report.items() if key != 'bindings'}
        portable['report'] = str((work/filename).relative_to(ROOT))
        with PORTABLE.open('x') as output:
            output.write(json.dumps(portable,indent=2)+'\n')
        bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (work/filename).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'configurations':len(rows),'bindings':len(bindings)}),flush=True)
    if report['status'] != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
