"""Measure complete processes with repeated dynamic regions and an opaque boundary.

The wrapper is a disclosed source variant. The boundary prevents removal of
repeated stores across calls; its overhead is included in every configuration.
"""
import argparse
import json
import os
from pathlib import Path
import re
import resource
import statistics

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from observe_piece_fusion import store_loops
from probe_piece_models import checked, run, PLUTO

BUILD = ROOT/'build/double-tree-model/compiler-attempts/native-dynamic-piece-selective-v1/report.json'
REPLAY = ROOT/'build/dynamic-piece-factory/runtime-attempts/symbolic-selective-v1/report.json'
PORTABLE = ROOT/'docs/dynamic-piece-selective-cost.json'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--attempt',required=True)
    parser.add_argument('--trials',type=int,default=7)
    parser.add_argument('--repetitions',type=int,default=1000)
    args = parser.parse_args()
    if (not re.fullmatch('[a-z0-9-]+',args.attempt) or args.trials<3
            or not 2<=args.repetitions<=10000000):
        raise ValueError('Fresh attempt, at least three trials, bounded repetitions required')
    bindings = {}
    build,replay = [checked(path,bindings) for path in [BUILD,REPLAY]]
    if replay['status']!='passed':
        raise ValueError('Require actual dynamic untiled and tiled installation')
    source = REPLAY.parent/'variant.c'
    original = permitted(source).read_text()
    start = original.index('#pragma scop')
    end = original.index('#pragma endscop')+len('#pragma endscop')
    text = original[:start]+('for (long long guardcert_repeat=0; guardcert_repeat<guardcert_repeats; ++guardcert_repeat) {\n')
    text += original[start:end]+'\nguardcert_boundary();\n}\n'+original[end:]
    text = text.replace('int main(int argc,char **argv)',
        'extern void guardcert_boundary(void);\nint main(int argc,char **argv)',1)
    text = text.replace('if (argc!=3) return 2;',
        'if (argc!=4) return 2;\n  long long guardcert_repeats=atoll(argv[3]);\n'
        '  if (guardcert_repeats<1 || guardcert_repeats>10000000) return 3;',1)
    work = ROOT/'build/dynamic-piece-factory/cost-attempts'/args.attempt
    work.mkdir(parents=True,exist_ok=False)
    (work/'script.py').write_bytes(Path(__file__).read_bytes())
    boundary = work/'boundary.c'
    boundary.write_text('void guardcert_boundary(void) { __asm__ __volatile__("" ::: "memory"); }\n')
    opaque,_,_ = run(['gcc','-O2','-c',str(boundary),'-o',str(work/'boundary.o')],work,'boundary')
    if opaque['returncode']:
        raise ValueError('Boundary build failed')
    compiler = permitted(ROOT/build['compiler'])
    affinity = sorted(os.sched_getaffinity(0))
    cpu = min(affinity)
    os.sched_setaffinity(0,{cpu})
    configurations = {}
    modes = ['unmarked','untiled','tiled']
    try:
        for mode in modes:
            directory = work/mode
            directory.mkdir()
            current = directory/'program.c'
            current.write_text(text.replace('#pragma scop\n','').replace('#pragma endscop\n','') if mode=='unmarked' else text)
            env = {key:value for key,value in os.environ.items() if not key.startswith('GUARDCERT_')}
            env.update(GUARDCERT_ORIGINAL_MODE='tile',GUARDCERT_DOUBLE_TILING_MODE='tile',
                GUARDCERT_PHASE_KIND='tiled' if mode=='tiled' else 'untiled',
                GUARDCERT_TREE_LOWER='0',GUARDCERT_TREE_UPPER='100',GUARDCERT_PLUTO=str(PLUTO),
                GUARDCERT_ORIGINAL_OUTPUT=str(directory),GUARDCERT_SCOP_DIAGNOSTICS='1')
            compiled,_,_ = run([str(compiler),'-fall','-stdlib',str(compiler.parent/'runtime'),
                '-dclight','-S','-o',str(directory/'program.s'),str(current)],directory,'compiler',env,timeout=600)
            if compiled['returncode']:
                raise ValueError('Compiler failed: '+mode)
            row = {'compiler':compiled,'source_sha256':sha(current)}
            if mode!='unmarked':
                clight = permitted(directory/'program.light.c').read_text()
                labels = list(re.finditer(r'\b__guardcert_scop_\d+:',clight))
                if len(labels)!=1:
                    raise ValueError('Require one actual selected repeat site')
                tail = clight[labels[0].end():]
                stop = re.search(r'\bguardcert_boundary\(\s*\);',tail)
                if stop is None:
                    raise ValueError('Require the actual opaque boundary after the region')
                groups = store_loops(tail[:stop.start()])
                if not groups['shared_A_B_loops']:
                    raise ValueError('Repeated context must retain actual whole fusion: '+mode)
                row['Clight_store_grouping'] = groups
            linked,_,_ = run(['gcc','-no-pie',str(directory/'program.s'),str(work/'boundary.o'),
                '-lm','-o',str(directory/'program')],directory,'link')
            if linked['returncode']:
                raise ValueError('Link failed: '+mode)
            row['link'] = linked
            configurations[mode] = row
        reference = work/'reference.c'
        reference.write_text(text)
        gcc,_,_ = run(['gcc','-O0','-ffp-contract=off',str(reference),str(work/'boundary.o'),
            '-lm','-o',str(work/'reference')],work,'gcc')
        if gcc['returncode']:
            raise ValueError('Reference failed to compile')
        cases = [(100,100),(33,31),(101,100),(100,101),(0,9223372036854775807),(2,0)]
        results = []
        for n,m in cases:
            case = work/f'inputs-{n}-{m}'
            case.mkdir()
            repetitions = args.repetitions if n>0 and m>0 else min(10000000,args.repetitions*1000)
            expected_call,expected,_ = run([str(work/'reference'),str(n),str(m),str(repetitions)],case,'reference')
            if expected_call['returncode']:
                raise ValueError('Reference execution failed')
            samples = {mode:[] for mode in modes}
            order = []
            for trial in range(args.trials+2):
                schedule = modes[trial%3:]+modes[:trial%3]
                if trial%2:
                    schedule = list(reversed(schedule))
                for mode in schedule:
                    before = resource.getrusage(resource.RUSAGE_CHILDREN)
                    outcome,actual,_ = run([str(work/mode/'program'),str(n),str(m),str(repetitions)],
                        case,f'{mode}-sample-{trial}')
                    after = resource.getrusage(resource.RUSAGE_CHILDREN)
                    if outcome['returncode'] or actual!=expected:
                        raise ValueError('Complete repeated output changed: '+mode)
                    sample = {'wall_seconds':outcome['elapsed_seconds'],
                        'child_cpu_seconds':after.ru_utime-before.ru_utime+after.ru_stime-before.ru_stime}
                    if trial>=2:
                        samples[mode].append(sample)
                        order.append({'trial':trial-1,'mode':mode,**sample})
            medians = {mode:{metric:statistics.median(row[metric] for row in samples[mode])
                for metric in ['wall_seconds','child_cpu_seconds']} for mode in modes}
            ratios = {mode:{metric:medians[mode][metric]/medians['unmarked'][metric]
                for metric in medians[mode]} for mode in ['untiled','tiled']}
            row = {'N':n,'M':m,'repetitions':repetitions,'reference':expected_call,
                'samples':samples,'order':order,'medians':medians,'over_source_ratios':ratios,
                'all_complete_outputs_match':True}
            results.append(row)
            (case/'row.json').write_text(json.dumps(row,indent=2)+'\n')
            print(json.dumps({'N':n,'M':m,'over_source_ratios':ratios}),flush=True)
        for path in [Path(__file__),PLUTO,*[p for p in work.rglob('*') if p.is_file()]]:
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
        report = {'status':'measured','compiler_entrypoint':build['whole_program_entrypoint'],
            'whole_program_theorem':build['actual_source_Csem_to_Asm_theorem'],
            'disclosed_repeated_dynamic_context_variant':True,
            'original_arrays_and_IEEE_kernel_retained':True,'configurations':configurations,
            'boundary_separately_compiled_without_LTO':True,'boundary_cost_included':True,
            'measurement_scope':'complete process: initialization, repeated guard/candidate-or-fallback/public-exit/boundary, digest and startup',
            'gcc':gcc,'opaque_boundary':opaque,'results':results,
            'trials_per_configuration_and_input':args.trials,'warmups_per_configuration_and_input':2,
            'same_CompCert_compiler_and_flags':True,'cpu_affinity':cpu,
            'external_host_load_controlled':False,'other_goal_commands_running_during_samples':False,
            'guard_cost_isolated':False,'benchmark_wide_profitability_claimed':False,
            'full_goal_complete':False,'bindings':bindings}
        portable = {key:value for key,value in report.items() if key!='bindings'}
        portable['report'] = str((work/'report.json').relative_to(ROOT))
        with PORTABLE.open('x') as output:
            output.write(json.dumps(portable,indent=2)+'\n')
        bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
        (work/'report.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps({'status':'measured','cases':len(results),'bindings':len(bindings)}),flush=True)
    except Exception as error:
        for path in [Path(__file__), PLUTO, *[p for p in work.rglob('*') if p.is_file()]]:
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
        (work/'rejection.json').write_text(json.dumps({'status':'rejected',
            'error':str(error),'compiler_entrypoint':build['whole_program_entrypoint'],
            'whole_program_theorem':build['actual_source_Csem_to_Asm_theorem'],
            'partial_configurations':configurations,'bindings':bindings},indent=2)+'\n')
        raise
    finally:
        os.sched_setaffinity(0,set(affinity))


if __name__=='__main__':
    main()
