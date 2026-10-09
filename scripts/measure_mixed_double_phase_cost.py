"""Measure pinned repeated matmul calls under the same complete compiler.

The repeat-count context is a disclosed source variant, not original coverage.
CPU affinity is fixed for all processes; external host load remains uncontrolled.
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
from probe_current_double_corpus import checked, run, PLUTO


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler-report',type=Path,required=True)
    parser.add_argument('--attempt',required=True)
    parser.add_argument('--trials',type=int,default=7)
    parser.add_argument('--repetitions',type=int,default=200)
    args=parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+',args.attempt) or args.trials<3 or args.repetitions<2:
        raise ValueError('Fresh attempt, at least three trials and two repetitions required')
    bindings={}
    build=checked(permitted(ROOT/args.compiler_report),bindings)
    compiler=permitted(ROOT/build['compiler'])
    input_path=permitted(ROOT/'build/benchmark-alignment/probe-v1/matmul/marked.c')
    original=input_path.read_text();bindings[str(input_path.relative_to(ROOT))]=sha(input_path)
    start=original.index('#pragma scop');end=original.index('#pragma endscop')+len('#pragma endscop')
    repeated=original[:start]+('for (int guardcert_repeat=0; guardcert_repeat<'+str(args.repetitions)+'; ++guardcert_repeat) {\n')+original[start:end]+'\n}\n'+original[end:]
    work=ROOT/'build/mixed-double-phases/cost-attempts'/args.attempt
    work.mkdir(parents=True,exist_ok=False)
    (work/'script.py').write_bytes(permitted(Path(__file__)).read_bytes())
    old_affinity=sorted(os.sched_getaffinity(0));cpu=min(old_affinity)
    os.sched_setaffinity(0,{cpu})
    if os.sched_getaffinity(0)!={cpu}:raise ValueError('Affinity was not set')
    builds={}
    modes=['unmarked','tiled','untiled']
    try:
        for mode in modes:
            directory=work/mode;directory.mkdir()
            source=directory/'program.c'
            text=repeated if mode!='unmarked' else repeated.replace('#pragma scop\n','').replace('#pragma endscop\n','')
            source.write_text(text)
            env={key:value for key,value in os.environ.items() if not key.startswith('GUARDCERT_')}
            env.update(GUARDCERT_ORIGINAL_MODE='tile',GUARDCERT_DOUBLE_TILING_MODE='tile',
                       GUARDCERT_TILE_SIZES='32',GUARDCERT_PLUTO=str(PLUTO),
                       GUARDCERT_ORIGINAL_OUTPUT=str(directory),GUARDCERT_SCOP_DIAGNOSTICS='1')
            if mode=='untiled':env['GUARDCERT_PHASE_ORDER']='0,2,1'
            outcome,out,err=run([str(compiler),'-fall','-stdlib',str(compiler.parent/'runtime'),
                '-dclight','-S','-o',str(directory/'program.s'),str(source)],directory,'compiler',env,timeout=600)
            trace=(out+err).decode(errors='replace')
            counts=re.findall(r'GUARDCERT_DOUBLE_INSTALLED original=(\d+) initialized=(\d+) regions=(\d+) pipeline_calls=(\d+) reduction=(\d+)',trace)
            installed=list(map(int,counts[-1])) if counts else None
            if outcome['returncode'] or installed is None or installed[2]!=(0 if mode=='unmarked' else 1):
                raise ValueError('Expected zero unmarked or one actual candidate site: '+mode)
            link,_,_=run(['gcc','-no-pie',str(directory/'program.s'),'-lm','-o',str(directory/'program')],directory,'link')
            if link['returncode']:raise ValueError('Link failed')
            builds[mode]={'compiler':outcome,'link':link,'installed':installed,
                          'phase_shapes':re.findall(r'^GUARDCERT_DOUBLE_PHASE_SHAPE .*',trace,re.M)}
        reference_source=work/'reference.c';reference_source.write_text(repeated)
        gcc,_,_=run(['gcc','-O0','-ffp-contract=off',str(reference_source),'-lm','-o',str(work/'reference')],work,'gcc',timeout=180)
        if gcc['returncode']:raise ValueError('Reference build failed')
        result,expected,_=run([str(work/'reference')],work,'reference',timeout=180)
        if result['returncode']:raise ValueError('Reference run failed')
        samples={mode:[] for mode in modes};order=[]
        for trial in range(args.trials+2):
            schedule=modes[trial%3:]+modes[:trial%3]
            if trial%2:schedule=list(reversed(schedule))
            for mode in schedule:
                directory=work/mode;before=resource.getrusage(resource.RUSAGE_CHILDREN)
                outcome,output,_=run([str(directory/'program')],directory,'sample-'+str(trial),timeout=180)
                after=resource.getrusage(resource.RUSAGE_CHILDREN)
                if outcome['returncode'] or output!=expected:raise ValueError('Complete output changed: '+mode)
                sample={'wall_seconds':outcome['elapsed_seconds'],
                        'user_seconds':after.ru_utime-before.ru_utime,
                        'system_seconds':after.ru_stime-before.ru_stime,
                        'child_cpu_seconds':after.ru_utime-before.ru_utime+after.ru_stime-before.ru_stime}
                if trial>=2:samples[mode].append(sample);order.append({'trial':trial-1,'mode':mode,**sample})
                print(json.dumps({'trial':trial,'mode':mode,**sample}),flush=True)
        medians={mode:{metric:statistics.median(row[metric] for row in rows) for metric in rows[0]}
                 for mode,rows in samples.items()}
        ratios={mode:{metric:medians[mode][metric]/medians['unmarked'][metric]
                      for metric in ['wall_seconds','child_cpu_seconds']}
                for mode in ['tiled','untiled']}
        for path in [Path(__file__),PLUTO,*[p for p in work.rglob('*') if p.is_file()]]:
            bindings[str(path.relative_to(ROOT))]=sha(permitted(path))
        report={'status':'measured','case':'matmul','repetitions_per_call':args.repetitions,
                'original_source':str(input_path.relative_to(ROOT)),
                'repeat_context_is_disclosed_variant_not_original_corpus':True,
                'original_numeric_types_arrays_and_IEEE_expression_tree_retained':True,
                'compiler_entrypoint':build['whole_program_entrypoint'],
                'whole_program_theorem':build['actual_source_Csem_to_Asm_theorem'],
                'builds':builds,'two_warmups_per_variant':True,'trials_per_variant':args.trials,
                'samples':samples,'order':order,'medians':medians,'over_unmarked_ratios':ratios,
                'same_compiler_and_flags':True,'all_outputs_match_repeated_GCC':True,
                'cpu_affinity':cpu,'original_cpu_affinity':old_affinity,
                'cpu_affinity_fixed_for_all_builds_and_executions':True,
                'external_host_load_controlled':False,'other_goal_commands_running_during_samples':False,
                'measurement_scope':'complete process including startup, one initialization, repeated original regions and digest',
                'guard_cost_isolated':False,'benchmark_wide_profitability_claimed':False,
                'full_goal_complete':False,'bindings':bindings}
        (work/'report.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps({'status':'measured','medians':medians,'over_unmarked_ratios':ratios}),flush=True)
    finally:
        os.sched_setaffinity(0,set(old_affinity))


if __name__=='__main__':main()
