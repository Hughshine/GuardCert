"""Compare fact residualization with prior pruning and the same-backend original."""
import argparse
import json
import os
from pathlib import Path
import random
import re
import resource
import statistics
import subprocess
import time

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked, run, PLUTO

INPUTS = [(0,9223372036854775807,-9223372036854775808), (4096,0,0),
          (4096,3,5), (4096,4096,4096), (4097,3,5), (1,4097,3)]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--attempt',required=True)
    args=parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+',args.attempt):
        raise ValueError('Use a fresh simple attempt')
    bindings={}
    reports={name:checked(permitted(ROOT/path),bindings) for name,path in [
        ('residual','build/double-tree-model/compiler-attempts/native-residual-v1/report.json'),
        ('pruned','build/double-tree-model/compiler-attempts/native-pruned-v1/report.json'),
        ('source','build/double-tree-model/compiler-attempts/native-pruned-v1/report.json')]}
    original=permitted(ROOT/'build/double-tree-source/runtime-attempts/argv-v1/program.c')
    work=permitted(ROOT/'build/double-tree-residual/cost-attempts'/args.attempt)
    work.mkdir(parents=True,exist_ok=False)
    (work/'script.py').write_bytes(permitted(Path(__file__)).read_bytes())
    source=work/'program.c';source.write_bytes(original.read_bytes())
    reference,_,_=run(['gcc','-O2','-fno-fast-math','-ffp-contract=off',str(source),'-lm','-o',str(work/'reference')],work,'reference-compile')
    if reference['returncode']:
        raise ValueError('Reference compile failed')
    binaries={}
    installations={}
    for name,build in reports.items():
        folder=work/name;folder.mkdir()
        compiler=permitted(ROOT/build['compiler'])
        env={key:value for key,value in os.environ.items() if not key.startswith('GUARDCERT_')}
        env.update(GUARDCERT_ORIGINAL_MODE='tile',GUARDCERT_DOUBLE_TILING_MODE='tile',
                   GUARDCERT_PHASE_KIND='untiled',GUARDCERT_PLUTO=str(PLUTO),
                   GUARDCERT_ORIGINAL_OUTPUT=str(folder),GUARDCERT_SCOP_DIAGNOSTICS='1',
                   GUARDCERT_TREE_LOWER='0',GUARDCERT_TREE_UPPER='4096')
        compile_source=source
        if name=='source':
            compile_source=folder/'program.c'
            compile_source.write_text(source.read_text().replace('#pragma scop\n','').replace('#pragma endscop\n',''))
        result,out,err=run([str(compiler),'-fall','-stdlib',str(compiler.parent/'runtime'),'-dclight','-S',
                            '-o',str(folder/'program.s'),str(compile_source)],folder,'compiler',env)
        found=re.findall(r'GUARDCERT_TREE_INSTALLED regions=(\d+) phase_calls=(\d+) adaptations=(\d+)',(out+err).decode(errors='replace'))
        installed=list(map(int,found[-1])) if found else None
        if result['returncode'] or installed is None or installed[0]!=(0 if name=='source' else 1):
            raise ValueError('Complete marked-region installation required for '+name)
        installations[name]=installed
        if name!='source':
            generated=permitted(folder/'tiling-pipeline-1/tree-generated.loop').read_text()
            if generated.count('loop [')!=2 or generated.count('instruction array=')!=4 or 'loop [0,4096)' not in generated:
                raise ValueError('Same source-derived reference required')
            if name in ['pruned','residual']:
                actual=permitted(folder/'tiling-pipeline-1/tree-runtime-pruned.loop').read_text()
                if actual.count('loop [')!=3 or 'loop [0,4096)' in actual:
                    raise ValueError('Runtime upper selection required')
        if name=='residual':
            actual=permitted(folder/'tiling-pipeline-1/tree-runtime-residual.loop').read_text()
            if actual.count('guard ')!=4 or 'div(' in actual:
                raise ValueError('Expected fact-scoped residual membership and normalized bounds')
        link,_,_=run(['gcc','-no-pie',str(folder/'program.s'),'-lm','-o',str(folder/'program')],folder,'link')
        if link['returncode']:
            raise ValueError('Link failed')
        binaries[name]=folder/'program'
    expected={}
    for index,values in enumerate(INPUTS):
        folder=work/f'input-{index}';folder.mkdir()
        result,output,_=run([str(work/'reference'),*map(str,values)],folder,'reference')
        if result['returncode']:
            raise ValueError('Reference execution failed')
        expected[index]=output
        for name,binary in binaries.items():
            result,output,_=run([str(binary),*map(str,values)],folder,'warmup-'+name)
            if result['returncode'] or output!=expected[index]:
                raise ValueError('Warmup complete output mismatch')
    batches=[]
    rng=random.Random(20261010)
    for batch in range(7):
        order=[(index,name) for index in range(len(INPUTS)) for name in binaries]
        rng.shuffle(order)
        rows=[]
        for index,name in order:
            folder=work/f'input-{index}'
            before=resource.getrusage(resource.RUSAGE_CHILDREN)
            start=time.monotonic()
            result=subprocess.run([str(binaries[name]),*map(str,INPUTS[index])],capture_output=True,timeout=60)
            elapsed=time.monotonic()-start
            after=resource.getrusage(resource.RUSAGE_CHILDREN)
            cpu=(after.ru_utime-before.ru_utime)+(after.ru_stime-before.ru_stime)
            (folder/f'batch-{batch}-{name}.stdout').write_bytes(result.stdout)
            (folder/f'batch-{batch}-{name}.stderr').write_bytes(result.stderr)
            if result.returncode or result.stdout!=expected[index] or cpu<=0:
                raise ValueError('Measured complete execution must match the reference')
            rows.append({'input':index,'variant':name,'cpu_seconds':cpu,'wall_seconds':elapsed})
        batches.append(rows)
        print(json.dumps({'batch':batch,'complete_output_matches':18}),flush=True)
    cases=[]
    for index,values in enumerate(INPUTS):
        samples={name:[next(row['cpu_seconds'] for row in batch if row['input']==index and row['variant']==name)
                       for batch in batches] for name in binaries}
        p,c,d=values
        accepted=0<=p<=4096 and (p==0 or (0<=c<=4096 and 0<=d<=4096))
        cases.append({'values':list(values),'expected_acceptance_from_emitted_capture':accepted,
                      'median_process_cpu_seconds':{name:statistics.median(sample) for name,sample in samples.items()},
                      'median_paired_residual_over_pruned_ratio':statistics.median([new/old for old,new in zip(samples['pruned'],samples['residual'])]),
                      'median_paired_residual_over_source_ratio':statistics.median([new/old for old,new in zip(samples['source'],samples['residual'])]),
                      'median_paired_pruned_over_source_ratio':statistics.median([new/old for old,new in zip(samples['source'],samples['pruned'])])})
    for path in [Path(__file__),original,PLUTO,*[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))]=sha(permitted(path))
    report={'status':'passed','source':str(original.relative_to(ROOT)),'source_byte_identical':True,
            'numeric_types_and_marked_computation_preserved':True,'profile':[0,4096],
            'installations':installations,'batches':batches,'cases':cases,'random_seed':20261010,
            'samples_per_variant_and_input':7,'complete_measured_outputs_matched':126, 'same_backend_unmarked_original_compared':True,
            'timing_scope':'Child process user+system CPU; includes executable startup, argv parsing, initialization, checks, candidate/fallback, public exits, complete-state digest and printing.',
            'kernel_only_call_timing':False,'separate_guard_cpu_cost':False,
            'CPU_pinning_or_frequency_control':False,'raw_original_corpus_coverage_added':False,
            'assembly_modified_or_target_instrumented':False,'full_goal_complete':False,'bindings':bindings}
    (work/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'passed','cases':cases,'report':str((work/'report.json').relative_to(ROOT))}),flush=True)


if __name__=='__main__':
    main()
