"""Attempt actual scheduling, tiling and intra-tile scheduling on the pinned original corpus.

Installation, scheduling effects and native observations are recorded separately.
The two disclosed initializer adaptations remain separate source variants.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import time
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

PARENT = ROOT / 'build/benchmark-alignment/probe-v1/report.json'
COMPAT = ROOT / 'build/benchmark-alignment/harness-compat-v1/report.json'
PLUTO = ROOT / 'build/polyhedral-pipeline/pluto-source/tool/pluto'

def checked(path, bindings):
    value = json.loads(permitted(path).read_text())
    for name,digest in value['bindings'].items():
        if sha(permitted(ROOT / name)) != digest: raise ValueError('Changed input: '+name)
        if name in bindings and bindings[name] != digest: raise ValueError('Conflicting input: '+name)
        bindings[name] = digest
    bindings[str(path.relative_to(ROOT))] = sha(path)
    return value

def run(argv,directory,label,env=None,timeout=180):
    start=time.monotonic()
    try:
        proc=subprocess.run(argv,cwd=directory,env=env,capture_output=True,timeout=timeout)
        result={'returncode':proc.returncode,'timeout':False}; out,err=proc.stdout,proc.stderr
    except subprocess.TimeoutExpired as error:
        result={'returncode':None,'timeout':True}; out,err=error.stdout or b'',error.stderr or b''
    for suffix,data in [('stdout',out),('stderr',err)]:
        with (directory / (label+'.'+suffix)).open('xb') as target: target.write(data)
    result.update(argv=argv,elapsed_seconds=time.monotonic()-start)
    return result,out,err

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler-report',type=Path,required=True)
    parser.add_argument('--attempt',required=True)
    parser.add_argument('--compiler-timeout',type=int,default=600)
    parser.add_argument('--witness-axes',type=int)
    parser.add_argument('--cases',nargs='+')
    parser.add_argument('--private-count',type=int)
    parser.add_argument('--phase-trace',action='store_true')
    args=parser.parse_args()
    if args.compiler_timeout<=0 or (args.witness_axes is not None and not 0<=args.witness_axes<=32):
        raise ValueError('Positive compiler timeout and witness axes in [0,32] required')
    if not re.fullmatch('[a-z0-9-]+',args.attempt): raise ValueError('Use a simple new attempt')
    if args.private_count is not None and args.private_count<0:
        raise ValueError('Private count must be nonnegative')
    bindings={}
    build=checked(ROOT / args.compiler_report,bindings)
    parent=checked(PARENT,bindings); compatibility=checked(COMPAT,bindings)
    inventory=json.loads(permitted(ROOT / 'docs/benchmark-alignment-inventory.json').read_text())
    names={row['case'] for row in inventory['polcert']['cases']}
    if len(names)!=62 or names!={row['case'] for row in parent['results']}:
        raise ValueError('Expected the complete pinned corpus')
    if args.cases:
        selected=set(args.cases)
        if not selected<=names: raise ValueError('Unknown original case')
        names=selected
    compiler=ROOT / build['compiler']
    work=ROOT / 'build/benchmark-alignment/adaptive-tiled-attempts' / args.attempt
    work.mkdir(parents=True,exist_ok=False)
    (work / 'script.py').write_bytes(Path(__file__).read_bytes())
    rows=[]
    originals={row['case']:row for row in parent['results']}
    variants=[(case,'original',PARENT.parent / case / 'marked.c') for case in sorted(names)]
    variants += [(row['case'],'disclosed-initializer-adaptation',COMPAT.parent / row['case'] / 'adapted.c')
                 for row in compatibility['cases'] if row['case'] in names]
    for case,variant,input_path in variants:
        original=permitted(input_path).read_text()
        expected_path=PARENT.parent / case / 'reference-run.stdout'
        if originals[case]['reference_execution']['returncode']!=0: raise ValueError('Missing original reference')
        expected=permitted(expected_path).read_bytes()
        directory=work / (case+'-'+variant); directory.mkdir()
        row={'case':case,'variant':variant,'input':str(input_path.relative_to(ROOT)),
             'input_sha256':sha(input_path),'original_GCC_reference':str(expected_path.relative_to(ROOT)),
             'configurations':{}}
        for mode in ['tile']:
            target=directory / mode; target.mkdir()
            text=original.replace('#pragma scop\n','').replace('#pragma endscop\n','') if mode=='unmarked' else original
            source=target / 'program.c'; source.write_text(text)
            env={key:value for key,value in os.environ.items() if not key.startswith('GUARDCERT_')}
            env.update(GUARDCERT_ORIGINAL_MODE='tile', GUARDCERT_DOUBLE_TILING_MODE='tile', GUARDCERT_TILE_SIZES='32',
                       GUARDCERT_PLUTO=str(PLUTO),GUARDCERT_ORIGINAL_OUTPUT=str(target),GUARDCERT_SCOP_DIAGNOSTICS='1')
            if args.private_count is not None: env['GUARDCERT_DOUBLE_PRIVATE_COUNT']=str(args.private_count)
            if args.phase_trace: env['GUARDCERT_PHASE_TRACE']='1'
            if args.witness_axes is not None: env['GUARDCERT_DOUBLE_WITNESS_AXES']=str(args.witness_axes)
            result,out,err=run([str(compiler),'-fall','-stdlib',str(compiler.parent / 'runtime'),'-dclight','-S',
                '-o',str(target / 'program.s'),str(source)],target,'compiler',env,timeout=args.compiler_timeout)
            trace=(out+err).decode(errors='replace')
            installed=re.findall(r'GUARDCERT_DOUBLE_INSTALLED original=(\d+) initialized=(\d+) regions=(\d+) pipeline_calls=(\d+) reduction=(\d+)',trace)
            config={'compiler':result,'source_sha256':sha(source),'installed':list(map(int,installed[-1])) if installed else None,
                'scheduler_changes':[p.read_text() for p in sorted(target.glob('pipeline-*/scheduler.log'))
                    if 'After intra-tile optimize' in p.read_text()],
                'proposal_reuses':trace.count('GUARDCERT_DOUBLE_PROPOSAL_REUSED'),
                'tiling_trace':re.findall(r'^GUARDCERT_DOUBLE_TILING_INSTALLED .*',trace,re.M),
                'tiling_phase_calls':trace.count('GUARDCERT_DOUBLE_TILING_PIPELINE call='),
                'actual_raw_candidates':len(list(target.glob('tiling-pipeline-*/raw-generated.loop'))),
                'actual_final_candidates':len(list(target.glob('tiling-pipeline-*/generated.loop'))),
                'selection_trace':re.findall(r'^GUARDCERT_SCOP .*',trace,re.M),
                'policy_trace':re.findall(r'^GUARDCERT_DOUBLE_POLICY .*',trace,re.M),
                'phase_trace':re.findall(r'^GUARDCERT_PHASE .*',trace,re.M),
                'last_oracle_event':(re.findall(r'^GUARDCERT_ORACLE .*',trace,re.M) or [None])[-1]}
            if result['returncode']!=0:
                config['status']='compiler_timeout' if result['timeout'] else 'frontend_or_compiler_refusal'
            else:
                link,_,_=run(['gcc','-no-pie',str(target / 'program.s'),'-lm','-o',str(target / 'program')],target,'link')
                config['link']=link
                if link['returncode']!=0: config['status']='link_failure'
                else:
                    native,actual,_=run([str(target / 'program')],target,'native')
                    config['native']=native
                    config['digest_matches_original_GCC']=native['returncode']==0 and actual==expected
                    config['status']='native_match' if config['digest_matches_original_GCC'] else 'native_mismatch_or_timeout'
            row['configurations'][mode]=config
        baseline=directory / 'unmarked/program.light.c'
        for mode,config in row['configurations'].items():
            code=directory / mode / 'program.light.c'
            config['emitted_Clight_equals_unmarked']=code.read_bytes()==baseline.read_bytes() if code.exists() and baseline.exists() else None
            # A changed guard/lowering is not itself evidence of nonidentity scheduling.
            config['nonidentity_effect_requires_analysis']=mode=='tile' and config['installed'] is not None and config['installed'][2]>0
        rows.append(row)
        (directory / 'row.json').write_text(json.dumps(row,indent=2)+'\n')
        print(json.dumps({'case':case,'variant':variant,'status':{m:x['status'] for m,x in row['configurations'].items()},
            'installed':{m:x['installed'] for m,x in row['configurations'].items()}}),flush=True)
    for path in [Path(__file__),ROOT / 'docs/benchmark-alignment-inventory.json',PLUTO,
                 *[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))]=sha(permitted(path))
    result={'status':'diagnostic_complete','original_cases_attempted':len(names), 'full_corpus_attempted':len(names)==62, 'compiler_timeout_seconds':args.compiler_timeout, 'witness_axes_override':args.witness_axes,'source_variants':len(rows),
        'compiler_entrypoint':build['whole_program_entrypoint'],'whole_program_theorem':build['actual_source_Csem_to_Asm_theorem'],
        'source_revision':inventory['polcert']['revision'],'modes':['tile'], 'tile_sizes':'32', 'private_count_override':args.private_count,'phase_trace_requested':args.phase_trace,'results':rows,
        'native_configuration_matches':sum(c['status']=='native_match' for r in rows for c in r['configurations'].values()),
        'native_failures':[r['case']+'-'+m for r in rows for m,c in r['configurations'].items()
            if c['status'] in {'native_mismatch_or_timeout','link_failure'}],
        'installed_cases':[r['case'] for r in rows if r['variant']=='original' and r['configurations']['tile']['installed']
            and r['configurations']['tile']['installed'][2]>0],
        'source_numeric_types_and_computations_preserved':True, 'requested_phase':'automatic affine scheduling, rectangular tiling and intra-tile scheduling; no identity option','original_baseline_reference_reused':True,
        'installed_regions_are_not_nonidentity_coverage':True,'controlled_cost_comparison':False,
        'full_goal_complete':False,'bindings':bindings}
    (work / 'report.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in {'results','bindings'}}),flush=True)
    if result['native_failures']: raise SystemExit(1)

if __name__=='__main__': main()
