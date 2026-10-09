"""Check the bounded-witness successor on the pinned original corpus.

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
PRIOR = ROOT / 'build/benchmark-alignment/current-double-attempts/corpus-v1/report.json'

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
    args=parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+',args.attempt): raise ValueError('Use a simple new attempt')
    bindings={}
    build=checked(ROOT / args.compiler_report,bindings)
    parent=checked(PARENT,bindings); compatibility=checked(COMPAT,bindings)
    prior=checked(PRIOR,bindings)
    inventory=json.loads(permitted(ROOT / 'docs/benchmark-alignment-inventory.json').read_text())
    names={row['case'] for row in inventory['polcert']['cases']}
    if len(names)!=62 or names!={row['case'] for row in parent['results']}:
        raise ValueError('Expected the complete pinned corpus')
    compiler=ROOT / build['compiler']
    work=ROOT / 'build/benchmark-alignment/witness-policy-attempts' / args.attempt
    work.mkdir(parents=True,exist_ok=False)
    (work / 'script.py').write_bytes(Path(__file__).read_bytes())
    rows=[]
    originals={row['case']:row for row in parent['results']}
    variants=[(case,'original',PARENT.parent / case / 'marked.c') for case in sorted(names)]
    variants += [(row['case'],'disclosed-initializer-adaptation',COMPAT.parent / row['case'] / 'adapted.c')
                 for row in compatibility['cases']]
    for case,variant,input_path in variants:
        original=permitted(input_path).read_text()
        expected_path=PARENT.parent / case / 'reference-run.stdout'
        if originals[case]['reference_execution']['returncode']!=0: raise ValueError('Missing original reference')
        expected=permitted(expected_path).read_bytes()
        directory=work / (case+'-'+variant); directory.mkdir()
        row={'case':case,'variant':variant,'input':str(input_path.relative_to(ROOT)),
             'input_sha256':sha(input_path),'original_GCC_reference':str(expected_path.relative_to(ROOT)),
             'configurations':{}}
        for mode in ['affine']:
            target=directory / mode; target.mkdir()
            text=original.replace('#pragma scop\n','').replace('#pragma endscop\n','') if mode=='unmarked' else original
            source=target / 'program.c'; source.write_text(text)
            env={key:value for key,value in os.environ.items() if not key.startswith('GUARDCERT_')}
            env.update(GUARDCERT_ORIGINAL_MODE='affine' if mode=='unmarked' else mode,
                       GUARDCERT_PLUTO=str(PLUTO),GUARDCERT_ORIGINAL_OUTPUT=str(target),GUARDCERT_SCOP_DIAGNOSTICS='1')
            result,out,err=run([str(compiler),'-fall','-stdlib',str(compiler.parent / 'runtime'),'-dclight','-S',
                '-o',str(target / 'program.s'),str(source)],target,'compiler',env)
            trace=(out+err).decode(errors='replace')
            installed=re.findall(r'GUARDCERT_DOUBLE_INSTALLED original=(\d+) initialized=(\d+) regions=(\d+) pipeline_calls=(\d+) reduction=(\d+)',trace)
            config={'compiler':result,'source_sha256':sha(source),'installed':list(map(int,installed[-1])) if installed else None,
                'scheduler_changes':[p.read_text() for p in sorted(target.glob('pipeline-*/scheduler.log'))
                    if 'After intra-tile optimize' in p.read_text()],
                'proposal_reuses':trace.count('GUARDCERT_DOUBLE_PROPOSAL_REUSED'),
                'selection_trace':re.findall(r'^GUARDCERT_SCOP .*',trace,re.M)}
            if result['returncode']!=0:
                config['status']='frontend_or_compiler_refusal'
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
        baseline=PRIOR.parent / (case+'-'+variant) / 'unmarked/program.light.c'
        for mode,config in row['configurations'].items():
            code=directory / mode / 'program.light.c'
            config['emitted_Clight_equals_unmarked']=code.exists() and baseline.exists() and code.read_bytes()==baseline.read_bytes()
            # A changed guard/lowering is not itself evidence of nonidentity scheduling.
            config['nonidentity_effect_requires_analysis']=mode=='affine' and config['installed'] is not None and config['installed'][2]>0
        rows.append(row)
        (directory / 'row.json').write_text(json.dumps(row,indent=2)+'\n')
        print(json.dumps({'case':case,'variant':variant,'status':{m:x['status'] for m,x in row['configurations'].items()},
            'installed':{m:x['installed'] for m,x in row['configurations'].items()}}),flush=True)
    for path in [Path(__file__),ROOT / 'docs/benchmark-alignment-inventory.json',PLUTO,
                 *[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))]=sha(permitted(path))
    result={'status':'diagnostic_complete','original_cases_attempted':62,'source_variants':len(rows),
        'compiler_entrypoint':build['whole_program_entrypoint'],'whole_program_theorem':build['actual_source_Csem_to_Asm_theorem'],
        'source_revision':inventory['polcert']['revision'],'modes':['affine'],'prior_corpus_report_sha256':sha(PRIOR),'results':rows,
        'native_configuration_matches':sum(c['status']=='native_match' for r in rows for c in r['configurations'].values()),
        'native_failures':[r['case']+'-'+m for r in rows for m,c in r['configurations'].items()
            if c['status'] in {'native_mismatch_or_timeout','link_failure'}],
        'installed_cases':[r['case'] for r in rows if r['variant']=='original' and r['configurations']['affine']['installed']
            and r['configurations']['affine']['installed'][2]>0],
        'source_numeric_types_and_computations_preserved':True,'original_baseline_reference_reused':True,
        'installed_regions_are_not_nonidentity_coverage':True,
        'proof_and_whole_program_entrypoint_unchanged':True,
        'witness_policy':'identity or one adjacent interchange, default six axes; bounded and incomplete','controlled_cost_comparison':False,
        'full_goal_complete':False,'bindings':bindings}
    (work / 'report.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in {'results','bindings'}}),flush=True)
    if result['native_failures']: raise SystemExit(1)

if __name__=='__main__': main()
