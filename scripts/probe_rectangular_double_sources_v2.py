"""Diagnose the actual source decoder using a separately linked native probe.

The probe reuses extracted checks and normalization. It is not the optimizer,
never supplies a semantic premise, and does not increase acceptance coverage.
"""
import json
import os
from pathlib import Path
import subprocess

from audit_interface_clight import ROOT,sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked


def main():
    work=permitted(ROOT/'build/rectangular-double-nests/source-probe-v4')
    if (work/'report.json').exists():raise ValueError('Successful diagnostic is frozen')
    bindings={}
    build=checked(permitted(ROOT/'build/rectangular-double-nests/compiler-attempts/native-v1/report.json'),bindings)
    base=permitted(ROOT/build['compiler']).parent
    attempts=[]
    for name in ['source-probe-v1','source-probe-v2','source-probe-v3','source-probe-v4']:
        folder=permitted(ROOT/'build/rectangular-double-nests'/name)
        attempts.append({'attempt':name,'linked':(folder/'probe').exists()})
        for path in folder.iterdir():
            if path.is_file():bindings[str(path.relative_to(ROOT))]=sha(permitted(path))
    parent=json.loads(permitted(ROOT/'build/rectangular-double-nests/source-probe-v1/baseline.json').read_text())
    for name,digest in parent['bindings'].items():
        if sha(permitted(ROOT/name))!=digest:raise ValueError('Changed diagnostic object '+name)
        bindings[name]=digest
    rows=[]
    for name in ['intratileopt1','intratileopt2','intratileopt3','intratileopt4','seq','spatial','matmul']:
        folder=work/name;folder.mkdir(exist_ok=False)
        source=permitted(ROOT/'build/benchmark-alignment/probe-v1'/name/'marked.c')
        bindings[str(source.relative_to(ROOT))]=sha(source)
        cmd=[str(work/'probe'),str(source),str(base/'runtime'),str(folder/'preprocessed.i')]
        env={key:value for key,value in os.environ.items() if not key.startswith('GUARDCERT_')}
        env['COMPCERT_CONFIG']=str(base/'compcert.ini')
        result=subprocess.run(cmd,cwd=folder,env=env,capture_output=True,text=True,timeout=60)
        (folder/'stdout').write_text(result.stdout);(folder/'stderr').write_text(result.stderr)
        row={'case':name,'returncode':result.returncode,'diagnostics':result.stdout.splitlines(),
             'command':cmd,'source_sha256':sha(source)}
        rows.append(row);print(json.dumps(row),flush=True)
    for path in [permitted(Path(__file__)),permitted(ROOT/'adapters/compcert-memory/native/GuardRectangularSourceProbeV2.ml'),
                 *[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))]=sha(permitted(path))
    report={'status':'diagnostic_complete' if all(row['returncode']==0 for row in rows) else 'rejected','cases':rows,'attempts':attempts,
            'compiler_entrypoint':build['whole_program_entrypoint'],
            'diagnostic_probe_is_not_a_transformation':True,'new_acceptance_coverage':False,
            'compiled_probe_uses_actual_extracted_source_checks':True,'bindings':bindings}
    (work/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    if any(row['returncode'] for row in rows):raise SystemExit(1)

if __name__=='__main__':main()
