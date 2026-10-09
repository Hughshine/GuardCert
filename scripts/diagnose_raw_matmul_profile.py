"""Preserve profile and raw matching diagnostics for the two-site context attempt."""
import json
import os
from pathlib import Path
import subprocess
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

BUILD = ROOT / 'build/original-matmul/compiler-attempts/raw-profile-native-v1/report.json'
NATIVE = ROOT / 'build/original-matmul/compiler-native-checks/raw-context-v2'
WORK = ROOT / 'build/original-matmul/profile-diagnostics-v1'

def main():
    build = json.loads(BUILD.read_text())
    for path,digest in build['bindings'].items():
        if sha(permitted(ROOT / path)) != digest:
            raise ValueError('Changed build input: '+path)
    WORK.mkdir(parents=True,exist_ok=False)
    compiler = ROOT / build['compiler']
    rows = []
    for case in ['multiple-marked','marked-and-unmarked']:
        directory = WORK / case
        directory.mkdir()
        source = NATIVE / case / 'program.c'
        environment = {key:value for key,value in os.environ.items() if not key.startswith('GUARDCERT_')}
        environment.update(GUARDCERT_ORIGINAL_MODE='affine',GUARDCERT_ORIGINAL_OUTPUT=str(directory),
          GUARDCERT_PLUTO=str(ROOT / 'build/polyhedral-pipeline/pluto-source/tool/pluto'),GUARDCERT_SCOP_DIAGNOSTICS='1')
        command = [str(compiler),'-fall','-stdlib',str(compiler.parent / 'runtime'),'-S','-o',str(directory / 'program.s'),str(source)]
        result = subprocess.run(command,cwd=directory,env=environment,capture_output=True,text=True,timeout=180)
        (directory / 'stdout').write_text(result.stdout)
        (directory / 'stderr').write_text(result.stderr)
        row = {'case':case,'command':command,'returncode':result.returncode,
               'diagnostics':[line for line in result.stderr.splitlines() if line.startswith('GUARDCERT_')]}
        rows.append(row)
        print(json.dumps(row),flush=True)
    bindings = dict(build['bindings'])
    for path in [BUILD,Path(__file__),*[p for p in WORK.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status':'recorded' if all(row['returncode']==0 for row in rows) else 'rejected','cases':rows,'bindings':bindings}
    (WORK / 'report.json').write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':
    main()
