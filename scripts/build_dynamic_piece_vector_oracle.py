"""Relink the same proved root with a fresh untrusted certificate search.

The backend parameter keeps its existing extraction binding and LCF checks.
All proof-extracted implementations and Driver are copied byte for byte; only
its native search implementation changes. No semantic function is replaced.
"""
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess

from audit_interface_clight import ROOT,sha
from audit_word_store_sequence import permitted
from probe_piece_models import checked

PARENT=ROOT/'build/double-tree-model/compiler-attempts/native-dynamic-piece-integer-v6/report.json'
NATIVE=ROOT/'adapters/compcert-memory/native'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--attempt',required=True)
    args=parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+',args.attempt):
        raise ValueError('Require a fresh simple attempt')
    bindings={}
    parent=checked(PARENT,bindings)
    if parent['status']!='built':
        raise ValueError('Require the current checked compiler')
    previous=PARENT.parent
    work=previous.parent/args.attempt
    if work.exists():
        raise ValueError('Attempt already exists')
    excluded={'report.json','build.log','snapshots','successor-snapshots'}
    shutil.copytree(previous,work,ignore=lambda directory,names:
        list(excluded & set(names)) if Path(directory)==previous else [])
    snapshots=work/'vector-snapshots'
    snapshots.mkdir()
    sources=[permitted(NATIVE/name) for name in ['GuardMemoryVectorOracle.ml','GuardMemoryVectorTimedOracle.ml']]
    shutil.copy2(PARENT,snapshots/'parent-report.json')
    shutil.copy2(Path(__file__),snapshots/'script.py')
    for source in sources:
        shutil.copy2(source,snapshots/source.name)
    shutil.copy2(sources[0],work/'extraction'/sources[0].name)
    for directory in ['extraction','inputs']:
        shutil.copy2(sources[1],work/directory/'GuardMemoryTimedOracle.ml')
    existing=list((previous/'extraction').glob('*.ml'))+list((previous/'extraction').glob('*.mli'))
    differences=[str(path.relative_to(previous)) for path in existing
        if sha(path)!=sha(permitted(work/path.relative_to(previous)))]
    if differences!=['extraction/GuardMemoryTimedOracle.ml']:
        raise ValueError('Only the existing untrusted backend search may differ: '+str(differences))
    if sha(work/'driver/Driver.ml')!=sha(previous/'driver/Driver.ml'):
        raise ValueError('Driver must be unchanged')
    if sha(work/'ExtractSelectedDouble.v')!=sha(previous/'ExtractSelectedDouble.v'):
        raise ValueError('Existing extraction directives must be unchanged')
    commands=[]
    with (work/'build.log').open('xb') as output:
        for argv in [['make','-f','Makefile.extr','depend'],['make','-j4','-f','Makefile.extr','ccomp']]:
            proc=subprocess.run(argv,cwd=work,stdout=output,stderr=subprocess.STDOUT)
            commands.append({'argv':argv,'returncode':proc.returncode})
            if proc.returncode:
                break
    for path in [Path(__file__),*sources,*[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))]=sha(permitted(path))
    report={key:value for key,value in parent.items() if key not in ['bindings','commands','compiler','compiler_sha256']}
    report.update(status='built' if proc.returncode==0 else 'rejected',
        compiler=str((work/'ccomp').relative_to(ROOT)),compiler_sha256=sha(work/'ccomp') if proc.returncode==0 else None,
        commands=commands,parent_report=str(PARENT.relative_to(ROOT)),
        Driver_unchanged=True,existing_extraction_directives_unchanged=True,
        semantic_extraction_reused_byte_for_byte=True,
        native_parameter_realization_changed=['PedraQBackend.isEmpty search implementation'],
        LCF_checks_and_all_proof_extracted_functions_unchanged=True,
        untrusted_Farkas_provenance_flattened_and_rebuilt_by_LCF=True,
        bindings=bindings)
    filename='report.json' if proc.returncode==0 else 'rejection.json'
    (work/filename).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'compiler':report['compiler'],'bindings':len(bindings)}),flush=True)
    if proc.returncode:
        raise SystemExit(proc.returncode)


if __name__=='__main__':
    main()
