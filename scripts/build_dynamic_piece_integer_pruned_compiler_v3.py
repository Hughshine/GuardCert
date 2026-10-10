"""Link a fresh data-only proposer against the byte-checked extracted compiler.

All extracted semantic ML sources are copied unchanged. The Driver changes only
the two untrusted proposer arguments to the same universally proved root.
"""
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_piece_models import checked

PARENT = ROOT/'build/double-tree-model/compiler-attempts/native-dynamic-piece-integer-v2/report.json'
MODULE = 'GuardSelectedDoublePieceIntegerCoverageV9'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--attempt',required=True)
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+',args.attempt):
        raise ValueError('Use a fresh simple attempt')
    bindings = {}
    parent = checked(PARENT,bindings)
    if parent['status']!='built' or not parent['integer_coverage_splits_are_untrusted_data_consumed_by_existing_checker']:
        raise ValueError('Require the proved and extracted current compiler')
    previous = PARENT.parent
    work = previous.parent/args.attempt
    if work.exists():
        raise ValueError('Attempt already exists')
    excluded = {'report.json','build.log','snapshots'}
    shutil.copytree(previous,work,ignore=lambda directory,names:
        list(excluded & set(names)) if Path(directory)==previous else [])
    snapshots = work/'successor-snapshots'
    snapshots.mkdir()
    shutil.copy2(PARENT,snapshots/'parent-report.json')
    shutil.copy2(Path(__file__),snapshots/'script.py')
    native = permitted(ROOT/'adapters/compcert-memory/native'/(MODULE+'.ml'))
    shutil.copy2(native,work/'extraction'/native.name)
    shutil.copy2(native,snapshots/native.name)
    dependency = permitted(ROOT/'adapters/compcert-memory/native/GuardSelectedDoublePieceIntegerCoverageV5.ml')
    shutil.copy2(dependency,work/'extraction'/dependency.name)
    shutil.copy2(dependency,snapshots/dependency.name)
    driver = work/'driver/Driver.ml'
    old = permitted(previous/'driver/Driver.ml').read_text()
    if old.count('GuardSelectedDoublePieceIntegerCoverageV2.')!=2:
        raise ValueError('Require exactly two untrusted policy arguments in Driver')
    new = old.replace('GuardSelectedDoublePieceIntegerCoverageV2.',MODULE+'.')
    driver.write_text(new)
    semantic_files = list((previous/'extraction').glob('*.ml'))+list((previous/'extraction').glob('*.mli'))
    if any(sha(permitted(path))!=sha(permitted(work/path.relative_to(previous))) for path in semantic_files):
        raise ValueError('An existing extracted semantic source changed')
    commands=[]
    with (work/'build.log').open('xb') as output:
        for argv in [['make','-f','Makefile.extr','depend'],['make','-j4','-f','Makefile.extr','ccomp']]:
            proc = subprocess.run(argv,cwd=work,stdout=output,stderr=subprocess.STDOUT)
            commands.append({'argv':argv,'returncode':proc.returncode})
            if proc.returncode:
                break
    for path in [Path(__file__),native,dependency,*[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {key:value for key,value in parent.items() if key not in ['bindings','commands','compiler','compiler_sha256']}
    report.update(status='built' if proc.returncode==0 else 'rejected',
                  compiler=str((work/'ccomp').relative_to(ROOT)),
                  compiler_sha256=sha(work/'ccomp') if proc.returncode==0 else None,
                  commands=commands,
                  parent_report=str(PARENT.relative_to(ROOT)),
                  semantic_extraction_reused_byte_for_byte=True,
                  Driver_changes_only_untrusted_arguments_to_same_proved_root=True,
                  integer_cuts_use_equality_reduction_and_positive_constraint_combinations=True,
                  bindings=bindings)
    filename = 'report.json' if proc.returncode==0 else 'rejection.json'
    (work/filename).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'compiler':report['compiler'],'bindings':len(bindings)}),flush=True)
    if proc.returncode:
        raise SystemExit(proc.returncode)


if __name__=='__main__':
    main()
