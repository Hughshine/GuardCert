"""Probe actual source extraction and OpenScop export for unchanged whole-tree fixtures."""
import argparse
import ast
import json
import re
import subprocess
from pathlib import Path

import check_double_tree_model as fixtures
import compile_matmul_installation as compiler
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

CODE = r'''From Stdlib Require Import List Bool ZArith.
From polcert.polygen Require Import Result.
From GuardMemory Require Import GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeDecode
  GuardMemoryDoubleSourceTreeProgress GuardMemoryDoubleTreeGuarded GuardMemoryDoubleTreeEntry
  GuardMemoryDoubleTreeFootprint GuardMemoryDoublePolyhedral GuardMemoryDoubleUniformPrepared.
From GuardTreeFixtures Require Import Original Probe.
Import ListNotations.
Definition request_summary source : list nat := match checked_double_source_tree prog source with
  | None=>[0]
  | Some tree=>
    [if double_tree_profile_check tree (fun _=>0%Z) (fun _=>4096%Z) then 1 else 0;
     if double_tree_footprint_check tree (fun _=>4096%Z) [] then 1 else 0;
     if double_tree_layout_span_check tree then 1 else 0;
     if double_source_tree_active_root tree then 1 else 0]++
    match DoubleAssignmentExtractor.extractor (double_tree_pipeline_request tree) with
    | Err _=>[0;0]
    | Okk model=>[1;match export_double_uniform_model model with Some _=>1 | None=>0 end] end
  end.
Goal True. idtac "TREE_PIPELINE_REQUEST_STATS". exact I. Qed.
Eval vm_compute in map request_summary selected_regions.
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--attempt', required=True)
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+', args.attempt):
        raise ValueError('Use a fresh simple attempt')
    source_report = json.loads(permitted(fixtures.SOURCE / 'report.json').read_text())
    bindings = dict(source_report['bindings'])
    for path, digest in bindings.items():
        if sha(permitted(ROOT / path)) != digest:
            raise ValueError('Changed original fixture: ' + path)
    work = permitted(ROOT / 'build/double-tree-model/pipeline-attempts' / args.attempt)
    work.mkdir(parents=True, exist_ok=False)
    (work / 'check-script.py').write_bytes(permitted(Path(__file__)).read_bytes())
    cases = []
    for name in fixtures.CASES:
        case = work / name
        case.mkdir()
        source = case / 'Request.v'
        source.write_text(CODE)
        argv = ['rocq', 'compile', *compiler.lowering.flags(), '-Q', str(fixtures.SOURCE / name),
                'GuardTreeFixtures', str(source)]
        with (case / 'proof.log').open('x') as log:
            result = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        log = permitted(case / 'proof.log').read_text()
        rows = None
        if result.returncode == 0:
            found = re.search(r'=\s*(\[.*?\])\s*:\s*list', log, re.S)
            if not found:
                raise ValueError('Missing computed request summary: ' + name)
            rows = ast.literal_eval(found.group(1).replace(';', ','))
            if any(len(row) != 6 for row in rows):
                raise ValueError('Unexpected request summary: ' + name)
        cases.append({'case': name, 'returncode': result.returncode, 'summaries': rows,
                      'columns': ['profile', 'footprint', 'layout_span', 'progress_root', 'Loop_extract', 'OpenScop_export'],
                      'profile': [0, 4096], 'command': argv})
        for path in case.iterdir():
            if path.is_file():
                bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    for path in [Path(__file__), Path(fixtures.__file__), work / 'check-script.py', fixtures.SOURCE / 'report.json']:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status': 'checked' if all(case['returncode'] == 0 for case in cases) else 'incomplete',
              'cases': cases, 'bindings': bindings, 'actual_pure_extractor_and_exporter_invoked': True,
              'external_phase_or_candidate_codegen_run': False, 'new_native_optimization_added': False,
              'full_goal_complete': False}
    (work / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'status': report['status'], 'cases': [{key: value for key, value in case.items() if key != 'command'}
                      for case in cases], 'report': str((work / 'report.json').relative_to(ROOT))}))
    if report['status'] != 'checked':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
