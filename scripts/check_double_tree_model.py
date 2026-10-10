"""Close whole-tree dynamic model premises on unchanged original Clight fixtures."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess

import audit_double_tree_capture as parent
import compile_matmul_installation as compiler
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

SOURCE = ROOT / "build/double-source-tree/source-attempts/source-v2"
CASES = ["fusion1", "multi-stmt-stencil-seq", "tricky3"]
CODE = r'''From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightRegionProgress ClightTempFrame ClightTempFootprint ClightGlobalScope.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryDoubleSourceLoopModel
  GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeDecode GuardMemoryDoubleSourceTreeState
  GuardMemoryDoubleSourceTreeModelData GuardMemoryDoubleSourceTreeExit GuardMemoryDoubleTreeCaptureData
  GuardMemoryDoubleTreeCaptureReceipt GuardMemoryDoubleTreeCapturePrepared GuardMemoryDoubleTreeCacheFrame GuardMemoryDoubleTreeCacheParameters
  GuardMemoryDoubleTreeCacheEnvironment GuardMemoryDoubleTreeFootprint GuardMemoryDoubleTreePreparedModel.
From GuardTreeFixtures Require Import Original Probe.
Import ListNotations.
Local Open Scope Z_scope.

Theorem original_marked_tree_footprints : forallb
  (fun source=>match checked_double_source_tree prog source with
    | Some tree=>double_tree_footprint_check tree (fun _=>16) [] | None=>false end) selected_regions=true.
Proof. vm_compute; reflexivity. Qed.
Theorem original_whole_tree_prepared_model source : In source selected_regions ->
  exists tree, checked_double_source_tree prog source=Some tree /\
  forall fe ge locals temps memory after final live cache flag,
  preserving_globals (globalenv prog) ge -> double_source_tree_scope tree locals ->
  locals_avoid (double_source_tree_headers tree) locals ->
  double_tree_cache_distinct (double_source_tree_headers tree) cache ->
  (forall header, In header (double_source_tree_headers tree) -> cache header<>flag) ->
  (forall key, In key (statement_temps source++live) -> ~ In key (double_tree_capture_private tree cache flag)) ->
  exec_stmt fe ge locals temps memory source Events.E0 after final Out_normal ->
  exists prepared accepted prepared_after,
    exec_stmt fe ge locals temps memory (double_tree_capture_prepare tree cache flag (fun _=>0) (fun _=>16))
      Events.E0 prepared memory Out_normal /\
    double_tree_flag_value prepared flag accepted /\ temp_agree live temps prepared /\
    double_tree_cache_environment (double_source_tree_parameters tree) cache (fun _=>0) (fun _=>16) prepared /\
    exec_stmt fe ge locals prepared memory source Events.E0 prepared_after final Out_normal /\ temp_agree live after prepared_after /\
    (accepted=true ->
      SL.loop_semantics (double_source_tree_model (double_source_tree_parameters tree) O tree)
        (double_tree_cached_parameters tree cache prepared)
        (RuntimeState (global_double_locations ge (double_source_tree_layouts tree)) memory)
        (RuntimeState (global_double_locations ge (double_source_tree_layouts tree)) final) /\
      prepared_after=double_source_tree_exit (double_tree_cached_value cache prepared) tree prepared).
Proof.
  intro MEMBER; pose proof original_marked_tree_footprints as CHECKED.
  apply forallb_forall with (x:=source) in CHECKED; [|exact MEMBER].
  destruct (checked_double_source_tree prog source) as [tree|] eqn:CHECK; [|discriminate].
  exists tree; split; [reflexivity|].
  intros; eapply checked_double_tree_prepared_model; try eassumption.
  intros header HEADER; cbn; unfold Int.min_signed,Int.max_signed; vm_compute; repeat split; discriminate.
Qed.
Goal True. idtac "TREE_MODEL_ASSUMPTIONS". exact I. Qed.
Print Assumptions original_marked_tree_footprints.
Print Assumptions original_whole_tree_prepared_model.
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not re.fullmatch(r"[a-z0-9-]+", args.attempt):
        raise ValueError("Use a simple attempt name")
    baseline = parent.validate()
    source_report = json.loads(permitted(SOURCE / "report.json").read_text())
    allowed = set(baseline["allowed_parent_globals"])
    for path, digest in source_report["bindings"].items():
        if sha(permitted(ROOT / path)) != digest:
            raise ValueError("Changed original source fixture: " + path)
    work = permitted(ROOT / "build/double-tree-model/source-attempts" / args.attempt)
    work.mkdir(parents=True, exist_ok=False)
    (work / "check-script.py").write_bytes(permitted(Path(__file__)).read_bytes())
    bindings = {str((SOURCE / "report.json").relative_to(ROOT)): sha(SOURCE / "report.json"),
                str((parent.WORK / "report.json").relative_to(ROOT)): sha(parent.WORK / "report.json"),
                str(Path(__file__).relative_to(ROOT)): sha(permitted(Path(__file__))),
                str((work / "check-script.py").relative_to(ROOT)): sha(work / "check-script.py")}
    bindings.update(source_report["bindings"])
    env = {key: value for key, value in os.environ.items() if not key.startswith("GUARDCERT_")}
    cases = []
    for name in CASES:
        case = work / name
        case.mkdir()
        proof = case / "Model.v"
        proof.write_text(CODE)
        argv = ["rocq", "compile", *compiler.lowering.flags(), "-Q", str(SOURCE / name),
                "GuardTreeFixtures", str(proof)]
        with (case / "proof.log").open("x") as log:
            run = subprocess.run(argv, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        output = permitted(case / "proof.log").read_text()
        actual = sorted(names(output.split("TREE_MODEL_ASSUMPTIONS\n", 1)[-1])) if run.returncode == 0 else []
        extra = sorted(set(actual) - allowed)
        if extra:
            raise ValueError("New original-instance globals: " + str(extra))
        original = next(item for item in source_report["cases"] if item["case"] == name)
        cases.append({"case": name, "stage": "footprint-and-prepared-model-proved" if run.returncode == 0 else "proof-refused",
                      "command": argv, "returncode": run.returncode, "assumptions": actual,
                      "source_tree_summaries": original["source_tree_summaries"], "profile": [0, 16]})
        for path in case.iterdir():
            if path.is_file():
                bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "checked" if all(item["returncode"] == 0 for item in cases) else "incomplete",
              "cases": cases, "bindings": bindings,
              "original_Clight_and_numeric_computation_reused_unchanged": True,
              "nonempty_footprint_envelopes_checked": True,
              "whole_source_tree_prepared_model_instantiated": True,
              "leaf_resolution_and_cached_parameter_obligations_closed": True,
              "guard_factory_instantiated": False, "path_sensitive_capture_installed": False,
              "candidate_or_native_optimization_added": False, "full_goal_complete": False}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "cases": [{key: value for key, value in item.items() if key != "command"}
                      for item in cases], "report": str((work / "report.json").relative_to(ROOT))}))
    if report["status"] != "checked":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
