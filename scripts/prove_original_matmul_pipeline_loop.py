"""Connect the actual exported matmul region to the pipeline Loop instance."""

import argparse
import json
from pathlib import Path
import subprocess

import audit_original_matmul_nest as parent
import audit_original_matmul_typed as typed
import polcert_core
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/original-matmul/source-pipeline-loop-v1"
CODE = r'''From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryDoubleMatmul GuardMemoryDoubleMatmulInstr
  GuardMemoryDoubleMatmulLoops GuardMemoryDoubleNestControl GuardMemoryDoubleMatmulNest
  GuardMemoryDoubleMatmulPipelineLoop GuardMemoryDoublePolyhedral.
From GuardOriginalMatmul Require Import OriginalMatmul OriginalMatmulBody.
From GuardOriginalMatmulNest Require Import OriginalMatmulNest.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem original_full_nest_pipeline_model fe ge locals temps memory blocks layouts m_block n_block k_block
  rows columns depth after final body :
  original_selected_body=Some body ->
  double_matmul_static ge locals original_matmul_site blocks ->
  double_matmul_layout_certificate original_matmul_site layouts ->
  double_global_binding ge locals _M m_block -> double_global_binding ge locals _N n_block ->
  double_global_binding ge locals _K k_block ->
  Z.of_nat rows<=98 -> Z.of_nat columns<=98 -> Z.of_nat depth<=98 ->
  matmul_nest_invariant m_block n_block k_block rows columns depth temps memory ->
  (exec_stmt fe ge locals temps memory body E0 after final Out_normal <->
   DoubleAssignmentIRs.Loop.loop_semantics (double_matmul_pipeline_nest original_matmul_site)
     [Z.of_nat rows;Z.of_nat columns;Z.of_nat depth]
     (RuntimeState (global_double_locations ge layouts) memory)
     (RuntimeState (global_double_locations ge layouts) final) /\
   after=double_matmul_nest_exit original_matmul_site rows columns depth temps).
Proof.
  intros BODY STATIC LAYOUT MB NB KB MS NS KS INV.
  rewrite (@original_full_nest_typed_model fe ge locals temps memory blocks layouts m_block n_block k_block
    rows columns depth after final body BODY STATIC LAYOUT MB NB KB MS NS KS INV).
  rewrite double_pipeline_nest_correspondence; reflexivity.
Qed.
Print Assumptions original_full_nest_pipeline_model.
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    parent.validate()
    if (WORK / "report.json").exists():
        raise ValueError("Successful source-nest checkpoint is frozen")
    WORK.mkdir(exist_ok=True)
    source = WORK / "OriginalMatmulPipeline.v"
    if source.with_suffix(".vo").exists():
        raise ValueError("Successful proof object is frozen")
    source.write_text(CODE)
    archive = WORK / "attempts"
    archive.mkdir(exist_ok=True)
    with (archive / f"{args.attempt}.v").open("x") as snapshot:
        snapshot.write(CODE)
    polcert_core.select_profile("optimizer")
    flags = [*polcert_core.load_flags(), "-Q", str(ROOT / "adapters/compcert-memory"), "GuardMemory",
             "-R", str(ROOT / "vendor/CompCert/export"), "compcert.export",
             "-Q", str(typed.AST), "GuardOriginalMatmul", "-Q", str(parent.AST), "GuardOriginalMatmulNest",
             "-Q", str(WORK), "GuardOriginalMatmulPipeline"]
    argv = ["rocq", "compile", *flags, str(source)]
    with (archive / f"{args.attempt}.log").open("x") as log:
        run = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    if run.returncode:
        print((archive / f"{args.attempt}.log").read_text()[-5000:])
        raise SystemExit(run.returncode)
    bindings = dict(parent.validate()["bindings"])
    for path in [Path(__file__), parent.WORK / "report.json", *WORK.rglob("*")]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "compiled", "kind": "actual-original-matmul-three-loop-to-pipeline-Loop-instance",
              "actual_selected_region_exact": True, "pipeline_Loop_instance_correspondence": True, "complete_three_loop_source_correspondence": True,
              "execution_directions": "both finite directions under conditional entry premises",
              "nonnegative_signed_I64_bounds": True, "conditional_N_and_K_entry_read_premises": True,
              "final_memory_and_all_public_iterator_exits_exact": True,
              "outer_empty_retains_j_and_k": True, "middle_empty_retains_k": True,
              "installed_entry_premise_producer": False, "safe_guard_or_candidate_lowering_installed": False,
              "new_native_optimized_case": False, "command": argv, "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "compiled", "bound_files": len(bindings), "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
