"""Prove that the original selected matmul supplies an exportable double pipeline input."""

import argparse
import json
from pathlib import Path
import subprocess

import audit_original_matmul_pipeline_loop as parent
import polcert_core
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/original-matmul/source-prepared-v1"
CODE = r'''From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.polygen Require Import Result.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryDoubleMatmul
  GuardMemoryDoubleMatmulInstr GuardMemoryDoubleMatmulLoops GuardMemoryDoubleNestControl
  GuardMemoryDoubleMatmulNest GuardMemoryDoubleMatmulPipelineLoop GuardMemoryDoublePolyhedral
  GuardMemoryDoublePrepared.
From GuardOriginalMatmul Require Import OriginalMatmul OriginalMatmulBody.
From GuardOriginalMatmulPipeline Require Import OriginalMatmulPipeline.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Loop execution uses [M;N;K]; the named parameter context uses its reverse. *)
Definition original_matmul_pipeline_request : DoubleAssignmentIRs.Loop.t :=
  (double_matmul_pipeline_nest original_matmul_site, [_K;_N;_M],
    map (fun id => (id,tt)) [_K;_N;_M;_A;_B;_C;_alpha;_beta]).

Theorem original_matmul_request_exportable : exists model exported,
  DoubleAssignmentExtractor.extractor original_matmul_pipeline_request = Okk model /\
  export_double_model model = Some exported.
Proof. vm_compute; eexists; eexists; split; reflexivity. Qed.

Theorem original_matmul_request_source_execution fe ge locals temps memory blocks layouts m_block n_block k_block
  rows columns depth after final body :
  original_selected_body=Some body ->
  double_matmul_static ge locals original_matmul_site blocks ->
  double_matmul_layout_certificate original_matmul_site layouts ->
  double_global_binding ge locals _M m_block -> double_global_binding ge locals _N n_block ->
  double_global_binding ge locals _K k_block ->
  Z.of_nat rows<=98 -> Z.of_nat columns<=98 -> Z.of_nat depth<=98 ->
  matmul_nest_invariant m_block n_block k_block rows columns depth temps memory ->
  exec_stmt fe ge locals temps memory body E0 after final Out_normal ->
  DoubleAssignmentIRs.Loop.semantics original_matmul_pipeline_request
    (RuntimeState (global_double_locations ge layouts) memory)
    (RuntimeState (global_double_locations ge layouts) final) /\
  after=double_matmul_nest_exit original_matmul_site rows columns depth temps.
Proof.
  intros BODY STATIC LAYOUT MB NB KB MS NS KS INV RUN.
  destruct (proj1 (@original_full_nest_pipeline_model fe ge locals temps memory blocks layouts
    m_block n_block k_block rows columns depth after final body BODY STATIC LAYOUT MB NB KB MS NS KS INV) RUN)
    as [MODEL EXIT]; split; [|exact EXIT].
  eapply DoubleAssignmentIRs.Loop.LSemaIntro with (env:=[Z.of_nat rows;Z.of_nat columns;Z.of_nat depth]).
  - reflexivity.
  - exact I.
  - apply global_double_locations_nonalias.
  - reflexivity.
  - exact MODEL.
Qed.

Print Assumptions original_matmul_request_exportable.
Print Assumptions original_matmul_request_source_execution.
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    baseline = parent.validate()
    if (WORK / "report.json").exists():
        raise ValueError("Successful source checkpoint is frozen")
    WORK.mkdir(exist_ok=True)
    source = WORK / "OriginalMatmulPrepared.v"
    if source.with_suffix(".vo").exists():
        raise ValueError("Successful proof object is frozen")
    source.write_text(CODE)
    archive = WORK / "attempts"
    archive.mkdir(exist_ok=True)
    with (archive / f"{args.attempt}.v").open("x") as snapshot:
        snapshot.write(CODE)
    polcert_core.select_profile("optimizer")
    flags = [*polcert_core.load_flags(), "-Q", str(ROOT / "adapters/compcert-memory"), "GuardMemory",
             "-Q", str(ROOT / "prototype/interface"), "GuardInterface",
             "-R", str(ROOT / "vendor/CompCert/export"), "compcert.export",
             "-Q", str(parent.typed.AST), "GuardOriginalMatmul",
             "-Q", str(parent.parent.AST), "GuardOriginalMatmulNest",
             "-Q", str(parent.AST), "GuardOriginalMatmulPipeline",
             "-Q", str(WORK), "GuardOriginalMatmulPrepared"]
    argv = ["rocq", "compile", *flags, str(source)]
    with (archive / f"{args.attempt}.log").open("x") as log:
        run = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    if run.returncode:
        print((archive / f"{args.attempt}.log").read_text()[-5000:])
        raise SystemExit(run.returncode)
    bindings = dict(baseline["bindings"])
    for path in [Path(__file__), parent.WORK / "report.json",
                 ROOT / "adapters/compcert-memory/GuardMemoryDoublePrepared.v",
                 ROOT / "adapters/compcert-memory/GuardMemoryDoublePrepared.vo", *WORK.rglob("*")]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "compiled", "kind": "actual-original-matmul-exportable-double-pipeline-input",
              "actual_selected_source_execution_to_pipeline_input": True,
              "pipeline_parameter_context": "K,N,M; Loop environment M,N,K",
              "extractor_and_OpenScop_export_success_proved": True,
              "entry_header_definedness_and_ranges_still_logical_premises": True,
              "source_user_entry_premises_automatically_produced": False,
              "selected_compiler_connected": False, "new_native_optimized_case": False,
              "command": argv, "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "compiled", "bound_files": len(bindings), "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
