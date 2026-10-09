"""Connect the actual exported matmul inner loop to typed PolCert execution."""

import argparse
import json
from pathlib import Path
import subprocess

import audit_original_matmul_typed as parent
import polcert_core
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/original-matmul/source-loop-v1"

CODE = r'''From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Integers Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryDoubleMatmul
  GuardMemoryDoubleMatmulInstr GuardMemoryDoubleMatmulLoops GuardMemoryDoubleMatmulLoopModel.
From GuardOriginalMatmul Require Import OriginalMatmul OriginalMatmulBody.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition original_selected_inner_loop :=
  match original_selected_body with
  | Some (Ssequence _ (Sloop (Ssequence _
      (Ssequence _ (Sloop (Ssequence _ inner) _))) _)) => Some inner
  | _ => None end.

Theorem original_selected_inner_loop_exact : original_selected_inner_loop=
  Some (double_matmul_inner_source original_matmul_site _K).
Proof. reflexivity. Qed.

Theorem original_inner_loop_typed_model fe ge locals temps memory blocks layouts bound_block
  i j m n count upper after final body :
  original_selected_inner_loop=Some body ->
  double_matmul_static ge locals original_matmul_site blocks ->
  double_matmul_layout_certificate original_matmul_site layouts ->
  double_global_binding ge locals _K bound_block ->
  0<=i+2<100 -> 0<=j+2<100 -> 0<=upper<=98 -> upper<=Int64.max_signed -> upper=Z.of_nat count ->
  temps ! _i=Some (Vlong (Int64.repr i)) -> temps ! _j=Some (Vlong (Int64.repr j)) ->
  Mem.load Mint64 memory bound_block 0=Some (Vlong (Int64.repr upper)) ->
  (exec_stmt fe ge locals temps memory body E0 after final Out_normal <->
   DoubleAssignmentLoop.loop_semantics (double_matmul_inner_model original_matmul_site) [j;i;m;n;upper]
     (RuntimeState (global_double_locations ge layouts) memory)
     (RuntimeState (global_double_locations ge layouts) final) /\
   after=PTree.set _k__1 (Vlong (Int64.repr upper)) temps).
Proof.
  intros BODY STATIC LAYOUT BOUND I J K RANGE LENGTH IV JV LOAD.
  rewrite original_selected_inner_loop_exact in BODY; inversion BODY; subst body.
  eapply double_matmul_original_inner_Loop.
  - exact STATIC.
  - exact LAYOUT.
  - exact BOUND.
  - vm_compute; discriminate.
  - vm_compute; discriminate.
  - vm_compute; discriminate.
  - exact I.
  - exact J.
  - cbn; lia.
  - lia.
  - exact LENGTH.
  - exact IV.
  - exact JV.
  - exact LOAD.
Qed.

Print Assumptions original_selected_inner_loop_exact.
Print Assumptions original_inner_loop_typed_model.
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    parent.validate()
    if (WORK / "report.json").exists():
        raise ValueError("Successful source-loop checkpoint is frozen")
    WORK.mkdir(exist_ok=True)
    source = WORK / "OriginalMatmulInnerLoop.v"
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
             "-Q", str(parent.AST), "GuardOriginalMatmul",
             "-Q", str(WORK), "GuardOriginalMatmulLoops"]
    argv = ["rocq", "compile", *flags, str(source)]
    with (archive / f"{args.attempt}.log").open("x") as log:
        run = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    if run.returncode:
        print((archive / f"{args.attempt}.log").read_text()[-4000:])
        raise SystemExit(run.returncode)
    bindings = dict(parent.validate()["bindings"])
    for path in [Path(__file__), parent.WORK / "report.json", *WORK.rglob("*")]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "compiled", "kind": "actual-original-matmul-inner-loop-to-typed-PolCert",
              "actual_AST_inner_loop_exact": True, "execution_bridge": "both finite directions",
              "final_memory_and_exact_public_k_exit": True, "original_expression_tree_retained": True,
              "bound_stability_from_global_block_separation": True,
              "input_premises_automatically_produced_by_installed_factory": False,
              "full_three_loop_nest": False, "new_native_optimized_case": False,
              "command": argv, "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "compiled", "bound_files": len(bindings),
                      "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
