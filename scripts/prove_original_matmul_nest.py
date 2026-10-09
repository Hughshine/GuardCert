"""Connect the actual exported three-loop matmul region to typed PolCert."""

import argparse
import json
from pathlib import Path
import subprocess

import audit_original_matmul_loops as parent
import audit_original_matmul_typed as typed
import polcert_core
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/original-matmul/source-nest-v1"
CODE = r'''From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Integers Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryDoubleMatmul
  GuardMemoryDoubleMatmulInstr GuardMemoryDoubleMatmulLoops GuardMemoryDoubleNestControl
  GuardMemoryDoubleMatmulNest GuardMemoryDoubleMatmulNestModel.
From GuardOriginalMatmul Require Import OriginalMatmul OriginalMatmulBody.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem original_selected_nest_exact : original_selected_body=
  Some (double_matmul_source_nest original_matmul_site _M _N _K).
Proof. reflexivity. Qed.

Theorem original_full_nest_typed_model fe ge locals temps memory blocks layouts m_block n_block k_block
  rows columns depth after final body :
  original_selected_body=Some body ->
  double_matmul_static ge locals original_matmul_site blocks ->
  double_matmul_layout_certificate original_matmul_site layouts ->
  double_global_binding ge locals _M m_block -> double_global_binding ge locals _N n_block ->
  double_global_binding ge locals _K k_block ->
  Z.of_nat rows<=98 -> Z.of_nat columns<=98 -> Z.of_nat depth<=98 ->
  matmul_nest_invariant m_block n_block k_block rows columns depth temps memory ->
  (exec_stmt fe ge locals temps memory body E0 after final Out_normal <->
   DoubleAssignmentLoop.loop_semantics (double_matmul_nest_model original_matmul_site)
     [Z.of_nat rows;Z.of_nat columns;Z.of_nat depth]
     (RuntimeState (global_double_locations ge layouts) memory)
     (RuntimeState (global_double_locations ge layouts) final) /\
   after=double_matmul_nest_exit original_matmul_site rows columns depth temps).
Proof.
  intros BODY STATIC LAYOUT MB NB KB MS NS KS INV.
  rewrite original_selected_nest_exact in BODY; inversion BODY; subst body.
  eapply double_matmul_original_nest_Loop.
  - exact STATIC.
  - exact LAYOUT.
  - exact MB.
  - exact NB.
  - exact KB.
  - vm_compute; discriminate.
  - vm_compute; discriminate.
  - vm_compute; discriminate.
  - vm_compute; discriminate.
  - vm_compute; discriminate.
  - vm_compute; discriminate.
  - cbn; lia.
  - cbn; lia.
  - cbn; lia.
  - cbn; lia.
  - change (Z.of_nat rows<=9223372036854775807); lia.
  - change (Z.of_nat columns<=9223372036854775807); lia.
  - change (Z.of_nat depth<=9223372036854775807); lia.
  - exact INV.
Qed.

Theorem original_outer_empty_exit columns depth temps :
  double_matmul_nest_exit original_matmul_site 0 columns depth temps=PTree.set _i (Vlong Int64.zero) temps.
Proof. reflexivity. Qed.
Theorem original_middle_empty_exit rows depth temps :
  double_matmul_nest_exit original_matmul_site (S rows) 0 depth temps=
  PTree.set _i (Vlong (Int64.repr (Z.of_nat (S rows)))) (PTree.set _j (Vlong Int64.zero) temps).
Proof. reflexivity. Qed.

Print Assumptions original_selected_nest_exact.
Print Assumptions original_full_nest_typed_model.
Print Assumptions original_outer_empty_exit.
Print Assumptions original_middle_empty_exit.
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
    source = WORK / "OriginalMatmulNest.v"
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
             "-Q", str(typed.AST), "GuardOriginalMatmul", "-Q", str(WORK), "GuardOriginalMatmulNest"]
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
    report = {"status": "compiled", "kind": "actual-original-matmul-three-loop-region-to-typed-PolCert",
              "actual_selected_region_exact": True, "complete_three_loop_source_correspondence": True,
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
