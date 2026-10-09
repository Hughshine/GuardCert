"""Check the actual original matmul AST against the typed local body bridge."""

import argparse
import json
from pathlib import Path
import subprocess

import polcert_core
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

FRONT = ROOT / "build/original-matmul/frontend-v1"
WORK = ROOT / "build/original-matmul/source-ast-v2"


def main():
    global WORK
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, default=WORK)
    args = parser.parse_args()
    WORK = args.work.resolve()
    if not WORK.is_relative_to(ROOT / "build/original-matmul"):
        raise ValueError("Use a checkpoint under build/original-matmul")
    if WORK.exists():
        raise ValueError("Source-AST proof checkpoint already exists")
    frontend = json.loads((FRONT / "report.json").read_text())
    for path, digest in frontend["bindings"].items():
        if sha(permitted(ROOT / path)) != digest:
            raise ValueError(f"Changed frontend input: {path}")
    WORK.mkdir()
    raw = (FRONT / "OriginalMatmul.v").read_text()
    old = "From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs."
    new = ("From compcert.lib Require Import Coqlib Integers Floats.\n"
           "From compcert.common Require Import AST.\n"
           "From compcert.cfrontend Require Import Ctypes Cop Clight.\n"
           "From compcert.export Require Import Clightdefs.")
    if raw.count(old) != 1:
        raise ValueError("Unexpected exported import header")
    adapted = WORK / "OriginalMatmul.v"
    adapted.write_text(raw.replace(old, new, 1))
    polcert_core.select_profile("optimizer")
    flags = [*polcert_core.load_flags(), "-R", str(ROOT / "vendor/CompCert/export"), "compcert.export",
             "-Q", str(ROOT / "adapters/compcert-memory"), "GuardMemory",
             "-Q", str(WORK), "GuardOriginalMatmul"]
    commands = []
    for source, label in [(adapted, "original-ast")]:
        argv = ["rocq", "compile", *flags, str(source)]
        with (WORK / f"{label}.log").open("x") as log:
            run = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        if run.returncode:
            raise ValueError((WORK / f"{label}.log").read_text()[-3000:])
        commands.append(argv)
    code = r'''From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryDoubleValue GuardMemoryDoubleSource
  GuardMemoryDoubleLocations GuardMemoryDoubleAssignment GuardMemoryLongControl GuardMemoryDoubleMatmul.
From GuardOriginalMatmul Require Import OriginalMatmul.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition original_matmul_site := DoubleMatmulSite _A _B _C _alpha _beta _i _j _k__1 100 2.
Definition original_long_loop iterator bound body :=
  Ssequence (Sset iterator memory_long_zero)
    (Sloop (Ssequence (Sifthenelse
      (Ebinop Olt (Etempvar iterator memory_long_type) (Evar bound memory_long_type) memory_signed_int_type)
      Sskip Sbreak) body)
      (Sset iterator (memory_long_plus_int (Etempvar iterator memory_long_type) 1))).
Definition original_matmul_region :=
  original_long_loop _i _M (original_long_loop _j _N
    (original_long_loop _k__1 _K (double_matmul_body original_matmul_site))).
Definition original_selected_body :=
  match fn_body f_main with
  | Ssequence (Ssequence _ (Ssequence (Slabel label region) _)) _ =>
      if Pos.eqb label ___guardcert_scop_1 then Some region else None
  | _ => None end.
Definition original_selected_assignment :=
  match original_selected_body with
  | Some (Ssequence _ (Sloop (Ssequence _
      (Ssequence _ (Sloop (Ssequence _
        (Ssequence _ (Sloop (Ssequence _ body) _))) _))) _)) => Some body
  | _ => None end.

Theorem original_selected_region_exact : original_selected_body = Some original_matmul_region.
Proof. reflexivity. Qed.
Theorem original_selected_assignment_exact :
  original_selected_assignment = Some (double_matmul_body original_matmul_site).
Proof. reflexivity. Qed.
Theorem original_selected_rhs_decodes :
  decode_double_expression (double_source_reads (double_matmul_rhs original_matmul_site))
    (double_matmul_rhs original_matmul_site) = Some double_matmul_expression.
Proof. vm_compute; reflexivity. Qed.
Theorem original_public_iterator_types : fn_temps f_main =
  [(_i,memory_long_type);(_j,memory_long_type);(_k__1,memory_long_type)].
Proof. reflexivity. Qed.

Theorem original_assignment_source_decode fe ge locals temps memory blocks i j k trace final_temps final outcome body :
  original_selected_assignment = Some body ->
  double_matmul_entry ge locals temps original_matmul_site blocks i j k ->
  exec_stmt fe ge locals temps memory body trace final_temps final outcome ->
  trace=E0 /\ final_temps=temps /\ outcome=Out_normal /\
  memory_action_run (MemoryAction (double_matmul_locations original_matmul_site blocks i j k)
    (double_matmul_location original_matmul_site (matmul_C_block blocks) i j)
    (fun values => compute_double_assignment values double_matmul_expression)) memory final.
Proof.
  intros BODY ENTRY RUN; rewrite original_selected_assignment_exact in BODY; inversion BODY; subst body.
  eapply double_matmul_source_decode; eauto.
Qed.
Theorem original_assignment_lowered_execution fe ge locals temps memory blocks i j k final body :
  original_selected_assignment = Some body ->
  double_matmul_entry ge locals temps original_matmul_site blocks i j k ->
  memory_action_run (MemoryAction (double_matmul_locations original_matmul_site blocks i j k)
    (double_matmul_location original_matmul_site (matmul_C_block blocks) i j)
    (fun values => compute_double_assignment values double_matmul_expression)) memory final ->
  exec_stmt fe ge locals temps memory body E0 temps final Out_normal.
Proof.
  intros BODY ENTRY RUN; rewrite original_selected_assignment_exact in BODY; inversion BODY; subst body.
  eapply double_matmul_lowered_execution; eauto.
Qed.
Print Assumptions original_selected_region_exact.
Print Assumptions original_selected_assignment_exact.
Print Assumptions original_selected_rhs_decodes.
Print Assumptions original_public_iterator_types.
Print Assumptions original_assignment_source_decode.
Print Assumptions original_assignment_lowered_execution.
'''
    proof = WORK / "OriginalMatmulBody.v"
    proof.write_text(code)
    argv = ["rocq", "compile", *flags, str(proof)]
    with (WORK / "body-proof.log").open("x") as log:
        run = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    if run.returncode:
        raise ValueError((WORK / "body-proof.log").read_text()[-3500:])
    commands.append(argv)
    bindings = {str(path.relative_to(ROOT)): sha(path) for path in
                [Path(__file__), FRONT / "report.json", FRONT / "OriginalMatmul.v",
                 ROOT / "scripts/polcert_core.py", *WORK.iterdir()] if path.is_file()}
    report = {"status": "compiled", "kind": "actual-original-matmul-Clight-body",
              "original_selected_region_and_assignment_exact": True,
              "original_numeric_types_and_operation_tree_retained": True,
              "AST_source_adaptation": "import namespaces only; all program definitions unchanged",
              "original_rhs_decoder_executed_in_Rocq": True,
              "local_source_and_lowered_proof_connected": True,
              "loop_context_produces_local_entry_premises": False,
              "optimization_installed": False, "new_native_optimized_case": False,
              "commands": commands, "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items() if key not in ["bindings", "commands"]}))


if __name__ == "__main__":
    main()
