"""Bind the assignment factory to both original exported initialization kernels."""

import argparse
import json
from pathlib import Path
import subprocess

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
import prove_original_matmul_double_lowering as lowering

SOURCE = ROOT / "build/double-source-initialization/source-attempts/v1"
WORK = ROOT / "build/double-source-initialization/source-proof-v1"
CODE = r'''
From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers Floats.
From compcert.common Require Import Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryDoubleValue GuardMemoryDoubleSource
  GuardMemoryDoubleAssignment GuardMemoryDoubleAssignmentLiteral GuardMemoryDoubleAssignmentFactory.
From GuardDoubleInitMxv Require Import MxvSource.
From GuardDoubleInitMatmul Require Import MatmulInitSource.
Import ListNotations.
Set Implicit Arguments.

(** Inspection of these two exported inputs, not a general region recognizer.
    Administrative skips elided by the exporter do not alter assignment nodes. *)
Definition selected_region body :=
  match body with
  | Ssequence (Ssequence _ (Ssequence (Slabel _ region) _)) _ => region
  | _ => Sskip end.
Fixpoint assignment_nodes body : list statement :=
  match body with
  | Sassign _ _ => [body]
  | Ssequence first second | Sloop first second => assignment_nodes first++assignment_nodes second
  | Sifthenelse _ yes no => assignment_nodes yes++assignment_nodes no
  | Slabel _ body => assignment_nodes body
  | _ => [] end.
Definition mxv_assignments := assignment_nodes (selected_region (fn_body MxvSource.f_main)).
Definition matmul_init_assignments := assignment_nodes (selected_region (fn_body MatmulInitSource.f_main)).
Definition mxv_initializer := hd Sskip mxv_assignments.
Definition matmul_initializer := hd Sskip matmul_init_assignments.
Definition assignment_description source :=
  match decode_double_assignment source with
  | Some descriptor => descriptor
  | None => DoubleAssignmentDescriptor (Econst_float Float.zero memory_double_type) [] (DoubleBits 0)
  end.
Definition mxv_initializer_description := assignment_description mxv_initializer.
Definition matmul_initializer_description := assignment_description matmul_initializer.

Theorem original_initialization_assignment_counts :
  length mxv_assignments=2%nat /\ length matmul_init_assignments=2%nat.
Proof. split; reflexivity. Qed.
Theorem original_initializers_have_integer_rhs :
  match mxv_initializer,matmul_initializer with
  | Sassign _ first,Sassign _ second =>
      first=Econst_int Int.zero (Tint I32 Signed noattr) /\
      second=Econst_int Int.zero (Tint I32 Signed noattr)
  | _,_ => False end.
Proof. split; reflexivity. Qed.
Theorem mxv_initializer_decodes : decode_double_assignment mxv_initializer=Some mxv_initializer_description.
Proof. reflexivity. Qed.
Theorem matmul_initializer_decodes : decode_double_assignment matmul_initializer=Some matmul_initializer_description.
Proof. reflexivity. Qed.
Theorem original_initializers_have_no_reads :
  double_assignment_reads mxv_initializer_description=[] /\
  double_assignment_reads matmul_initializer_description=[].
Proof. split; reflexivity. Qed.

Theorem mxv_initializer_execution fe ge locals temps memory write final :
  double_memory_location_receipt ge locals temps memory
    (double_assignment_target mxv_initializer_description) write ->
  (exec_stmt fe ge locals temps memory mxv_initializer E0 temps final Out_normal <->
   memory_action_run (double_assignment_descriptor_action mxv_initializer_description [] write) memory final).
Proof.
  intro WRITE; eapply decoded_double_assignment_execution_iff;
    [exact mxv_initializer_decodes|constructor|exact WRITE].
Qed.
Theorem matmul_initializer_execution fe ge locals temps memory write final :
  double_memory_location_receipt ge locals temps memory
    (double_assignment_target matmul_initializer_description) write ->
  (exec_stmt fe ge locals temps memory matmul_initializer E0 temps final Out_normal <->
   memory_action_run (double_assignment_descriptor_action matmul_initializer_description [] write) memory final).
Proof.
  intro WRITE; eapply decoded_double_assignment_execution_iff;
    [exact matmul_initializer_decodes|constructor|exact WRITE].
Qed.

Print Assumptions original_initialization_assignment_counts.
Print Assumptions original_initializers_have_integer_rhs.
Print Assumptions mxv_initializer_decodes.
Print Assumptions matmul_initializer_decodes.
Print Assumptions original_initializers_have_no_reads.
Print Assumptions mxv_initializer_execution.
Print Assumptions matmul_initializer_execution.
'''


def flags():
    return [*lowering.flags(), "-Q", str(SOURCE / "mxv"), "GuardDoubleInitMxv",
            "-Q", str(SOURCE / "matmul-init"), "GuardDoubleInitMatmul",
            "-Q", str(WORK), "GuardDoubleInitProof"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    baseline = json.loads((SOURCE / "report.json").read_text())
    if baseline["status"] != "exported":
        raise ValueError("Expected successful original exports")
    for name, digest in baseline["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError("Changed export input: " + name)
    if (WORK / "report.json").exists():
        raise ValueError("Successful source checkpoint is frozen")
    WORK.mkdir(exist_ok=True)
    attempts = WORK / "attempts"
    attempts.mkdir(exist_ok=True)
    commands = []
    for item in baseline["results"]:
        source = permitted(ROOT / item["AST"])
        if not source.with_suffix(".vo").exists():
            argv = ["rocq", "compile", "-time", *flags(), str(source)]
            commands.append(argv)
            with (attempts / f'{item["module"]}-{args.attempt}.log').open("x") as log:
                run = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
            (attempts / f'{item["module"]}-{args.attempt}.json').write_text(json.dumps({"command": argv,
                "source_sha256": sha(source), "returncode": run.returncode}, indent=2)+"\n")
            if run.returncode:
                raise SystemExit(run.returncode)
    source = WORK / "OriginalDoubleInitialization.v"
    if source.with_suffix(".vo").exists():
        raise ValueError("Successful proof source and object are frozen")
    source.write_text(CODE)
    snapshot = attempts / (args.attempt + ".v")
    with snapshot.open("x") as archive:
        archive.write(CODE)
    argv = ["rocq", "compile", "-time", *flags(), str(source)]
    commands.append(argv)
    with (attempts / (args.attempt + ".log")).open("x") as log:
        run = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    (attempts / (args.attempt + ".json")).write_text(json.dumps({"command": argv,
        "source_sha256": sha(snapshot), "returncode": run.returncode}, indent=2)+"\n")
    print(json.dumps({"returncode": run.returncode, "log": str((attempts / (args.attempt + ".log")).relative_to(ROOT))}))
    if run.returncode:
        print((attempts / (args.attempt + ".log")).read_text()[-5000:])
        raise SystemExit(run.returncode)
    bindings = dict(baseline["bindings"])
    for path in [Path(__file__), SOURCE / "report.json", *WORK.rglob("*"), *SOURCE.rglob("*")]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "compiled", "kind": "actual-original-initialization-assignment-source-bindings",
              "commands": commands, "actual_original_sources": [item["case"] for item in baseline["results"]],
              "assignment_nodes_observed": 4, "initialization_nodes_decoded": 2,
              "original_integer_zero_nodes_retained": True,
              "whole_loop_source_bridge_or_installation_added": False,
              "new_native_or_optimized_benchmark_evidence": False, "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
