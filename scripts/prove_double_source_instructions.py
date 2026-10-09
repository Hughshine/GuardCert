"""Bind automatically encoded instructions to four original assignment nodes."""

import argparse
import json
from pathlib import Path
import subprocess

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
import prove_double_initialization_sources as initialization

WORK = ROOT / "build/double-source-instructions/source-proof-v1"
HEADER = r'''
From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers Floats.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryDynamicTensorLayout
  GuardMemoryDoubleValue GuardMemoryDoubleLocations GuardMemoryDoubleAssignment
  GuardMemoryDoubleAssignmentFactory GuardMemoryDoubleTensorBackend
  GuardMemoryDoubleAffineSourceAccess GuardMemoryDoubleSourceInstruction.
From GuardDoubleInitMxv Require Import MxvSource.
From GuardDoubleInitMatmul Require Import MatmulInitSource.
From GuardDoubleInitProof Require Import OriginalDoubleInitialization.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition instruction_description p controls source :=
  match checked_double_source_instruction p controls source with
  | Some description => description
  | None => DoubleSourceInstruction
      (DoubleAssignmentDescriptor (Econst_float Float.zero memory_double_type) [] (DoubleBits 0))
      (DoubleAffineSourceAccess (1%positive,[]) []) [] end.
'''
FIXTURES = [
    ("mxv_initializer", "MxvSource", "mxv_assignments", 0, ["_i"], "_y", "[([1],2)]", 0),
    ("mxv_reduction", "MxvSource", "mxv_assignments", 1, ["_i", "_j"], "_y", "[([1;0],2)]", 3),
    ("matmul_initializer", "MatmulInitSource", "matmul_init_assignments", 0, ["_i", "_j"],
     "_C", "[([1;0],2);([0;1],2)]", 0),
    ("matmul_reduction", "MatmulInitSource", "matmul_init_assignments", 1, ["_i", "_j", "_k__1"],
     "_C", "[([1;0;0],2);([0;1;0],2)]", 3),
]


def code():
    parts = [HEADER]
    endpoints = []
    for name, module, nodes, index, controls, target, rows, read_count in FIXTURES:
        control_code = "[" + ";".join(module + "." + identifier for identifier in controls) + "]"
        parts.append(f'''
Definition {name}_controls := {control_code}.
Definition {name}_source := nth {index}%nat {nodes} Sskip.
Definition {name}_instruction := instruction_description {module}.prog {name}_controls {name}_source.
Theorem {name}_compiles :
  checked_double_source_instruction {module}.prog {name}_controls {name}_source=Some {name}_instruction.
Proof. reflexivity. Qed.
Theorem {name}_access_data :
  value_instruction_write (double_source_instruction_model {name}_instruction)=({module}.{target},{rows}) /\\
  length (value_instruction_reads (double_source_instruction_model {name}_instruction))={read_count}%nat.
Proof. split; reflexivity. Qed.
Theorem {name}_function_scope :
  function_avoids_check (double_source_instruction_globals {name}_instruction) {module}.f_main=true.
Proof. reflexivity. Qed.
Theorem {name}_execution valuation fe ge locals temps memory write reads final :
  preserving_globals (globalenv {module}.prog) ge ->
  locals_avoid (double_source_instruction_globals {name}_instruction) locals ->
  (forall identifier, In identifier {name}_controls ->
    temps ! identifier=Some (Vlong (Int64.repr (valuation identifier)))) ->
  global_double_locations ge (double_source_instruction_layouts {name}_instruction)
    (exact_cell (value_instruction_write (double_source_instruction_model {name}_instruction))
      (map valuation {name}_controls))=Some write ->
  resolve_cells (map (fun access => exact_cell access (map valuation {name}_controls))
    (value_instruction_reads (double_source_instruction_model {name}_instruction)))
    (global_double_locations ge (double_source_instruction_layouts {name}_instruction))=Some reads ->
  (exec_stmt fe ge locals temps memory {name}_source E0 temps final Out_normal <->
   DoubleAssignmentInstr.instr_semantics (double_source_instruction_model {name}_instruction)
    (map valuation {name}_controls)
    [exact_cell (value_instruction_write (double_source_instruction_model {name}_instruction))
      (map valuation {name}_controls)]
    (map (fun access => exact_cell access (map valuation {name}_controls))
      (value_instruction_reads (double_source_instruction_model {name}_instruction)))
    (RuntimeState (global_double_locations ge (double_source_instruction_layouts {name}_instruction)) memory)
    (RuntimeState (global_double_locations ge (double_source_instruction_layouts {name}_instruction)) final)).
Proof. eapply checked_double_source_instruction_execution_iff; exact {name}_compiles. Qed.
''')
        endpoints += [name + suffix for suffix in ("_compiles", "_access_data", "_function_scope", "_execution")]
    parts += ["\n".join("Print Assumptions " + endpoint + "." for endpoint in endpoints)]
    return "\n".join(parts) + "\n"


def flags():
    return [*initialization.flags(), "-Q", str(WORK), "GuardDoubleInstrProof"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    baseline_path = initialization.WORK / "report.json"
    baseline = json.loads(baseline_path.read_text())
    if baseline["status"] != "compiled":
        raise ValueError("Expected compiled original source bindings")
    for name, digest in baseline["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError("Changed source binding: " + name)
    if (WORK / "report.json").exists():
        raise ValueError("Successful source checkpoint is frozen")
    WORK.mkdir(parents=True, exist_ok=True)
    attempts = WORK / "attempts"
    attempts.mkdir(exist_ok=True)
    source = WORK / "OriginalDoubleSourceInstructions.v"
    if source.with_suffix(".vo").exists():
        raise ValueError("Successful source/object are frozen")
    source.write_text(code())
    snapshot = attempts / (args.attempt + ".v")
    with snapshot.open("xb") as archive:
        archive.write(source.read_bytes())
    argv = ["rocq", "compile", "-time", *flags(), str(source)]
    log_path = attempts / (args.attempt + ".log")
    with log_path.open("x") as log:
        run = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    (attempts / (args.attempt + ".json")).write_text(json.dumps({"command": argv,
        "source_sha256": sha(snapshot), "returncode": run.returncode}, indent=2)+"\n")
    print(json.dumps({"returncode": run.returncode, "log": str(log_path.relative_to(ROOT))}), flush=True)
    if run.returncode:
        print(log_path.read_text()[-5000:])
        raise SystemExit(run.returncode)
    bindings = dict(baseline["bindings"])
    for path in [Path(__file__), baseline_path, *WORK.rglob("*")]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "compiled", "kind": "actual-source-to-typed-double-instruction-bindings",
              "commands": [argv], "actual_original_sources": ["mxv", "matmul-init"],
              "actual_assignment_nodes_compiled": len(FIXTURES),
              "source_control_dimensions": [len(item[4]) for item in FIXTURES],
              "source_read_counts": [item[-1] for item in FIXTURES],
              "layouts_and_accesses_generated_from_actual_AST": True,
              "point_bounds_resolution_still_required": True,
              "whole_loop_source_bridge_or_installation_added": False,
              "new_native_or_optimized_benchmark_evidence": False, "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
