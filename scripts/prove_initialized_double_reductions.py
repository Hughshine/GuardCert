"""Bind initialized reduction source/model bridges to both original kernels."""

import argparse
import json
from pathlib import Path
import subprocess

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
import prove_double_source_instructions as instructions

WORK = ROOT / "build/double-initialized-reductions/source-proof-v1"
HEADER = r'''
From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Floats.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From polcert.lib Require Import Linalg.
From Guard Require Import ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryDynamicTensorLayout
  GuardMemoryDoubleValue GuardMemoryDoubleLocations GuardMemoryDoubleAssignmentFactory
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTransport GuardMemoryDoubleAffineSourceAccess
  GuardMemoryDoubleSourceLoopModel GuardMemoryDoubleInitializedReductionData
  GuardMemoryDoubleInitializedReductionSource GuardMemoryDoubleSourceResolvedPoints.
From GuardDoubleInitMxv Require Import MxvSource.
From GuardDoubleInitMatmul Require Import MatmulInitSource.
From GuardDoubleInitProof Require Import OriginalDoubleInitialization.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition initialized_loop_body source := match source with
  | Ssequence (Sset _ _) (Sloop (Ssequence _ body) _) => body
  | _ => Sskip end.
Definition reduction_description p controls source :=
  match checked_double_initialized_reduction p controls source with
  | Some description => description
  | None => let dummy := DoubleSourceInstruction
      (DoubleAssignmentDescriptor (Econst_float Float.zero memory_double_type) [] (DoubleBits 0))
      (DoubleAffineSourceAccess (1%positive,[]) []) [] in
      DoubleInitializedReduction 1%positive 1%positive Sskip Sskip dummy dummy end.
'''
FIXTURES = [("mxv", "MxvSource", ["_i"], 1, "_j"),
            ("matmul_init", "MatmulInitSource", ["_i", "_j"], 2, "_k__1")]


def bounded_proofs(name, module):
    if name == "mxv":
        specifications = [
            ("initial", ["i"], [("_y", "[([1],2)]", "[100]")]),
            ("body", ["i", "j"], [("_y", "[([1;0],2)]", "[100]"),
                                    ("_y", "[([1;0],2)]", "[100]"),
                                    ("_a", "[([1;0],2);([0;1],2)]", "[100;100]"),
                                    ("_x", "[([0;1],2)]", "[100]")])]
    else:
        specifications = [
            ("initial", ["i", "j"], [("_C", "[([1;0],2);([0;1],2)]", "[100;100]")]),
            ("body", ["i", "j", "k"], [("_C", "[([1;0;0],2);([0;1;0],2)]", "[100;100]"),
                                         ("_C", "[([1;0;0],2);([0;1;0],2)]", "[100;100]"),
                                         ("_A", "[([1;0;0],2);([0;0;1],2)]", "[100;100]"),
                                         ("_B", "[([0;0;1],2);([0;1;0],2)]", "[100;100]")])]
    output, endpoints = [], []
    for part, coordinates, accesses in specifications:
        entry = "initialized_reduction_" + ("initial_instruction" if part == "initial" else "body_instruction")
        vector = "[" + ";".join(coordinates) + "]"
        ranges = " -> ".join("0<=" + coordinate + "<98" for coordinate in coordinates)
        explicit = "[" + ";".join(f"DoubleAffineSourceAccess ({module}.{array},{rows}) {dimensions}"
                                    for array, rows, dimensions in accesses) + "]"
        theorem = name + "_" + part + "_bounds"
        hypotheses = " ".join("RANGE_" + coordinate for coordinate in coordinates)
        # Nested right disjunctions are kept explicit; each branch names only
        # the equality selected from the actual access list.
        pattern = "[SAME|" * len(accesses) + "IMPOSSIBLE" + "]" * len(accesses)
        output.append(f'''
Theorem {theorem} {' '.join(coordinates)} : {ranges} ->
  double_source_instruction_bounded ({entry} {name}_initialized_description) {vector}.
Proof.
  intros {hypotheses} access MEMBER.
  change (In access {explicit}) in MEMBER; cbn [In] in MEMBER.
  destruct MEMBER as {pattern}; try contradiction;
    subst access; unfold double_source_access_bounded, affine_product;
    cbn [double_affine_source_dimensions double_affine_source_function fst snd map dot_product];
    repeat (apply Forall2_cons; [lia|]); apply Forall2_nil.
Qed.
''')
        endpoints.append(theorem)
    return "\n".join(output), endpoints


def code():
    parts, endpoints = [HEADER], []
    for name, module, controls, depth, iterator in FIXTURES:
        control_code = "[" + ";".join(module + "." + identifier for identifier in controls) + "]"
        source_code = "selected_region (fn_body " + module + ".f_main)"
        for _ in range(depth):
            source_code = "initialized_loop_body (" + source_code + ")"
        parts.append(f'''
Definition {name}_controls := {control_code}.
Definition {name}_initialized_body := {source_code}.
Definition {name}_initialized_description := reduction_description {module}.prog {name}_controls {name}_initialized_body.
Theorem {name}_initialized_body_compiles :
  checked_double_initialized_reduction {module}.prog {name}_controls {name}_initialized_body=Some {name}_initialized_description.
Proof. reflexivity. Qed.
Theorem {name}_initialized_header_iterator :
  initialized_reduction_header {name}_initialized_description={module}._N /\\
  initialized_reduction_iterator {name}_initialized_description={module}.{iterator}.
Proof. split; reflexivity. Qed.
Theorem {name}_initialized_scope :
  function_avoids_check (double_initialized_reduction_globals {name}_initialized_description) {module}.f_main=true.
Proof. reflexivity. Qed.
''')
        bounds, bound_endpoints = bounded_proofs(name, module)
        parts.append(bounds)
        endpoints += bound_endpoints
        parts.append(f'''
Theorem {name}_initialized_source_model valuation fe ge locals header_block count temps memory after final :
  preserving_globals (globalenv {module}.prog) ge ->
  locals_avoid (double_initialized_reduction_globals {name}_initialized_description) locals ->
  double_global_binding ge locals (initialized_reduction_header {name}_initialized_description) header_block ->
  Z.of_nat count<=Int64.max_signed ->
  double_source_instruction_bounded (initialized_reduction_initial_instruction {name}_initialized_description)
    (map valuation {name}_controls) ->
  (forall value, 0<=value<Z.of_nat count ->
    double_source_instruction_bounded (initialized_reduction_body_instruction {name}_initialized_description)
      (map valuation {name}_controls++[value])) ->
  double_source_prefix_words {name}_controls valuation temps ->
  Mem.load Mint64 memory header_block 0=Some (Vlong (Int64.repr (Z.of_nat count))) ->
  (exec_stmt fe ge locals temps memory {name}_initialized_body E0 after final Out_normal <->
   SL.loop_semantics (double_source_initialized_reduction_model
       (double_source_instruction_model (initialized_reduction_initial_instruction {name}_initialized_description))
       (double_source_instruction_model (initialized_reduction_body_instruction {name}_initialized_description))
       (length {name}_controls))
     (rev (map valuation {name}_controls)++[Z.of_nat count])
     (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts {name}_initialized_description)) memory)
     (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts {name}_initialized_description)) final) /\\
   after=PTree.set (initialized_reduction_iterator {name}_initialized_description)
     (Vlong (Int64.repr (Z.of_nat count))) temps).
Proof.
  intros GLOBAL LOCAL HEADER UPPER INITIAL_BOUNDS BODY_BOUNDS WORDS LOAD.
  destruct (@checked_double_initialized_reduction_sound {module}.prog {name}_controls {name}_initialized_body
    {name}_initialized_description {name}_initialized_body_compiles) as [CODE [IC [BC STATIC]]].
  destruct (@double_initialized_reduction_static_sound {module}.prog {name}_controls {name}_initialized_description STATIC)
    as [DISTINCT [DECL [IW [RW [IL RL]]]]].
  destruct (double_initialized_reduction_scope LOCAL) as [LI LR].
  assert (INITIAL : double_source_instruction_resolved (initialized_reduction_initial_instruction {name}_initialized_description)
    (map valuation {name}_controls) ge (double_initialized_reduction_layouts {name}_initialized_description)).
  {{ eapply checked_double_source_instruction_resolved_from_bounds; eassumption. }}
  assert (BODY : forall value, 0<=value<Z.of_nat count ->
    double_source_instruction_resolved (initialized_reduction_body_instruction {name}_initialized_description)
      (map valuation {name}_controls++[value]) ge (double_initialized_reduction_layouts {name}_initialized_description)).
  {{ intros value RANGE; eapply checked_double_source_instruction_resolved_from_bounds;
      [exact BC|exact RL|exact GLOBAL|exact LR|apply BODY_BOUNDS; exact RANGE]. }}
  eapply double_initialized_reduction_source_model;
    [exact {name}_initialized_body_compiles|exact GLOBAL|exact LOCAL|exact HEADER|exact UPPER|exact INITIAL|exact BODY|].
  split; assumption.
Qed.
''')
        endpoints += [name + suffix for suffix in ("_initialized_body_compiles", "_initialized_header_iterator",
                                                   "_initialized_scope", "_initialized_source_model")]
    parts += ["\n".join("Print Assumptions " + endpoint + "." for endpoint in endpoints)]
    return "\n".join(parts) + "\n"


def flags():
    return [*instructions.flags(), "-Q", str(WORK), "GuardInitializedDoubleProof"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    baseline_path = instructions.WORK / "report.json"
    baseline = json.loads(baseline_path.read_text())
    if baseline["status"] != "compiled":
        raise ValueError("Expected compiled source instruction bindings")
    for name, digest in baseline["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError("Changed source binding: " + name)
    if (WORK / "report.json").exists():
        raise ValueError("Successful source checkpoint is frozen")
    WORK.mkdir(parents=True, exist_ok=True)
    attempts = WORK / "attempts"
    attempts.mkdir(exist_ok=True)
    source = WORK / "OriginalInitializedDoubleReductions.v"
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
    report = {"status": "compiled", "kind": "actual-initializer-and-inner-reduction-source-model-bindings",
              "commands": [argv], "actual_original_sources": ["mxv", "matmul-init"],
              "initialized_reduction_components_compiled": len(FIXTURES),
              "outer_control_dimensions": [1, 2], "initializer_integer_zero_preserved": True,
              "complete_inner_loop_and_intermediate_memory_correspondence": True,
              "whole_marked_region_bridge_or_installation_added": False,
              "point_bounds_still_logical_premises": True,
              "actual_100_extent_geometry_lemmas_discharge_bounds_for_controls_below_98": True,
              "new_native_or_optimized_benchmark_evidence": False, "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
