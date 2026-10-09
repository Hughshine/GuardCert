"""Bind full checked canonical initialization/reduction nests to original inputs."""

import argparse
import json
from pathlib import Path
import subprocess

import audit_initialized_double_reductions as parent
import prove_initialized_double_reductions as inner
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/double-initialized-nests/source-proof-v1"
HEADER = inner.HEADER + r'''
From GuardMemory Require Import GuardMemoryDoubleInitializedNestData GuardMemoryDoubleInitializedNestSyntax
  GuardMemoryDoubleInitializedNestModel GuardMemoryDoubleInitializedNestExit GuardMemoryDoubleInitializedNestSource
  GuardMemoryDoubleInitializedNestProgress.
From GuardInitializedDoubleProof Require Import OriginalInitializedDoubleReductions.
'''
FIXTURES = [("mxv", "MxvSource", ["_i"], "_j"),
            ("matmul_init", "MatmulInitSource", ["_i", "_j"], "_k__1")]


def code():
    parts, endpoints = [HEADER], []
    for name, module, controls, iterator in FIXTURES:
        outer_code = "[" + ";".join(module+"."+key for key in controls) + "]"
        coordinates = ["i", "j"][:len(controls)]
        steps = []
        for coordinate in coordinates:
            steps.append(f"destruct coordinates as [|{coordinate} coordinates]; [cbn [length] in LENGTH; lia|].")
        steps.append("destruct coordinates as [|extra coordinates]; [|cbn [length] in LENGTH; lia].")
        tail = "BOUNDS"
        for index, coordinate in enumerate(coordinates):
            steps.append(f"pose proof (Forall_inv {tail}) as RANGE_{coordinate}.")
            steps.append(f"change (0<={coordinate}<Z.of_nat count) in RANGE_{coordinate}.")
            if index+1 < len(coordinates):
                steps.append(f"pose proof (Forall_inv_tail {tail}) as TAIL_{index}.")
                tail = f"TAIL_{index}"
        bounds_setup = "\n  ".join(steps)
        positive_exit = "temps"
        for key in reversed([*controls, iterator]):
            positive_exit = f"PTree.set {module}.{key} (Vlong (Int64.repr (Z.of_nat (S count)))) ({positive_exit})"
        parts.append(f'''
Definition {name}_whole_source := selected_region (fn_body {module}.f_main).
Definition {name}_outer_iterators := {outer_code}.
Theorem {name}_whole_nest_compiles : checked_double_initialized_nest {module}.prog [] {name}_whole_source=
  Some ({name}_outer_iterators,{name}_initialized_description).
Proof. reflexivity. Qed.
Theorem {name}_whole_nest_ready ge locals count :
  preserving_globals (globalenv {module}.prog) ge ->
  locals_avoid (double_initialized_reduction_globals {name}_initialized_description) locals ->
  Z.of_nat count<=98 ->
  double_initialized_nest_ready {name}_initialized_description ge count [] (length {name}_outer_iterators).
Proof.
  intros GLOBAL LOCAL UPPER coordinates LENGTH BOUNDS.
  change (length coordinates={len(controls)}%nat) in LENGTH.
  {bounds_setup}
  destruct (@checked_double_initialized_nest_sound {module}.prog [] {name}_whole_source {name}_outer_iterators
    {name}_initialized_description {name}_whole_nest_compiles) as [CODE [LEAF FRESH]].
  destruct (@checked_double_initialized_reduction_sound {module}.prog ([]++{name}_outer_iterators)
    (double_initialized_reduction_code {name}_initialized_description) {name}_initialized_description LEAF)
    as [_ [IC [BC STATIC]]].
  destruct (@double_initialized_reduction_static_sound {module}.prog ([]++{name}_outer_iterators)
    {name}_initialized_description STATIC) as [DISTINCT [DECL [IW [RW [IL RL]]]]].
  destruct (double_initialized_reduction_scope LOCAL) as [LI LR].
  split.
  - eapply checked_double_source_instruction_resolved_from_bounds;
      [exact IC|exact IL|exact GLOBAL|exact LI|].
    apply (@{name}_initial_bounds {' '.join(coordinates)}); lia.
  - intros value RANGE; eapply checked_double_source_instruction_resolved_from_bounds;
      [exact BC|exact RL|exact GLOBAL|exact LR|].
    apply (@{name}_body_bounds {' '.join(coordinates)} value); lia.
Qed.
Theorem {name}_whole_source_model fe ge locals header_block count temps memory after final :
  preserving_globals (globalenv {module}.prog) ge ->
  locals_avoid (double_initialized_reduction_globals {name}_initialized_description) locals ->
  double_global_binding ge locals (initialized_reduction_header {name}_initialized_description) header_block ->
  Z.of_nat count<=98 ->
  Mem.load Mint64 memory header_block 0=Some (Vlong (Int64.repr (Z.of_nat count))) ->
  (exec_stmt fe ge locals temps memory {name}_whole_source E0 after final Out_normal <->
   SL.loop_semantics (double_source_initialized_nest_model
     (double_source_instruction_model (initialized_reduction_initial_instruction {name}_initialized_description))
     (double_source_instruction_model (initialized_reduction_body_instruction {name}_initialized_description))
     (length {name}_outer_iterators) 0) [Z.of_nat count]
     (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts {name}_initialized_description)) memory)
     (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts {name}_initialized_description)) final) /\\
   after=double_initialized_nest_exit {name}_outer_iterators (initialized_reduction_iterator {name}_initialized_description) count temps).
Proof.
  intros GLOBAL LOCAL HEADER UPPER LOAD.
  eapply (@checked_double_initialized_nest_source_model {module}.prog fe ge locals header_block count GLOBAL
    ltac:(change (Z.of_nat count<=9223372036854775807); lia) [] (fun _=>0));
    [exact {name}_whole_nest_compiles|exact LOCAL|exact HEADER| |].
  - eapply {name}_whole_nest_ready; eassumption.
  - split; [intros key MEMBER; contradiction|exact LOAD].
Qed.
Theorem {name}_whole_zero_exit temps :
  double_initialized_nest_exit {name}_outer_iterators (initialized_reduction_iterator {name}_initialized_description) 0 temps=
    PTree.set {module}.{controls[0]} (Vlong Int64.zero) temps.
Proof. reflexivity. Qed.
Theorem {name}_whole_positive_exit count temps :
  double_initialized_nest_exit {name}_outer_iterators (initialized_reduction_iterator {name}_initialized_description) (S count) temps=
    {positive_exit}.
Proof. reflexivity. Qed.
Theorem {name}_whole_source_progress : exists F : region_progress {name}_whole_source, True.
Proof. eapply checked_double_initialized_nest_region_progress; exact {name}_whole_nest_compiles. Qed.
''')
        endpoints += [name+suffix for suffix in ("_whole_nest_compiles", "_whole_nest_ready", "_whole_source_model",
                                                "_whole_zero_exit", "_whole_positive_exit", "_whole_source_progress")]
    parts.append("\n".join("Print Assumptions " + name + "." for name in endpoints))
    return "\n".join(parts)+"\n"


def flags():
    return [*inner.flags(), "-Q", str(WORK), "GuardInitializedNestProof"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    baseline = parent.validate()
    if (WORK / "report.json").exists():
        raise ValueError("Successful source checkpoint is frozen")
    WORK.mkdir(parents=True, exist_ok=True)
    attempts = WORK / "attempts"
    attempts.mkdir(exist_ok=True)
    source = WORK / "OriginalInitializedDoubleNests.v"
    if source.with_suffix(".vo").exists():
        raise ValueError("Successful source/object are frozen")
    source.write_text(code())
    snapshot = attempts / (args.attempt+".v")
    with snapshot.open("xb") as archive:
        archive.write(source.read_bytes())
    argv = ["rocq", "compile", "-time", *flags(), str(source)]
    log_path = attempts / (args.attempt+".log")
    with log_path.open("x") as log:
        run = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    (attempts / (args.attempt+".json")).write_text(json.dumps({"command": argv,
        "source_sha256": sha(snapshot), "returncode": run.returncode}, indent=2)+"\n")
    print(json.dumps({"returncode": run.returncode, "log": str(log_path.relative_to(ROOT))}), flush=True)
    if run.returncode:
        print(log_path.read_text()[-5500:])
        raise SystemExit(run.returncode)
    bindings = dict(baseline["bindings"])
    for path in [Path(__file__), parent.WORK / "report.json", *WORK.rglob("*")]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "compiled", "kind": "actual-full-canonical-initialized-double-nest-bindings",
              "actual_original_sources": ["mxv", "matmul-init"], "outer_depths": [1, 2],
              "full_canonical_regions_have_finite_source_model_iff": True,
              "all_point_address_resolution_produced_for_counts_at_most_98": True,
              "zero_outer_count_preserves_unreached_inner_temporaries": True,
              "small_step_source_progress_produced_independently_of_accepted_bounds": True,
              "raw_frontend_skip_transport_or_progress_added": False,
              "runtime_header_load_receipt_still_logical_premise": True,
              "new_guard_compiler_or_native_optimized_case": False, "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
