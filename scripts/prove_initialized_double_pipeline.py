"""Connect checked original initialized nests to the literal-capable prepared pipeline."""

import argparse
import json
from pathlib import Path
import subprocess

import export_initialized_double_raw_sources as exported
import prove_initialized_double_raw_nests as raw_proof
import audit_initialized_double_nests as parent
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/double-initialized-nests/pipeline-proof-v1"
FIXTURES = [("mxv", "MxvSource", "GuardInitializedRawMxv", "MxvRawSource"),
            ("matmul_init", "MatmulInitSource", "GuardInitializedRawMatmul", "MatmulInitRawSource")]


def flags():
    return [*raw_proof.flags(), "-Q", str(WORK), "GuardInitializedPipelineProof"]


def code():
    parts = [raw_proof.canonical.HEADER,
             "From GuardMemory Require Import GuardMemoryDoublePolyhedral GuardMemoryDoubleInitializedPipeline GuardMemoryDoubleLiteralPrepared GuardMemoryDoubleCandidateProgress.",
             "From GuardInitializedNestProof Require Import OriginalInitializedDoubleNests.",
             "From GuardInitializedRawNestProof Require Import OriginalInitializedDoubleRawNests.",
             "From polcert.polygen Require Import Result.",
             "From polcert.lib Require Import ImpureAlarmConfig.",
             "From Vpl Require Import Impure."]
    endpoints = []
    for name, module, namespace, raw in FIXTURES:
        parts.append(fr'''
Definition {name}_initialized_pipeline_request : DoubleAssignmentIRs.Loop.t :=
  Eval vm_compute in (double_initialized_pipeline_request {name}_outer_iterators {name}_initialized_description).
Theorem {name}_initialized_pipeline_exportable : exists model exported,
  DoubleAssignmentExtractor.extractor {name}_initialized_pipeline_request=Okk model /\
  export_double_literal_model model=Some exported.
Proof.
  eexists; eexists; split.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.
Theorem {name}_initialized_pipeline_source_model fe ge locals header_block count temps memory after final :
  preserving_globals (globalenv {module}.prog) ge ->
  locals_avoid (double_initialized_reduction_globals {name}_initialized_description) locals ->
  double_global_binding ge locals (initialized_reduction_header {name}_initialized_description) header_block ->
  Z.of_nat count<=98 ->
  Mem.load Mint64 memory header_block 0=Some (Vlong (Int64.repr (Z.of_nat count))) ->
  (exec_stmt fe ge locals temps memory {name}_raw_whole_source E0 after final Out_normal <->
   DoubleAssignmentIRs.Loop.loop_semantics (fst (fst {name}_initialized_pipeline_request)) [Z.of_nat count]
     (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts {name}_initialized_description)) memory)
     (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts {name}_initialized_description)) final) /\
   after=double_initialized_nest_exit {name}_outer_iterators (initialized_reduction_iterator {name}_initialized_description) count temps).
Proof.
  intros GLOBAL LOCAL HEADER UPPER LOAD.
  rewrite (@{name}_raw_whole_source_model fe ge locals header_block count temps memory after final GLOBAL LOCAL HEADER UPPER LOAD).
  rewrite double_initialized_pipeline_model_execution; reflexivity.
Qed.
Theorem {name}_initialized_generated_at schedule swaps generated fe ge locals header_block count temps memory after final :
  mayReturn (checked_double_literal_prepared_loop_progress schedule swaps {name}_initialized_pipeline_request) (Some generated) ->
  preserving_globals (globalenv {module}.prog) ge ->
  locals_avoid (double_initialized_reduction_globals {name}_initialized_description) locals ->
  double_global_binding ge locals (initialized_reduction_header {name}_initialized_description) header_block ->
  Z.of_nat count<=98 ->
  Mem.load Mint64 memory header_block 0=Some (Vlong (Int64.repr (Z.of_nat count))) ->
  exec_stmt fe ge locals temps memory {name}_raw_whole_source E0 after final Out_normal ->
  DoubleAssignmentIRs.Loop.loop_semantics (fst (fst generated)) [Z.of_nat count]
    (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts {name}_initialized_description)) memory)
    (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts {name}_initialized_description)) final).
Proof.
  intros PIPELINE GLOBAL LOCAL HEADER UPPER LOAD SOURCE.
  destruct (proj1 (@{name}_initialized_pipeline_source_model fe ge locals header_block count temps memory after final
    GLOBAL LOCAL HEADER UPPER LOAD) SOURCE) as [MODEL EXIT].
  apply (proj1 (@checked_double_literal_prepared_loop_progress_at schedule swaps {name}_initialized_pipeline_request generated
    [Z.of_nat count] (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts {name}_initialized_description)) memory)
    (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts {name}_initialized_description)) final)
    PIPELINE eq_refl ltac:(apply global_double_locations_nonalias))); exact MODEL.
Qed.
''')
        endpoints += [name+suffix for suffix in ("_initialized_pipeline_exportable", "_initialized_pipeline_source_model", "_initialized_generated_at")]
    parts += ["Print Assumptions "+name+"." for name in endpoints]
    return "\n".join(parts)+"\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    baseline = parent.validate()
    if baseline["status"] != "compiled":
        raise ValueError("Canonical source checkpoint absent")
    exported_report = exported.validate()
    bindings = dict(baseline["bindings"])
    bindings.update(exported_report["bindings"])
    for name, digest in bindings.items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError("Changed source proof input: " + name)
    if (WORK / "report.json").exists():
        raise ValueError("Successful raw source checkpoint is frozen")
    WORK.mkdir(parents=True, exist_ok=True)
    attempts = WORK / "attempts"
    attempts.mkdir(exist_ok=True)
    source = WORK / "OriginalInitializedDoublePipeline.v"
    if source.with_suffix(".vo").exists():
        raise ValueError("Successful source/object are frozen")
    source.write_text(code())
    snapshot = attempts / (args.attempt + ".v")
    snapshot.open("xb").write(source.read_bytes())
    argv = ["rocq", "compile", "-time", *flags(), str(source)]
    log_path = attempts / (args.attempt + ".log")
    with log_path.open("x") as log:
        run = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    (attempts / (args.attempt + ".json")).open("x").write(json.dumps(
        {"command": argv, "source_sha256": sha(snapshot), "returncode": run.returncode}, indent=2) + "\n")
    print(json.dumps({"returncode": run.returncode, "log": str(log_path.relative_to(ROOT))}), flush=True)
    if run.returncode:
        print(log_path.read_text()[-4000:])
        raise SystemExit(run.returncode)
    paths = [Path(__file__), parent.WORK / "report.json", exported.WORK / "report.json"]
    paths += [path for path in WORK.rglob("*") if path.is_file()]
    for path in paths:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "compiled", "kind": "actual-initialized-double-source-to-literal-prepared-pipeline",
              "actual_original_cases": ["mxv", "matmul-init"],
              "actual_source_to_pipeline_Loop_iff": True,
              "extractor_and_literal_OpenScop_export_success_proved": True,
              "accepted_generated_Loop_at_actual_captured_parameter": True,
              "candidate_lowering_or_installation_added": False,
              "entry_header_load_receipt_still_logical_premise": True,
              "new_guard_compiler_or_native_optimized_case": False, "bindings": bindings}
    (WORK / "report.json").open("x").write(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
