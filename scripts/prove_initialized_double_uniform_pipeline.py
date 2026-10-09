"""Connect the common-coordinate pipeline to actual source capture receipts."""

import argparse
import json
from pathlib import Path
import subprocess

import audit_initialized_double_pipeline as parent
import prove_initialized_double_entry as entry
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/double-initialized-nests/uniform-proof-v1"


def flags():
    return [*entry.flags(), "-Q", str(WORK), "GuardInitializedUniformProof"]


def code():
    parts = [entry.pipeline.raw_proof.canonical.HEADER,
             "From GuardMemory Require Import GuardMemoryDoublePolyhedral GuardMemoryDoubleUniformPrepared GuardMemoryLongRangeCapture.",
             "From Guard Require Import ClightTempFrame ClightTempFootprint.",
             "From GuardInitializedNestProof Require Import OriginalInitializedDoubleNests.",
             "From GuardInitializedRawNestProof Require Import OriginalInitializedDoubleRawNests.",
             "From GuardInitializedPipelineProof Require Import OriginalInitializedDoublePipeline.",
             "From GuardInitializedEntryProof Require Import OriginalInitializedDoubleEntry.",
             "From polcert.polygen Require Import Result.",
             "From polcert.lib Require Import ImpureAlarmConfig.",
             "From Vpl Require Import Impure."]
    endpoints = []
    for name, module, _, _ in entry.FIXTURES:
        parts.append(fr'''
Theorem {name}_uniform_exportable : exists model exported,
  DoubleAssignmentExtractor.extractor {name}_initialized_pipeline_request=Okk model /\
  export_double_uniform_model model=Some exported.
Proof.
  eexists; eexists; split.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.
Theorem {name}_capture_and_uniform_candidate schedule swaps generated fe ge locals temps memory cache flag live after final :
  mayReturn (checked_double_uniform_prepared_loop_progress schedule swaps {name}_initialized_pipeline_request) (Some generated) ->
  preserving_globals (globalenv {module}.prog) ge ->
  locals_avoid (double_initialized_reduction_globals {name}_initialized_description) locals ->
  cache<>flag ->
  (forall key, In key (statement_temps {name}_raw_whole_source++live) -> ~ In key [cache;flag]) ->
  exec_stmt fe ge locals temps memory {name}_raw_whole_source E0 after final Out_normal ->
  exists (accepted : bool) prepared prepared_after,
    exec_stmt fe ge locals temps memory
      (memory_long_range_capture (initialized_reduction_header {name}_initialized_description) cache flag 98)
      E0 prepared memory Out_normal /\
    prepared ! flag=Some (Vint (if accepted then Int.one else Int.zero)) /\
    temp_agree live temps prepared /\
    exec_stmt fe ge locals prepared memory {name}_raw_whole_source E0 prepared_after final Out_normal /\
    temp_agree live after prepared_after /\
    (accepted=true -> exists count,
      Z.of_nat count<=98 /\
      prepared ! cache=Some (Vint (Int.repr (Z.of_nat count))) /\
      DoubleAssignmentIRs.Loop.loop_semantics (fst (fst generated)) [Z.of_nat count]
        (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts {name}_initialized_description)) memory)
        (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts {name}_initialized_description)) final) /\
      prepared_after=double_initialized_nest_exit {name}_outer_iterators
        (initialized_reduction_iterator {name}_initialized_description) count prepared).
Proof.
  intros PIPELINE GLOBAL LOCAL DISTINCT PRIVATE SOURCE.
  destruct (@{name}_initialized_capture_and_model fe ge locals temps memory cache flag live after final
    GLOBAL LOCAL DISTINCT PRIVATE SOURCE)
    as [accepted [prepared [prepared_after [CAPTURE [FLAG [ENTRY [FALLBACK [EXIT FACTS]]]]]]]].
  exists accepted,prepared,prepared_after.
  split; [exact CAPTURE|split; [exact FLAG|split; [exact ENTRY|split; [exact FALLBACK|split; [exact EXIT|]]]]].
  intro TRUE; destruct (FACTS TRUE) as [count [RANGE [CACHE [MODEL SET]]]].
  exists count; split; [exact RANGE|split; [exact CACHE|split; [|exact SET]]].
  apply (proj1 (@checked_double_uniform_prepared_loop_progress_at schedule swaps {name}_initialized_pipeline_request
    generated [Z.of_nat count]
    (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts {name}_initialized_description)) memory)
    (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts {name}_initialized_description)) final)
    PIPELINE eq_refl ltac:(apply global_double_locations_nonalias))); exact MODEL.
Qed.
''')
        endpoints += [name + "_uniform_exportable", name + "_capture_and_uniform_candidate"]
    parts += ["Print Assumptions " + name + "." for name in endpoints]
    return "\n".join(parts) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    baseline = parent.validate()
    if (WORK / "report.json").exists():
        raise ValueError("Successful proof checkpoint is frozen")
    WORK.mkdir(parents=True, exist_ok=True)
    attempts = WORK / "attempts"
    attempts.mkdir(exist_ok=True)
    source = WORK / "OriginalInitializedDoubleUniform.v"
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
    bindings = dict(baseline["bindings"])
    for path in [Path(__file__), parent.WORK / "report.json", *WORK.rglob("*")]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "compiled", "kind": "actual-source-capture-to-uniform-final-checked-candidate",
              "actual_original_cases": ["mxv", "matmul-init"],
              "common_schedule_coordinates_and_actual_parameter_count": True,
              "actual_capture_produces_all_numeric_candidate_entry_premises": True,
              "candidate_lowering_or_Csem_installation_added": False, "bindings": bindings}
    (WORK / "report.json").open("x").write(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
