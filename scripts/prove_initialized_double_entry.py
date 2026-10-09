"""Produce actual-source header, capture, range and pipeline-entry evidence."""

import argparse
import json
from pathlib import Path
import subprocess

import export_initialized_double_raw_sources as exported
import prove_initialized_double_pipeline as pipeline
import audit_initialized_double_nests as parent
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/double-initialized-nests/entry-proof-v1"
FIXTURES = [("mxv", "MxvSource", "GuardInitializedRawMxv", "MxvRawSource"),
            ("matmul_init", "MatmulInitSource", "GuardInitializedRawMatmul", "MatmulInitRawSource")]


def flags():
    return [*pipeline.flags(), "-Q", str(WORK), "GuardInitializedEntryProof"]


def code():
    parts = [pipeline.raw_proof.canonical.HEADER,
             "From GuardMemory Require Import GuardMemoryDoublePolyhedral GuardMemoryDoubleInitializedEntry GuardMemoryLongRangeCapture.",
             "From Guard Require Import ClightTempFrame ClightTempFootprint.",
             "From GuardInitializedNestProof Require Import OriginalInitializedDoubleNests.",
             "From GuardInitializedRawNestProof Require Import OriginalInitializedDoubleRawNests.",
             "From GuardInitializedPipelineProof Require Import OriginalInitializedDoublePipeline."]
    endpoints = []
    for name, module, namespace, raw in FIXTURES:
        rest = "[]" if name == "mxv" else "[MatmulInitSource._j]"
        parts.append(fr'''
Theorem {name}_initialized_header_binding ge locals :
  preserving_globals (globalenv {module}.prog) ge ->
  locals_avoid (double_initialized_reduction_globals {name}_initialized_description) locals ->
  exists header_block, double_global_binding ge locals (initialized_reduction_header {name}_initialized_description) header_block.
Proof.
  intros GLOBAL LOCAL.
  destruct (@checked_double_initialized_nest_sound {module}.prog [] {name}_whole_source
    {name}_outer_iterators {name}_initialized_description {name}_whole_nest_compiles) as [CODE [LEAF FRESH]].
  eapply checked_double_initialized_reduction_header_binding; eassumption.
Qed.
Theorem {name}_initialized_capture_and_model fe ge locals temps memory cache flag live after final :
  preserving_globals (globalenv {module}.prog) ge ->
  locals_avoid (double_initialized_reduction_globals {name}_initialized_description) locals ->
  cache<>flag ->
  (forall key, In key (statement_temps {name}_raw_whole_source++live) -> ~ In key [cache;flag]) ->
  exec_stmt fe ge locals temps memory {name}_raw_whole_source E0 after final Out_normal ->
  exists (accepted : bool) prepared prepared_after,
    exec_stmt fe ge locals temps memory
+      (memory_long_range_capture (initialized_reduction_header {name}_initialized_description) cache flag 98)
+      E0 prepared memory Out_normal /\
+    prepared ! flag=Some (Vint (if accepted then Int.one else Int.zero)) /\
+    temp_agree live temps prepared /\
+    exec_stmt fe ge locals prepared memory {name}_raw_whole_source E0 prepared_after final Out_normal /\
+    temp_agree live after prepared_after /\
+    (accepted=true -> exists count,
+      Z.of_nat count<=98 /\
+      prepared ! cache=Some (Vint (Int.repr (Z.of_nat count))) /\
+      DoubleAssignmentIRs.Loop.loop_semantics (fst (fst {name}_initialized_pipeline_request)) [Z.of_nat count]
+        (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts {name}_initialized_description)) memory)
+        (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts {name}_initialized_description)) final) /\
+      prepared_after=double_initialized_nest_exit {name}_outer_iterators
+        (initialized_reduction_iterator {name}_initialized_description) count prepared).
+Proof.
+  intros GLOBAL LOCAL DISTINCT PRIVATE SOURCE.
+  destruct (@{name}_initialized_header_binding ge locals GLOBAL LOCAL) as [header_block HEADER].
+  destruct (@checked_double_initialized_raw_source_capture {module}.prog [] {name}_raw_whole_source {module}._i
+    {rest} {name}_initialized_description fe ge locals temps memory header_block cache flag 98 after final
+    {name}_raw_whole_compiles HEADER ltac:(change (0<=98<=2147483647); lia) DISTINCT SOURCE)
+    as [accepted [prepared [CAPTURE [FLAG FACTS]]]].
+  destruct (@checked_double_initialized_capture_source_transport {module}.prog [] {name}_raw_whole_source
+    {name}_outer_iterators {name}_initialized_description fe ge locals temps memory cache flag 98 live prepared after final
+    {name}_raw_whole_compiles PRIVATE CAPTURE SOURCE) as [prepared_after [PREPARED EXIT]].
+  exists accepted,prepared,prepared_after; split; [exact CAPTURE|split; [exact FLAG|split]].
+  - eapply double_initialized_capture_public_frame; [|exact CAPTURE].
+    intros key MEMBER; apply PRIVATE; apply in_or_app; right; exact MEMBER.
+  - split; [exact PREPARED|split; [exact EXIT|intro TRUE]].
+    destruct (FACTS TRUE) as [count [RANGE [CACHE LOAD]]].
+    destruct (proj1 (@{name}_initialized_pipeline_source_model fe ge locals header_block count prepared memory prepared_after final
+      GLOBAL LOCAL HEADER RANGE LOAD) PREPARED) as [MODEL SET].
+    exists count; repeat split; assumption.
+Qed.
+'''.replace("\n+", "\n"))
        endpoints += [name+suffix for suffix in ("_initialized_header_binding", "_initialized_capture_and_model")]
    parts += ["Print Assumptions "+name+"." for name in endpoints]
    return "\n".join(parts)+"\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    baseline = json.loads((pipeline.WORK / "report.json").read_text())
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
    source = WORK / "OriginalInitializedDoubleEntry.v"
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
    paths = [Path(__file__), pipeline.WORK / "report.json", exported.WORK / "report.json"]
    paths += [path for path in WORK.rglob("*") if path.is_file()]
    for path in paths:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "compiled", "kind": "actual-initialized-double-safe-capture-and-model-entry",
              "actual_original_cases": ["mxv", "matmul-init"],
              "actual_source_to_pipeline_Loop_iff": True,
              "extractor_and_literal_OpenScop_export_success_proved": True,
              "capture_accepted_and_refused_public_source_transport": True,
              "candidate_lowering_or_installation_added": False,
              "source_execution_produces_header_load_and_accepted_count_without_numeric_entry_premises": True,
              "new_guard_compiler_or_native_optimized_case": False, "bindings": bindings}
    (WORK / "report.json").open("x").write(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
