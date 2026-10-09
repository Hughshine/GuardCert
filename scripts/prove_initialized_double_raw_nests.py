"""Bind literal frontend source, canonical models and source progress."""

import argparse
import json
from pathlib import Path
import subprocess

import export_initialized_double_raw_sources as exported
import prove_initialized_double_nests as canonical
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/double-initialized-nests/raw-proof-v1"
FIXTURES = [("mxv", "MxvSource", "GuardInitializedRawMxv", "MxvRawSource"),
            ("matmul_init", "MatmulInitSource", "GuardInitializedRawMatmul", "MatmulInitRawSource")]


def flags():
    result = canonical.flags()
    for (case, *_), (_, _, namespace, _) in zip(exported.FIXTURES, FIXTURES):
        result += ["-Q", str(exported.WORK / case), namespace]
    return [*result, "-Q", str(WORK), "GuardInitializedRawNestProof"]


def code():
    parts = [canonical.HEADER,
             "From Guard Require Import ClightSkipPrefix.",
             "From GuardMemory Require Import GuardMemoryDoubleInitializedRawNest GuardMemoryDoubleInitializedRawNestProgress.",
             "From GuardInitializedNestProof Require Import OriginalInitializedDoubleNests."]
    endpoints = []
    for name, module, namespace, raw in FIXTURES:
        parts.append(f"From {namespace} Require Import {raw}.")
        parts.append(fr'''
Definition {name}_raw_whole_source := {raw}.raw_initialized_region.
Theorem {name}_raw_whole_compiles :
  checked_double_initialized_raw_nest {module}.prog [] {name}_raw_whole_source=
    Some ({name}_outer_iterators,{name}_initialized_description).
Proof. reflexivity. Qed.
Theorem {name}_raw_canonical_execution :
  statement_execution_equivalent {name}_raw_whole_source {name}_whole_source.
Proof.
  destruct (@checked_double_initialized_nest_sound {module}.prog [] {name}_whole_source
    {name}_outer_iterators {name}_initialized_description {name}_whole_nest_compiles) as [CODE REST].
  destruct (@checked_double_initialized_raw_nest_sound {module}.prog [] {name}_raw_whole_source
    {name}_outer_iterators {name}_initialized_description {name}_raw_whole_compiles) as [RAW [CHECK EQUIV]].
  rewrite CODE; exact EQUIV.
Qed.
Theorem {name}_raw_whole_source_model fe ge locals header_block count temps memory after final :
  preserving_globals (globalenv {module}.prog) ge ->
  locals_avoid (double_initialized_reduction_globals {name}_initialized_description) locals ->
  double_global_binding ge locals (initialized_reduction_header {name}_initialized_description) header_block ->
  Z.of_nat count<=98 ->
  Mem.load Mint64 memory header_block 0=Some (Vlong (Int64.repr (Z.of_nat count))) ->
  (exec_stmt fe ge locals temps memory {name}_raw_whole_source E0 after final Out_normal <->
   (SL.loop_semantics (double_source_initialized_nest_model
      (double_source_instruction_model (initialized_reduction_initial_instruction {name}_initialized_description))
      (double_source_instruction_model (initialized_reduction_body_instruction {name}_initialized_description))
      (length {name}_outer_iterators) 0) [Z.of_nat count]
      (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts {name}_initialized_description)) memory)
      (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts {name}_initialized_description)) final)) /\
   after=double_initialized_nest_exit {name}_outer_iterators
     (initialized_reduction_iterator {name}_initialized_description) count temps).
Proof.
  intros GLOBAL LOCAL HEADER UPPER LOAD.
  rewrite (@{name}_raw_canonical_execution fe ge locals temps memory E0 after final Out_normal).
  exact (@{name}_whole_source_model fe ge locals header_block count temps memory after final
    GLOBAL LOCAL HEADER UPPER LOAD).
Qed.
Theorem {name}_raw_whole_source_progress : exists F : region_progress {name}_raw_whole_source, True.
Proof. eapply checked_double_initialized_raw_nest_region_progress; exact {name}_raw_whole_compiles. Qed.
''')
        endpoints += [name + suffix for suffix in ("_raw_whole_compiles", "_raw_canonical_execution",
                                                    "_raw_whole_source_model", "_raw_whole_source_progress")]
    parts += ["Print Assumptions " + name + "." for name in endpoints]
    return "\n".join(parts) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    baseline = json.loads((canonical.WORK / "report.json").read_text())
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
    for (case, *_), (_, _, _, raw_module) in zip(exported.FIXTURES, FIXTURES):
        source = permitted(exported.WORK / case / (raw_module + ".v"))
        if source.with_suffix(".vo").exists():
            continue
        argv = ["rocq", "compile", *flags(), str(source)]
        with (attempts / (args.attempt + "-" + raw_module + ".log")).open("x") as log:
            run = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        (attempts / (args.attempt + "-" + raw_module + ".json")).open("x").write(json.dumps(
            {"command": argv, "source_sha256": sha(source), "returncode": run.returncode}, indent=2) + "\n")
        if run.returncode:
            raise ValueError("Raw AST compilation failed: " + raw_module)
    source = WORK / "OriginalInitializedDoubleRawNests.v"
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
    paths = [Path(__file__), canonical.WORK / "report.json", exported.WORK / "report.json"]
    paths += [path for path in WORK.rglob("*") if path.is_file()]
    paths += [exported.WORK / case / (module + suffix) for (case, *_), (_, _, _, module) in
              zip(exported.FIXTURES, FIXTURES) for suffix in (".v", ".vo")]
    for path in paths:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "compiled", "kind": "actual-literal-initialized-double-nest-source-bindings",
              "actual_original_cases": ["mxv", "matmul-init"],
              "literal_frontend_source_model_finite_iff": True,
              "literal_small_step_source_progress_independent_of_accepted_count": True,
              "entry_header_load_receipt_still_logical_premise": True,
              "new_guard_compiler_or_native_optimized_case": False, "bindings": bindings}
    (WORK / "report.json").open("x").write(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
