"""Bind real Pluto acceptance/refusal probes to the actual initialized sources."""

import argparse
import json
from pathlib import Path
import subprocess
import time

import audit_initialized_double_uniform_pipeline as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/double-initialized-nests/uniform-native-check-v1"
BUILD = ROOT / "build/double-initialized-nests/native-attempts/uniform-native-v2/report.json"
PLUTO = ROOT / "build/polyhedral-pipeline/pluto-build.json"
MATRIX = [(case, mode, witness) for case in ("mxv", "matmul-init") for mode, witness in
          [("identity", "none"), ("affine", "none"), ("affine", "0"), ("affine", "1"),
           ("reverse", "none"), ("malformed", "none"), ("refuse", "none")]]


def bound_report(path, status):
    report = json.loads(permitted(path).read_text())
    if report["status"] != status:
        raise ValueError("Unexpected report status: " + str(path))
    for name, digest in report["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError("Changed input: " + name)
    return report


def validate():
    report = json.loads((WORK / "report.json").read_text())
    if report["status"] != "validated" or report["whole_program_compiler"]:
        raise ValueError("Invalid pipeline probe checkpoint")
    for name, digest in report["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError("Changed evidence: " + name)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate:
        report = validate()
        print(json.dumps({"status": "validated", "checks": len(report["checks"]),
                          "bindings": len(report["bindings"]), "report_sha256": sha(WORK / "report.json")}))
        return
    if (WORK / "report.json").exists():
        raise ValueError("Successful checkpoint is frozen")
    baseline = proof.validate()
    native = bound_report(BUILD, "built")
    pluto = bound_report(PLUTO, "built")
    executable, scheduler = ROOT / native["executable"], ROOT / pluto["binary"]
    WORK.mkdir(parents=True, exist_ok=True)
    checks = []
    for case, mode, witness in MATRIX:
        name = "-".join((case, mode, witness))
        output = WORK / name
        execution = WORK / (name + ".execution.json")
        argv = [str(executable), case, str(scheduler), mode, witness, str(output)]
        if execution.exists():
            receipt = json.loads(execution.read_text())
            if receipt["command"] != argv:
                raise ValueError("Changed existing invocation: " + name)
        else:
            if output.exists():
                raise ValueError("Incomplete attempt must be retained separately: " + name)
            start = time.monotonic()
            try:
                run = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True, timeout=60)
                receipt = {"command": argv, "returncode": run.returncode, "stdout": run.stdout,
                           "stderr": run.stderr, "seconds": time.monotonic()-start, "timed_out": False}
            except subprocess.TimeoutExpired as error:
                receipt = {"command": argv, "returncode": None,
                           "stdout": (error.stdout or b"").decode(), "stderr": (error.stderr or b"").decode(),
                           "seconds": time.monotonic()-start, "timed_out": True}
            execution.open("x").write(json.dumps(receipt, indent=2)+"\n")
        result_path = output / "result.json"
        result = json.loads(result_path.read_text()) if result_path.exists() else None
        if receipt["timed_out"]:
            stage = "after-codegen-before-final-result" if (output / "phase-generated.loop").exists() else "before-codegen-result"
        elif receipt["returncode"]:
            stage = "process-error"
        elif result is None:
            raise ValueError("Missing successful process result: " + name)
        elif result["status"] == "accepted":
            if not all(result[key] for key in ["alarm_free", "phase_accepted", "final_checked",
                                               "original_double_instructions_retained"]):
                raise ValueError("Incomplete accepted candidate: " + name)
            stage = "accepted-final-candidate"
        else:
            stage = "final-check-refusal" if result["phase_accepted"] else "export-import-or-phase-refusal"
        if result is not None and mode in {"reverse", "malformed", "refuse"} and result["status"] != "refused":
            raise ValueError("Unsound diagnostic accepted: " + name)
        check = {"case": case, "mode": mode, "swap_witness": witness, "result": result,
                 "stage": stage, "execution": str(execution.relative_to(ROOT)), "seconds": receipt["seconds"],
                 "timed_out": receipt["timed_out"]}
        checks.append(check)
        print(name + ": " + stage, flush=True)
    for case in ("mxv", "matmul-init"):
        if not any(item["case"] == case and item["mode"] == "identity" and
                   item["stage"] == "accepted-final-candidate" for item in checks):
            raise ValueError("Original identity route must accept: " + case)
    bindings = dict(baseline["bindings"])
    for report in (native, pluto):
        bindings.update(report["bindings"])
    roots = [WORK, ROOT / "build/double-initialized-nests/native-check-v1",
             ROOT / "build/double-initialized-nests/native-attempts/literal-native-v1",
             ROOT / "build/double-initialized-nests/native-attempts/literal-native-v2",
             ROOT / "build/double-initialized-nests/native-attempts/uniform-native-v1"]
    for directory in roots:
        for path in directory.rglob("*"):
            if path.is_file():
                bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    for path in [Path(__file__), BUILD, PLUTO, proof.WORK / "report.json"]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "validated", "kind": "actual-initialized-source-real-Pluto-pipeline-probes",
              "checks": checks, "bindings": bindings,
              "accepted_final_candidates": sum(item["stage"] == "accepted-final-candidate" for item in checks),
              "refused_candidates": sum("refusal" in item["stage"] for item in checks),
              "timed_out_attempts": sum(item["timed_out"] for item in checks),
              "previous_coordinate_diagnostic_completed_refusals": 4,
              "previous_coordinate_diagnostic_interrupted_attempts": 1,
              "failed_native_builds_preserved": 2,
              "original_double_I64_array_source_model_requests": True,
              "actual_safe_entry_and_fixed_parameter_candidate_proofs_bound": True,
              "probe_executes_original_or_generated_C_or_assembly": False,
              "whole_program_compiler": False, "new_installed_original_corpus_cases": 0,
              "original_corpus_nonidentity_optimized_cases": 1,
              "guard_or_optimized_program_performance_measured": False, "full_goal_complete": False}
    (WORK / "report.json").open("x").write(json.dumps(report, indent=2)+"\n")
    validate()
    print(json.dumps({"status": "validated", "checks": len(checks),
                      "accepted": report["accepted_final_candidates"], "refused": report["refused_candidates"],
                      "timeouts": report["timed_out_attempts"], "bindings": len(bindings),
                      "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
