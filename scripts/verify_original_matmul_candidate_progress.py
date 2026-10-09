"""Check the actual final generated-loop pipeline, including a wrong coordinate witness."""

import argparse
import json
from pathlib import Path
import subprocess
import time

import audit_original_matmul_candidate_progress as proof
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/original-matmul/candidate-progress-native-check-v1"
GOOD = ROOT / "build/original-matmul/candidate-progress-native-attempts/scoped-checker-marker-v2"
OLD = ROOT / "build/original-matmul/candidate-progress-native-attempts/actual-final-candidate-v1"
DIAGNOSTICS = ROOT / "build/original-matmul/candidate-progress-native-diagnostics/v1"
PLUTO_REPORT = ROOT / "build/polyhedral-pipeline/pluto-build.json"


def bound_report(path):
    report = json.loads(path.read_text())
    for name, digest in report["bindings"].items():
        if sha(ROOT / name) != digest:
            raise ValueError(f"Changed bound input: {name}")
    return report


def validate():
    report = bound_report(WORK / "report.json")
    if report["status"] != "validated" or report["new_native_optimized_case"]:
        raise ValueError("Wrong final-checker probe scope")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate:
        report = validate()
        print(json.dumps({"status": "validated", "runs": len(report["runs"]),
                          "report_sha256": sha(WORK / "report.json")}))
        return
    if WORK.exists():
        raise ValueError("Existing run checkpoint is preserved; use a successor")
    baseline = proof.validate()
    good = bound_report(GOOD / "report.json")
    old = bound_report(OLD / "report.json")
    pluto = bound_report(PLUTO_REPORT)
    binary = ROOT / "build/polyhedral-pipeline/pluto-source/tool/pluto"
    if sha(binary) != pluto["bindings"][str(binary.relative_to(ROOT))]:
        raise ValueError("Wrong scheduler binary")
    WORK.mkdir()
    records = []
    for mode in ["identity", "affine", "wrong-witness", "reverse", "malformed", "refuse"]:
        output = WORK / mode
        argv = ["/usr/bin/timeout", "120", str(ROOT / good["executable"]), str(binary), mode, str(output)]
        started = time.monotonic()
        run = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
        (WORK / f"{mode}.stdout").write_text(run.stdout)
        (WORK / f"{mode}.stderr").write_text(run.stderr)
        record = {"mode": mode, "command": argv, "returncode": run.returncode,
                  "elapsed_seconds_diagnostic_only": time.monotonic()-started}
        records.append(record)
        if run.returncode:
            (WORK / "rejection.json").write_text(json.dumps({"status": "rejected", "runs": records}, indent=2)+"\n")
            raise ValueError(f"Native probe failed: {mode}; {run.stderr}")
        result = json.loads((output / "result.json").read_text())
        record["result"] = result
        expected = "accepted" if mode in {"identity", "affine"} else "refused"
        if result["status"] != expected or not result["alarm_free"] or result["scheduler_calls"] != 1:
            raise ValueError(f"Wrong acceptance/refusal result: {mode}")
        if not result["final_generated_Loop_checker_in_executable"] or result["C_compiler_or_whole_program_installation"]:
            raise ValueError("Wrong executable scope marker")
        if mode in {"identity", "affine"}:
            if not result["original_double_instructions_retained"]:
                raise ValueError("Candidate changed the original double instruction")
            generated = (output / "generated.loop").read_text()
            expected_args = "args=(v2,v0,v1)" if mode == "affine" else "args=(v2,v1,v0)"
            if expected_args not in generated or result["model_changed"] != (mode == "affine"):
                raise ValueError(f"Wrong generated iterator order: {mode}")
        if mode in {"affine", "wrong-witness"}:
            if "T(S1): (i_0, i_2, i_1)" not in (output / "scheduler.log").read_text():
                raise ValueError("Real affine transformation missing")
        if mode in {"reverse", "wrong-witness"} and not (output / "proposed.model").exists():
            raise ValueError("Proposal did not reach the checked pipeline")
        if mode == "malformed" and not (output / "import-refusal.txt").exists():
            raise ValueError("Malformed proposal was not refused by the importer")

    # The first executable's computation was correct, but a static output field
    # claimed the final checker ran even when external refusal stopped earlier.
    output = WORK / "old-marker-refusal"
    argv = ["/usr/bin/timeout", "120", str(ROOT / old["executable"]), str(binary), "refuse", str(output)]
    run = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
    (WORK / "old-marker.stdout").write_text(run.stdout)
    (WORK / "old-marker.stderr").write_text(run.stderr)
    result = json.loads((output / "result.json").read_text())
    if run.returncode or result["status"] != "refused" or not result["final_generated_Loop_checker_executed"]:
        raise ValueError("First probe's inaccurate static marker was not reproduced")
    records.append({"mode": "old-marker-refusal", "command": argv, "returncode": run.returncode,
                    "expected_diagnostic_scope_failure": True,
                    "reason": "a static field said final-checker-executed despite earlier external refusal"})
    bindings = dict(baseline["bindings"])
    bindings.update(good["bindings"])
    bindings.update(old["bindings"])
    bindings.update(pluto["bindings"])
    for path in [proof.WORK / "report.json", GOOD / "report.json", OLD / "report.json",
                 PLUTO_REPORT, Path(__file__), *DIAGNOSTICS.rglob("*"), *WORK.rglob("*")]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "validated", "kind": "actual-matmul-final-generated-loop-progress-checker",
              "runs": records, "real_affine_schedule_i_j_k_to_i_k_j": True,
              "original_IEEE_double_instruction_tree_retained": True,
              "actual_final_candidate_extraction_domain_coordinate_and_dependence_checks": True,
              "wrong_coordinate_witness_refused": True,
              "reverse_malformed_and_external_refusals_preserved": True,
              "prior_inaccurate_scope_marker_reproduced_and_corrected": True,
              "candidate_model_forward_progress_proved": True,
              "native_source_or_candidate_model_execution": False,
              "candidate_Clight_lowering_complete": False,
              "source_total_progress_or_divergence_proved": False,
              "selected_compiler_connected": False, "new_native_optimized_case": False,
              "complete_program_Csem_to_Asm_endpoint_added": False, "full_goal_complete": False,
              "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    validate()
    print(json.dumps({"status": "validated", "runs": len(records), "bound_files": len(bindings),
                      "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
