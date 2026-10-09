"""Check actual Pluto receipts and extracted candidate/guarded Clight AST emission."""

import argparse
import json
from pathlib import Path
import subprocess
import time

import audit_original_matmul_double_lowering as proof
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/original-matmul/double-lowering-native-check-v1"
GOOD = ROOT / "build/original-matmul/double-lowering-native-attempts/actual-tensor-clight-v1"
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
        raise ValueError("Wrong Clight-emission probe scope")
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
        raise ValueError("Existing checkpoint is preserved; use a successor")
    baseline = proof.validate()
    good = bound_report(GOOD / "report.json")
    pluto = bound_report(PLUTO_REPORT)
    binary = ROOT / "build/polyhedral-pipeline/pluto-source/tool/pluto"
    if sha(binary) != pluto["bindings"][str(binary.relative_to(ROOT))]:
        raise ValueError("Wrong scheduler binary")
    WORK.mkdir()
    records = []
    try:
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
                raise ValueError(f"Native probe failed: {mode}; {run.stderr}")
            result = json.loads((output / "result.json").read_text())
            record["result"] = result
            accepted = mode in {"identity", "affine"}
            if result["status"] != ("accepted" if accepted else "refused") or not result["alarm_free"] or result["scheduler_calls"] != 1:
                raise ValueError(f"Wrong pipeline result: {mode}")
            if not result["final_generated_Loop_checker_in_executable"] or result["C_compiler_or_whole_program_installation"] or result["Clight_statement_execution"]:
                raise ValueError("Wrong executable scope marker")
            if result["actual_candidate_Clight_lowered"] != accepted or result["actual_guarded_Clight_emitted"] != accepted:
                raise ValueError(f"Actual Clight lowering/emission disagrees: {mode}")
            for filename in ["candidate.clight.bin", "guarded.clight.bin"]:
                artifact = output / filename
                if artifact.exists() != accepted or (accepted and artifact.stat().st_size == 0):
                    raise ValueError(f"Wrong actual AST artifact: {mode}/{filename}")
            if accepted:
                if not result["original_double_instructions_retained"]:
                    raise ValueError("Candidate changed the original double instruction")
                generated = (output / "generated.loop").read_text()
                expected_args = "args=(v2,v0,v1)" if mode == "affine" else "args=(v2,v1,v0)"
                if expected_args not in generated or result["model_changed"] != (mode == "affine"):
                    raise ValueError(f"Wrong generated iterator order: {mode}")
            if mode in {"affine", "wrong-witness"} and "T(S1): (i_0, i_2, i_1)" not in (output / "scheduler.log").read_text():
                raise ValueError("Real Pluto interchange missing")
            if mode in {"reverse", "wrong-witness"} and not (output / "proposed.model").exists():
                raise ValueError("Proposal did not reach the checked pipeline")
            if mode == "malformed" and not (output / "import-refusal.txt").exists():
                raise ValueError("Malformed proposal did not reach the importer")
    except Exception as error:
        (WORK / "rejection.json").write_text(json.dumps({"status": "rejected", "error": str(error), "runs": records}, indent=2)+"\n")
        raise
    bindings = dict(baseline["bindings"])
    bindings.update(good["bindings"])
    bindings.update(pluto["bindings"])
    for path in [proof.WORK / "report.json", GOOD / "report.json", PLUTO_REPORT,
                 Path(__file__), *WORK.rglob("*")]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "validated", "kind": "actual-matmul-extracted-candidate-and-guarded-Clight-emission",
              "runs": records, "real_affine_schedule_i_j_k_to_i_k_j": True,
              "original_IEEE_double_instruction_tree_retained": True,
              "actual_final_candidate_checks_and_Clight_lowering": True,
              "guarded_AST_contains_actual_capture_candidate_exit_and_original_fallback": True,
              "wrong_coordinate_witness_reverse_malformed_and_external_refusals_preserved": True,
              "candidate_Clight_execution_proved": True,
              "native_Clight_statement_or_C_Asm_execution": False,
              "source_total_progress_or_divergence_proved": False,
              "selected_compiler_connected": False, "new_native_optimized_case": False,
              "complete_program_Csem_to_Asm_endpoint_added": False, "new_cost_results": False,
              "full_goal_complete": False, "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    validate()
    print(json.dumps({"status": "validated", "runs": len(records), "bound_files": len(bindings),
                      "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
