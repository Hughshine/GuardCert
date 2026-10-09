"""Verify real Pluto/proved double-pipeline acceptance and refusal, with immutable receipts."""

import argparse
import json
import subprocess
import time

import audit_original_matmul_prepared as proof
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/original-matmul/prepared-native-check-v1"
GOOD = ROOT / "build/original-matmul/prepared-receipt-native-attempts/dense-array-return-receipt-v2"
OLD = ROOT / "build/original-matmul/prepared-native-attempts/actual-source-double-extraction-v1"
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
        raise ValueError("Wrong pipeline-probe acceptance scope")
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
        raise ValueError("Successful or rejected run checkpoint is preserved; use a successor")
    baseline = proof.validate()
    good = bound_report(GOOD / "report.json")
    old = bound_report(OLD / "report.json")
    pluto = bound_report(PLUTO_REPORT)
    binary = ROOT / "build/polyhedral-pipeline/pluto-source/tool/pluto"
    if sha(binary) != pluto["bindings"][str(binary.relative_to(ROOT))]:
        raise ValueError("Wrong scheduler binary")
    WORK.mkdir()
    records = []
    for mode in ["identity", "affine", "reverse", "malformed", "refuse"]:
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
        if mode in {"identity", "affine"}:
            if not result["original_double_instructions_retained"]:
                raise ValueError("Generated candidate changed the original double instruction")
            generated = (output / "generated.loop").read_text()
            expected_args = "args=(v2,v0,v1)" if mode == "affine" else "args=(v2,v1,v0)"
            if expected_args not in generated or result["model_changed"] != (mode == "affine"):
                raise ValueError(f"Wrong generated iterator order: {mode}")
        if mode == "affine":
            log = (output / "scheduler.log").read_text()
            if "T(S1): (i_0, i_2, i_1)" not in log or not result["generated_Loop_changed"]:
                raise ValueError("Real affine transformation missing")
        if mode == "reverse" and not (output / "proposed.model").exists():
            raise ValueError("Reverse proposal never reached the dependency validator")
        if mode == "malformed" and not (output / "import-refusal.txt").exists():
            raise ValueError("Malformed proposal was not refused by the importer")

    # Preserve and reproduce the original probe's post-scheduler transport bug.
    output = WORK / "old-dense-return-rejection"
    argv = ["/usr/bin/timeout", "120", str(ROOT / old["executable"]), str(binary), "identity", str(output)]
    run = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
    (WORK / "old-dense-return.stdout").write_text(run.stdout)
    (WORK / "old-dense-return.stderr").write_text(run.stderr)
    if run.returncode != 2 or "Not_found" not in run.stderr or not (output / "before.scop.afterscheduling.scop").exists():
        raise ValueError("Original dense-array diagnostic failure was not reproduced")
    records.append({"mode": "old-dense-return-rejection", "command": argv, "returncode": run.returncode,
                    "expected_failure": True, "reason": "returned dense array IDs cannot be re-exported with sparse source IDs"})

    bindings = dict(baseline["bindings"])
    bindings.update(good["bindings"])
    bindings.update(old["bindings"])
    bindings.update(pluto["bindings"])
    for path in [proof.WORK / "report.json", GOOD / "report.json", OLD / "report.json",
                 PLUTO_REPORT, __file__, *WORK.rglob("*")]:
        from pathlib import Path
        path = Path(path)
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "validated", "kind": "actual-original-matmul-real-Pluto-typed-prepared-pipeline",
              "runs": records, "real_affine_schedule_i_j_k_to_i_k_j": True,
              "original_IEEE_double_instruction_tree_retained": True,
              "real_extractor_validator_and_prepared_codegen_executed": True,
              "reverse_dependency_proposal_refused": True, "malformed_import_refused": True,
              "external_refusal_preserved": True, "prior_probe_transport_failure_reproduced": True,
              "safe_guard_or_candidate_Clight_lowering_installed": False,
              "source_user_entry_premises_automatically_produced": False,
              "fixed_parameter_source_candidate_execution_bridge_complete": False,
              "selected_compiler_connected": False, "new_native_optimized_case": False,
              "complete_program_Csem_to_Asm_endpoint_added": False, "full_goal_complete": False,
              "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    validate()
    print(json.dumps({"status": "validated", "runs": len(records), "bound_files": len(bindings),
                      "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
