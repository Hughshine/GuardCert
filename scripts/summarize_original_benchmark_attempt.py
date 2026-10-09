"""Bind and summarize the first original-program attempts without claiming optimization."""

import argparse
import json
from pathlib import Path

from benchmark_polcert_source_probe import ROOT, sha
from audit_word_store_sequence import permitted

BASE = ROOT / "build/benchmark-alignment"


def checked(path, bindings):
    value = json.loads(path.read_text())
    for name, digest in value.get("bindings", {}).items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError(f"Changed checkpoint binding: {name}")
        if name in bindings and bindings[name] != digest:
            raise ValueError(f"Inconsistent parent bindings: {name}")
        bindings[name] = digest
    bindings[str(path.relative_to(ROOT))] = sha(path)
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, default=BASE / "stage-v2")
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    work = args.work.resolve()
    if not work.is_relative_to(BASE):
        raise ValueError("Checkpoint must stay in benchmark-alignment")
    if args.validate:
        bindings = {}
        result = checked(work / "report.json", bindings)
        print(json.dumps({"status": "bindings_validated", "files": len(bindings),
                          "report_sha256": sha(work / "report.json"),
                          "requested_optimized_corpus_cases": result["requested_optimized_corpus_cases"]}))
        return
    if work.exists():
        raise ValueError("Use a new summary checkpoint")
    paths = {"corpus_raw": BASE / "probe-v1/report.json",
             "corpus_analysis": BASE / "probe-analysis-v1/report.json",
             "harness_compatibility": BASE / "harness-compat-v1/report.json",
             "double_value_proof": BASE / "floating-proof-v1/report.json",
             "source_materialization": BASE / "source-materialization.json",
             "BT_reproducer": BASE / "bt-probe-v3/report.json"}
    bindings = {}
    reports = {name: checked(path, bindings) for name, path in paths.items()}
    raw, analysis, compat, proof, bt = (reports[name] for name in
        ["corpus_raw", "corpus_analysis", "harness_compatibility", "double_value_proof", "BT_reproducer"])
    inventory = checked(ROOT / "docs/benchmark-alignment-inventory.json", bindings)
    names = {row["case"] for row in inventory["polcert"]["cases"]}
    if len(names) != 62 or {row["case"] for row in raw["results"]} != names:
        raise ValueError("Complete corpus not attempted")
    for corpus in reports["source_materialization"]["corpora"]:
        for row in corpus["files"]:
            path = permitted(ROOT / row["path"])
            if sha(path) != row["sha256"]:
                raise ValueError(f"Changed materialized original source: {path}")
            bindings[row["path"]] = row["sha256"]
    initial_matches = sum(row["status"] == "native_match" for case in raw["results"] for row in case["configurations"].values())
    repaired = sum(row["native_original_reference_match"] for case in compat["cases"] for row in case["configurations"].values())
    unchanged = analysis["active_unchanged_clight_no_pipeline_pairs"] + sum(
        row["emitted_clight_equals_disabled"] and not row["pipeline_files"]
        for case in compat["cases"] for mode, row in case["configurations"].items() if mode != "disabled")
    if initial_matches != 180 or repaired != 6 or unchanged != 124:
        raise ValueError("Unexpected first-attempt observations")
    if proof["additional_global_axioms"] or proof["selected_compiler_connected"]:
        raise ValueError("Unexpected double proof scope")
    bt_rows = []
    for mode, row in bt["configurations"].items():
        if len(row["units"]) != 17 or not row["NPB_verification_passed"] or not row["ten_numerical_rows_match_GCC_baseline"]:
            raise ValueError("Original BT reproduction failed")
        bt_rows.append({"mode": mode, "compiled_units": len(row["units"]),
                        "NPB_verification_passed": row["NPB_verification_passed"],
                        "ten_numerical_rows_match_GCC_baseline": row["ten_numerical_rows_match_GCC_baseline"],
                        "rhs_Clight_unchanged": row["rhs_Clight_unchanged"],
                        "selected_rhs_regions": row["selected_rhs_regions"],
                        "phase_artifact_count": len(row["phase_artifacts"])})
    lock = checked(ROOT / "toolchain.lock.json", bindings)
    stamp_path = ROOT / "vendor/CompCert/.guard-source.json"
    if json.loads(stamp_path.read_text()) != lock["compcert"]:
        raise ValueError("CompCert source pin differs from lock")
    for path in [Path(__file__), ROOT / "scripts/materialize_benchmark_source_pins.py", stamp_path,
                 BASE / "bt-probe-v2/rejected-runner.py", BASE / "bt-probe-v2/rejection.json"]:
        bindings[str(path.relative_to(ROOT))] = sha(path)
    actual_globals = sorted(set().union(*map(set, proof["endpoint_assumptions"].values())))
    result = {"status": "validated_partial_progress",
              "kind": "original-benchmark-baseline-and-double-data-foundation",
              "case_attempts": len(names), "initial_configuration_attempts": analysis["configuration_attempts"],
              "initial_native_matches": initial_matches,
              "initial_frontend_refused_cases": analysis["frontend_refused_cases"],
              "explicit_constant_initializer_repairs": len(compat["cases"]), "repaired_native_comparisons": repaired,
              "corpus_cases_with_matching_modeled_state_after_disclosed_adaptation": len(names),
              "active_corpus_Clight_unchanged": unchanged, "requested_optimized_corpus_cases": 0,
              "corpus_input_tier": "pinned smoke; literal sizes retained including 10000-by-10000 fusion3",
              "corpus_observation": "digest of every modeled scalar and array element; not all C machine state and not a universal proof",
              "compatibility_environment_metadata": "parent records inherited environment; helper overrides GUARDCERT_PIPELINE_DUMP to its new per-mode phases directory",
              "BT_configurations": bt_rows, "BT_source_tier": "original serial NPB Class S, double, 12x12x12,60iterations",
              "BT_observation": bt["observation"], "BT_optimized": False,
              "BT_reproducer_repeat_is_new_coverage": False,
              "BT_rejected_reproducer": "bt-probe-v2 omitted subprocess environment; archived and corrected in bt-probe-v3",
              "double_instruction_source_lines": proof["new_source_lines"],
              "double_instruction_endpoints": len(proof["endpoints"]),
              "double_instruction_max_inherited_globals": max(map(len, proof["endpoint_assumptions"].values())),
              "double_instruction_union_inherited_globals": actual_globals,
              "double_instruction_additional_global_axioms": proof["additional_global_axioms"],
              "double_instruction_bound_files": len(proof["bindings"]),
              "double_instruction_expression_direction": proof["expression_direction"],
              "double_instruction_original_source_decode_installed": False,
              "double_instruction_Mfloat64_address_guard_installed": False,
              "double_instruction_selected_compiler_installed": False,
              "actual_toolchain_source_pin": lock["compcert"],
              "reported_compiler_version": "3.17 (upstream v3.18 VERSION metadata)",
              "next_required_chain": "actual matmul double body decode and Mfloat64/global view; int64 controls; typed validators/codegen/guard/factory/host/native together",
              "guard_cost_or_profitability_measured": False, "full_goal_complete": False,
              "reports": {name: {"path": str(path.relative_to(ROOT)), "sha256": sha(path)} for name, path in paths.items()},
              "bindings": bindings}
    work.mkdir()
    (work / "report.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k not in ["bindings", "reports", "actual_toolchain_source_pin"]}))


if __name__ == "__main__":
    main()
