"""Bind initialized tiling, refusal-resource repair and separately scoped corpus attempts."""
import argparse
import json
from pathlib import Path

import audit_initialized_double_tiled_stable_installation as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked

OUTPUT = ROOT / "docs/initialized-double-tiling.json"
BASE = "build/initialized-double-tiling/"
REPORTS = {
    "compiler_before_resource_repair": BASE + "compiler-attempts/native-v1/report.json",
    "compiler": BASE + "compiler-attempts/native-v2/report.json",
    "initial_originals": BASE + "original-attempts/originals-v1/report.json",
    "initial_matrix": BASE + "original-attempts/original-matrix-v1/report.json",
    "initial_contexts": BASE + "check-attempts/contexts-v1/report.json",
    "initial_public_mixed_configuration": BASE + "public-attempts/public-v1/report.json",
    "initial_public_resource_collision": BASE + "public-attempts/public-v2/report.json",
    "initial_paths_sandbox_refusal": BASE + "path-attempts/paths-v1/report.json",
    "initial_paths": BASE + "path-attempts/paths-v2/report.json",
    "matrix_command_error": BASE + "original-attempts/stable-matrix-v1/report.json",
    "matrix": BASE + "original-attempts/stable-matrix-v2/report.json",
    "contexts": BASE + "check-attempts/stable-contexts-v1/report.json",
    "public": BASE + "public-attempts/stable-public-v1/report.json",
    "paths": BASE + "path-attempts/stable-paths-v1/report.json",
    "retained_command_error": "build/double-tiling/original-attempts/stable-initialized-retained-v1/report.json",
    "retained_reductions": "build/double-tiling/original-attempts/stable-initialized-retained-v2/report.json",
    "preceding_full_corpus": "build/benchmark-alignment/reindexed-tiled-attempts/corpus-v1/report.json",
    "high_rank_witness_retry": "build/benchmark-alignment/reindexed-tiled-attempts/initialized-tce-axes10-v1/report.json",
}


def schedules(path):
    lines = [line.split("#", 1)[0].strip() for line in permitted(path).read_text().splitlines()]
    lines = [line for line in lines if line]
    result = []
    for start, name in enumerate(lines):
        if name != "SCATTERING":
            continue
        metadata = list(map(int, lines[start + 1].split()))
        count, width, outputs, inputs, locals_, params = metadata
        rows = [list(map(int, line.split())) for line in lines[start + 2:start + 2 + count]]
        if len(rows) != count or any(len(row) != width for row in rows) or locals_ or count != outputs:
            raise ValueError("Expected explicit recorded schedule")
        expressions = [None] * outputs
        for row in rows:
            coefficients = row[1:1 + outputs]
            if row[0] or coefficients.count(-1) != 1 or any(value not in (-1, 0) for value in coefficients):
                raise ValueError("Expected one diagonal output per schedule row")
            expressions[coefficients.index(-1)] = row[1 + outputs:]
        if any(expression is None for expression in expressions):
            raise ValueError("Missing schedule expression")
        result.append({"inputs": inputs, "parameters": params, "rows": expressions})
    if not result:
        raise ValueError("Missing actual phase schedule")
    return result


def summarize():
    certificate = proof.validate()
    bindings = dict(certificate["bindings"])
    bindings[str((proof.WORK / "report.json").relative_to(ROOT))] = sha(proof.WORK / "report.json")
    reports = {name: checked(permitted(ROOT / path), bindings) for name, path in REPORTS.items()}
    failures = {"initial_public_mixed_configuration", "initial_public_resource_collision", "initial_paths_sandbox_refusal",
                "matrix_command_error", "retained_command_error"}
    diagnostics = {"preceding_full_corpus", "high_rank_witness_retry"}
    for name, report in reports.items():
        expected = ("built" if name.startswith("compiler") else "rejected" if name in failures
                    else "diagnostic_complete" if name in diagnostics else "passed")
        if report["status"] != expected:
            raise ValueError("Unexpected attempt status: " + name)
    if reports["compiler"]["whole_program_entrypoint"] != proof.ENTRY:
        raise ValueError("Wrong final extracted entry")
    for name, field, count in [("matrix", "results", 10), ("contexts", "cases", 20),
                               ("public", "cases", 7), ("paths", "cases", 6),
                               ("retained_reductions", "results", 10)]:
        rows = reports[name][field]
        if len(rows) != count or not all(row["passed"] for row in rows):
            raise ValueError("Incomplete final acceptance: " + name)
    for name in ["initial_public_mixed_configuration", "initial_public_resource_collision"]:
        rows = reports[name]["cases"]
        if sum(row["passed"] for row in rows) != 6 or not all(row["digest_matches_original_GCC"] for row in rows):
            raise ValueError("Missing preserved installation-only failure")
    for name in ["matrix_command_error", "retained_command_error"]:
        if len(reports[name]["results"]) != 2 or not all(row["native_match"] for row in reports[name]["results"]):
            raise ValueError("Missing preserved CLI mode-list error")
    stages = {}
    for row in reports["matrix"]["results"]:
        if row["mode"] != "tile":
            continue
        if row["installed_phase_calls_adaptations"] != [1, 1, 1]:
            raise ValueError("Missing installed initialized tiling")
        directory = permitted(ROOT / row["actual_phase_directories"][0])
        command = (directory / "command.txt").read_text().splitlines()
        if "--identity" in command or "--intratileopt" not in command or "--tile" not in command:
            raise ValueError("Wrong actual phase options")
        stages[row["case"]] = {
            "directory": str(directory.relative_to(ROOT)),
            "before": schedules(directory / "before.scop"),
            "middle": schedules(directory / "before.scop.midtransform.scop"),
            "after": schedules(directory / "before.scop.afterscheduling.scop"),
        }
        if stages[row["case"]]["before"] == stages[row["case"]]["middle"]:
            raise ValueError("Missing real initial schedule change")
    corpus = reports["preceding_full_corpus"]
    if not corpus["full_corpus_attempted"] or corpus["original_cases_attempted"] != 62 or len(corpus["results"]) != 64:
        raise ValueError("Missing complete preceding corpus")
    originals = {row["case"]: row["configurations"]["tile"] for row in corpus["results"] if row["variant"] == "original"}
    adapted = [row["configurations"]["tile"] for row in corpus["results"] if row["variant"] != "original"]
    timeouts = {case: data["compiler"]["elapsed_seconds"] for case, data in originals.items() if data["compiler"]["timeout"]}
    if set(timeouts) != {"polynomial"} or originals["polynomial"]["actual_raw_candidates"] != 0:
        raise ValueError("Missing actual compiler timeout before raw generation")
    matches = sum(data["status"] == "native_match" for data in originals.values())
    sites = sum((data["installed"] or [0, 0, 0])[2] for data in originals.values())
    refused = sorted(case for case, data in originals.items()
                     if not data["compiler"]["timeout"] and data["status"] != "native_match")
    no_phase = sum(data["status"] == "native_match" and not data["tiling_phase_calls"] for data in originals.values())
    no_install_after_phase = sorted(case for case, data in originals.items()
                                   if data["status"] == "native_match" and data["tiling_phase_calls"]
                                   and not (data["installed"] or [0, 0, 0])[2])
    if (matches != 59 or sites != 22 or len(corpus["installed_cases"]) != 9 or len(adapted) != 2
            or not all(data["status"] == "native_match" for data in adapted)
            or refused != ["corcol3", "pca"] or no_phase != 48 or no_install_after_phase != ["tce", "tricky3"]):
        raise ValueError("Wrong preceding corpus accounting")
    retry = reports["high_rank_witness_retry"]
    high = retry["results"][0]["configurations"]["tile"]
    if (retry["full_corpus_attempted"] or retry["original_cases_attempted"] != 1 or
            retry["witness_axes_override"] != 10 or retry["installed_cases"] != ["tce"] or
            high["installed"][2] != 4 or not high["digest_matches_original_GCC"]):
        raise ValueError("Wrong focused high-rank retry")
    for path in [Path(__file__), ROOT / "docs/initialized-double-tiling-proof.json",
                 ROOT / "docs/initialized-double-tiling-stable-proof.json"]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    return {
        "status": "validated", "narrative_reference": "8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9",
        "compiler_entrypoint": proof.ENTRY, "compiler_theorem": proof.ENTRY + "_correct",
        "new_modules": certificate["new_modules"], "source_lines": certificate["new_source_lines"],
        "audited_endpoints": len(certificate["endpoints"]), "closed_endpoints": certificate["closed_endpoints"],
        "reachable_sources": certificate["reachable_source_count"], "maximum_inherited_globals": 42,
        "additional_global_axioms": [], "kernel_and_host_laws_unchanged": True,
        "generic_composition_theorem_directly_invoked_by_this_guarded_execution": False,
        "factory_discharges_source_model_guard_frame_scope_and_public_exit_obligations": True,
        "source_users_supply_semantic_callbacks": False,
        "empty_tiling_tables_preserve_program_and_do_not_allocate_private_temps": True,
        "current_intermediate_program_evidence_recomputed_at_each_pass": True,
        "condition": {"common_global_I64_bound": True, "original_accepting_range": [0, 98],
                      "extent104_accepting_range": [0, 102], "runtime_alias_test": False,
                      "private_capture_not_whole_state_readonly": True, "weakest_or_optimal_condition_claimed": False},
        "original_installed_tiled_sites": {"mxv": 1, "matmul-init": 1}, "actual_phase_schedules": stages,
        "final_checks": {"original_modes": 10, "contexts": 20, "public_and_legacy": 7,
                         "retained_reduction_modes": 10, "unchanged_assembly_paths": 6},
        "guard_paths": {row["case"]: row["actual"] for row in reports["paths"]["cases"]},
        "public_controls": {row["case"]: row["expected_public_controls"] for row in reports["public"]["cases"] if "expected_public_controls" in row},
        "preceding_complete_corpus": {"entrypoint": corpus["compiler_entrypoint"], "originals": 62,
            "raw_native_matches": matches, "adapted_native_matches": 2,
            "raw_frontend_refusals": refused, "compiler_timeouts": timeouts,
            "installed_original_cases": 9, "installed_sites": sites,
            "compiled_originals_without_tiling_phase_calls": no_phase,
            "compiled_phase_called_without_installation": no_install_after_phase,
            "all_matches_are_not_installed_or_nonidentity_effects": True},
        "focused_high_rank_retry": {"entrypoint": retry["compiler_entrypoint"], "case": "tce",
            "private_temporaries": 32, "witness_axes": 10, "installed_sites": 4,
            "compiler_seconds": high["compiler"]["elapsed_seconds"], "native_matches_original_GCC": True,
            "default_six_axis_policy_not_repaired": True, "complete_corpus_replay": False},
        "complete_corpus_replayed_with_final_resource_repair_build": False,
        "controlled_cost_or_profitability_established": False, "full_goal_complete": False,
        "preserved_rejected_reports": sorted(failures), "reports": REPORTS, "bindings": bindings,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    result = summarize()
    if args.validate:
        if json.loads(OUTPUT.read_text()) != result:
            raise ValueError("Changed summary or bound evidence")
    else:
        OUTPUT.open("x").write(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "validated", "reports": len(REPORTS), "bindings": len(result["bindings"]),
                      "summary_sha256": sha(OUTPUT)}))


if __name__ == "__main__":
    main()
