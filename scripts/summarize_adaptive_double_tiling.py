"""Bind the default-policy corpus replay and separately scoped codegen diagnostics."""
import argparse
import json
from pathlib import Path
import re

import audit_initialized_double_tiled_stable_installation as proof
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked
from summarize_initialized_double_tiling import schedules

OUTPUT = ROOT / "docs/adaptive-double-tiling.json"
REPORTS = {
    "adaptive_build_rejection": "build/adaptive-double-tiling/compiler-attempts/native-v1/rejection.json",
    "compiler": "build/adaptive-double-tiling/compiler-attempts/native-v2/report.json",
    "preceding_corpus": "build/benchmark-alignment/reindexed-tiled-attempts/corpus-v1/report.json",
    "corpus": "build/benchmark-alignment/adaptive-tiled-attempts/corpus-v1/report.json",
    "public": "build/initialized-double-tiling/public-attempts/adaptive-public-v1/report.json",
    "trace_precheck_rejection": "build/profiled-double-tiling/precheck-rejections/v1/report.json",
    "profiled_compiler": "build/profiled-double-tiling/compiler-attempts/native-v1/report.json",
    "profile": "build/benchmark-alignment/adaptive-tiled-attempts/profile-polynomial-v1/report.json",
    "compact_compiler": "build/profiled-double-tiling/compiler-attempts/native-v2/report.json",
    "compact_profile": "build/benchmark-alignment/adaptive-tiled-attempts/compact-profile-polynomial-v1/report.json",
    "codegen_compiler": "build/profiled-double-tiling/compiler-attempts/native-v3/report.json",
    "codegen_profile": "build/benchmark-alignment/adaptive-tiled-attempts/codegen-profile-polynomial-v1/report.json",
}
TRACE_ATTEMPTS = [
    ("GuardMemoryDoubleTiledPhaseTrace", "v1", 0),
    ("GuardMemoryDoubleCodegenTrace", "v1", 1),
    ("GuardMemoryDoubleCodegenTrace", "v2", 0),
    ("GuardMemoryDoubleTiledCodegenTrace", "v1", 1),
    ("GuardMemoryDoubleTiledCodegenTrace", "v2", 0),
]


def trace_summary(directory, configuration):
    text = permitted(directory / "compiler.stderr").read_text()
    durations, pending = [], {}
    for label, wall, cpu in re.findall(
            r'^GUARDCERT_PHASE label="guardcert-phase/([^\"]+)" wall=([0-9.]+) cpu=([0-9.]+)$', text, re.M):
        stage, event = label.rsplit("/", 1)
        if event == "begin":
            pending[stage] = (float(wall), float(cpu))
        elif event == "end" and stage in pending:
            started = pending.pop(stage)
            durations.append({"stage": stage, "wall_seconds": float(wall) - started[0],
                              "cpu_seconds": float(cpu) - started[1]})
    queries = re.findall(r'^GUARDCERT_ORACLE query=(\d+) event=begin constraints=(\d+) phase="([^\"]*)"$', text, re.M)
    additions = re.findall(r'^GUARDCERT_ORACLE_ADD batch=(\d+) input=(\d+) retained=(\d+) removed_total=(\d+)$', text, re.M)
    return {"status": configuration["status"], "installed": configuration["installed"],
            "compiler_wall_seconds": configuration["compiler"]["elapsed_seconds"],
            "completed_stages": durations, "uncompleted_stages": list(pending),
            "oracle_queries_begun": int(queries[-1][0]) if queries else 0,
            "maximum_oracle_input_constraints": max((int(row[1]) for row in queries), default=0),
            "last_oracle_event": configuration["last_oracle_event"],
            "last_add_proposal": list(map(int, additions[-1])) if additions else None,
            "raw_candidates": configuration["actual_raw_candidates"],
            "final_candidates": configuration["actual_final_candidates"]}


def summarize():
    certificate = proof.validate()
    bindings = dict(certificate["bindings"])
    bindings[str((proof.WORK / "report.json").relative_to(ROOT))] = sha(proof.WORK / "report.json")
    reports = {name: checked(permitted(ROOT / path), bindings) for name, path in REPORTS.items()}
    for name, report in reports.items():
        expected = ("built" if name.endswith("compiler") else "rejected" if name.endswith("rejection")
                    else "passed" if name == "public" else "diagnostic_complete")
        if report["status"] != expected:
            raise ValueError("Unexpected attempt status: " + name)
    for name in ["compiler", "profiled_compiler", "compact_compiler", "codegen_compiler"]:
        if reports[name]["whole_program_entrypoint"] != proof.ENTRY or not reports[name]["proof_and_entrypoint_unchanged"]:
            raise ValueError("Whole-program proof entry changed: " + name)
    corpus = reports["corpus"]
    if (not corpus["full_corpus_attempted"] or corpus["original_cases_attempted"] != 62
            or len(corpus["results"]) != 64 or corpus["private_count_override"] is not None
            or corpus["witness_axes_override"] is not None or corpus["native_failures"]):
        raise ValueError("Expected complete default-policy replay")
    raw = {row["case"]: row["configurations"]["tile"] for row in corpus["results"] if row["variant"] == "original"}
    adapted = [row["configurations"]["tile"] for row in corpus["results"] if row["variant"] != "original"]
    installed = {case: config["installed"][2] for case, config in raw.items() if config["installed"] and config["installed"][2]}
    timeouts = {case: config["compiler"]["elapsed_seconds"] for case, config in raw.items() if config["compiler"]["timeout"]}
    refusals = sorted(case for case, config in raw.items() if config["status"] == "frontend_or_compiler_refusal")
    no_phase = sum(config["status"] == "native_match" and not config["tiling_phase_calls"] for config in raw.values())
    phase_without_install = sorted(case for case, config in raw.items() if config["status"] == "native_match"
                                   and config["tiling_phase_calls"] and case not in installed)
    if (len(installed) != 13 or sum(installed.values()) != 29 or len(adapted) != 2
            or not all(config["status"] == "native_match" for config in adapted)
            or sum(config["status"] == "native_match" for config in raw.values()) != 59
            or refusals != ["corcol3", "pca"] or set(timeouts) != {"polynomial"}
            or no_phase != 45 or phase_without_install != ["tricky3"]):
        raise ValueError("Complete corpus accounting changed")
    policy = raw["tce"]["policy_trace"]
    if (installed["tce"] != 4 or len(policy) != 1 or "source_loop_depth=5 private_count=22 witness_axes=10" not in policy[0]
            or "private_override=false witness_override=false" not in policy[0]):
        raise ValueError("Default high-rank policy not observed")
    public = reports["public"]["cases"]
    if len(public) != 7 or not all(row["passed"] for row in public):
        raise ValueError("Public-exit and legacy regression incomplete")
    attempts, trace_globals, closed = [], set(), 0
    for stem, attempt, returncode in TRACE_ATTEMPTS:
        base = ROOT / "build/original-matmul/installation-attempts-v1" / (stem + "-" + attempt)
        metadata = json.loads(permitted(base.with_suffix(".json")).read_text())
        if metadata["returncode"] != returncode or metadata["source_sha256"] != sha(permitted(base.with_suffix(".v"))):
            raise ValueError("Changed proof attempt: " + str(base))
        for suffix in [".v", ".json", ".log"]:
            path = permitted(base.with_suffix(suffix)); bindings[str(path.relative_to(ROOT))] = sha(path)
        if returncode == 0:
            path = permitted(ROOT / "adapters/compcert-memory" / (stem + ".v"))
            if sha(path) != metadata["source_sha256"]:
                raise ValueError("Changed successful trace source")
            for asset in [path, permitted(path.with_suffix(".vo"))]:
                bindings[str(asset.relative_to(ROOT))] = sha(asset)
            log = permitted(base.with_suffix(".log")).read_text()
            trace_globals |= names(log); closed += log.count("Closed under the global context")
        attempts.append({"module": stem, "attempt": attempt, "returncode": returncode})
    if not trace_globals <= set(certificate["allowed_parent_globals"]) or closed != 1:
        raise ValueError("Unexpected trace proof assumptions")
    profiles = {}
    for name in ["profile", "compact_profile", "codegen_profile"]:
        report = reports[name]
        if report["full_corpus_attempted"] or report["original_cases_attempted"] != 2 or report["installed_cases"] != ["mvt"]:
            raise ValueError("Wrong focused profile scope: " + name)
        root = (ROOT / REPORTS[name]).parent
        profiles[name] = {}
        for row in report["results"]:
            config = row["configurations"]["tile"]
            profiles[name][row["case"]] = trace_summary(root / (row["case"] + "-original") / "tile", config)
        if (profiles[name]["mvt"]["status"] != "native_match" or profiles[name]["mvt"]["installed"][2] != 2
                or profiles[name]["polynomial"]["status"] != "compiler_timeout"
                or profiles[name]["polynomial"]["raw_candidates"] != 0):
            raise ValueError("Diagnostic or control changed: " + name)
    phases = {}
    for case in ["dct", "mxv", "matmul-init", "tce"]:
        directories = sorted((ROOT / REPORTS["corpus"]).parent.glob(case + "-original/tile/tiling-pipeline-*"))
        phases[case] = []
        for directory in directories:
            command = permitted(directory / "command.txt").read_text().splitlines()
            if "--identity" in command or "--tile" not in command or "--intratileopt" not in command:
                raise ValueError("Unexpected actual phase command")
            phases[case].append({"directory": str(directory.relative_to(ROOT)),
                                 "before": schedules(directory / "before.scop"),
                                 "middle": schedules(directory / "before.scop.midtransform.scop"),
                                 "after": schedules(directory / "before.scop.afterscheduling.scop")})
    bindings[str(Path(__file__).relative_to(ROOT))] = sha(Path(__file__))
    return {"status": "validated", "narrative_reference": "8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9",
            "compiler_entrypoint": proof.ENTRY, "compiler_theorem": proof.ENTRY + "_correct",
            "semantic_compiler_proof_unchanged": True, "kernel_and_host_laws_unchanged": True,
            "new_semantic_axioms": [], "source_users_supply_semantic_callbacks": False,
            "generic_kernel_composition_theorem_directly_invoked": False,
            "untrusted_input_policy": {"source_depth_scope": "all Csyntax function bodies",
                "candidate_depth_proposal": "(tiling enabled ? 2 : 1) * maximum source loop depth",
                "private_count_default": "max(16, 2 * candidate_depth + 2)",
                "witness_axes_default": "max(6, candidate_depth)",
                "minimum_or_universal_sufficiency_proved": False,
                "existing_factories_check_freshness_capacity_and_witnesses": True,
                "tce_actual_policy": policy},
            "complete_default_corpus": {"originals": 62, "adaptations": 2, "raw_native_matches": 59,
                "adapted_native_matches": 2, "frontend_refusals": refusals, "compiler_timeouts": timeouts,
                "installed_original_cases": installed, "installed_sites": sum(installed.values()),
                "compiled_originals_without_tiling_phase": no_phase,
                "compiled_originals_with_phase_without_installation": phase_without_install,
                "native_mismatches": [], "installed_cases_are_not_speedup_or_exhaustive_nonidentity_counts": True},
            "preceding_corpus": {"installed_cases": reports["preceding_corpus"]["installed_cases"], "installed_sites": 22,
                                 "same_build_comparison_claimed": False},
            "public_and_legacy_cases": len(public), "actual_phase_schedules": phases,
            "trace_proofs": {"modules": sorted({stem for stem, _, _ in TRACE_ATTEMPTS}),
                "source_lines": sum(len(permitted(ROOT / "adapters/compcert-memory" / (stem + ".v")).read_text().splitlines())
                                    for stem in {row[0] for row in TRACE_ATTEMPTS}),
                "endpoints": 6, "closed_endpoints": closed, "inherited_globals": sorted(trace_globals),
                "additional_globals": [], "attempts": attempts, "definitionally_equal_to_original_computation": True},
            "profiles": profiles,
            "compact_oracle": {"untrusted_add_proposal": "keep first constraint per exact canonical key",
                "only_existing_input_certificates_returned": True,
                "original_emptiness_search_and_LCF_check_retained": True,
                "conjunction_equivalence_or_minimality_proved": False,
                "polynomial_codegen_timeout_resolved": False, "full_corpus_with_compact_policy_attempted": False},
            "new_runtime_guard_or_check_family": False, "target_execution_instrumented": False,
            "controlled_cost_or_profitability_established": False, "full_goal_complete": False,
            "reports": REPORTS, "bindings": bindings}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    result = summarize()
    if args.validate:
        if json.loads(OUTPUT.read_text()) != result:
            raise ValueError("Summary changed")
    else:
        with OUTPUT.open("x") as out:
            out.write(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "validated", "reports": len(REPORTS), "bindings": len(result["bindings"]),
                      "installed_cases": len(result["complete_default_corpus"]["installed_original_cases"]),
                      "installed_sites": result["complete_default_corpus"]["installed_sites"], "sha256": sha(OUTPUT)}))


if __name__ == "__main__":
    main()
