"""Audit loaded-affine stability, alias, candidate, host and Csem-to-Asm composition."""
import json
from pathlib import Path
import re
import subprocess

import audit_affine_nest_materialized as deep
import audit_loaded_affine_numeric as numeric
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/loaded-affine-multi/proof"
LANGUAGE = ["prototype/interface/ClightCheckedTempWrites.v",
            "prototype/interface/ClightMaterializedEntryCertificate.v"]
DOMAIN = ["prototype/interface/ClightLoadedAffineScanTransfer.v",
          "prototype/interface/ClightLoadedAffineCandidate.v",
          "prototype/interface/ClightLoadedAffineMultiGuard.v",
          "prototype/interface/ClightLoadedAffineMultiPreservation.v",
          "prototype/interface/ClightLoadedAffineMultiFactory.v",
          "prototype/interface/ClightGuardedLoadedAffineMultiCompiler.v"]
FIXTURES = ["prototype/interface/ClightLoadedAffineMultiExamples.v"]
SCAN = ROOT / "build/loaded-affine-scan/proof/report.json"
ENTRY = "ClightGuardedLoadedAffineMultiCompiler.compile_loaded_affine_multi_regions"


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    inherited = {key: json.loads(path.read_text()) for key, path in
                 (("scan", SCAN), ("deep", numeric.PARENT), ("cursor", numeric.CURSOR))}
    for report in inherited.values():
        assert report["status"] == "compiled"
        numeric.unchanged(report)
    deep.WORK = WORK
    selected = [ROOT / p for p in LANGUAGE + DOMAIN + FIXTURES] + [
        ROOT / "prototype/interface/ClightGuardedAffineNestCompiler.v",
        ROOT / "prototype/interface/ClightGuardedAffineCursorDependentCompiler.v"]
    closure = deep.compile_closure(deep.flags(), entries=selected)
    for report in inherited.values():
        numeric.unchanged(report)
    queries = {"COMPCERT": "Compiler.transf_c_program_correct",
               "CANDIDATE": "AffineNestCandidateEvidence.checked_affine_candidate_correct",
               "KERNEL": "GuardInterface.guardify_preservation",
               "DEEP_REGRESSION": numeric.DEEP_ENTRY, "CURSOR_REGRESSION": numeric.CURSOR_ENTRY}
    for kind, paths in (("LANGUAGE", LANGUAGE), ("DOMAIN", DOMAIN), ("FIXTURE", FIXTURES)):
        for path in paths:
            for theorem in re.findall(r"^Print Assumptions (\w+)\.", (ROOT / path).read_text(), re.MULTILINE):
                queries[f"{kind}_{len(queries)}"] = f"{Path(path).stem}.{theorem}"
    source = ["From compcert.driver Require Import Compiler.",
              "From GuardInterface Require Import GuardInterface ClightGuardedAffineNestCompiler "
              "ClightGuardedAffineCursorDependentCompiler "
              + " ".join(Path(p).stem for p in LANGUAGE + DOMAIN + FIXTURES) + ".",
              "From GuardAffineNest Require Import AffineNestCandidateEvidence."]
    for short, qualified in deep.PRINTER_ALIASES.items():
        source.append(f"Goal {short}={qualified}. reflexivity. Qed.")
    for marker, theorem in queries.items():
        source += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {theorem}."]
    source.append('Goal True. idtac "END". exact I. Qed.')
    audit = WORK / "Audit.v"
    audit.write_text("\n".join(source) + "\n")
    run = subprocess.run(["rocq", "compile", *deep.flags(), str(audit)], cwd=ROOT,
                         capture_output=True, text=True)
    (WORK / "assumptions.log").write_text(run.stdout + run.stderr)
    assert run.returncode == 0, run.stdout + run.stderr
    markers = [*queries, "END"]
    assumptions = {m: names(run.stdout.split(m + "\n", 1)[1].split(markers[i+1] + "\n", 1)[0])
                   for i, m in enumerate(markers[:-1])}
    assert not assumptions["KERNEL"]
    qualify = lambda values: {deep.PRINTER_ALIASES.get(n, n) for n in values}
    for marker, theorem in (("DEEP_REGRESSION", numeric.DEEP_ENTRY),
                            ("CURSOR_REGRESSION", numeric.CURSOR_ENTRY)):
        expected = inherited["scan"]["compiler_regressions"][theorem]
        assert qualify(assumptions[marker]) == qualify(expected), marker
    baseline = assumptions["COMPCERT"] | assumptions["CANDIDATE"]
    endpoints = {}
    for marker, actual in assumptions.items():
        if marker.startswith(("LANGUAGE_", "DOMAIN_", "FIXTURE_")):
            permitted = assumptions["COMPCERT"] if marker.startswith("LANGUAGE_") else baseline
            assert not actual - permitted, (queries[marker], actual - permitted)
            endpoints[queries[marker]] = sorted(actual)
    assert qualify(endpoints[ENTRY + "_correct"]) == qualify(assumptions["DEEP_REGRESSION"])
    report = {
        "status": "compiled", "kind": "loaded-recursive-affine-multi-compiler-proof",
        "whole_program_entrypoint": ENTRY, "required_closure": closure,
        "sources": {**inherited["scan"]["sources"], **{s: sha(ROOT / s) for s in closure}},
        "compiled_objects": {s: sha((ROOT / s).with_suffix(".vo")) for s in closure},
        "endpoint_assumptions": endpoints,
        "language_endpoints": [queries[m] for m in queries if m.startswith("LANGUAGE_")],
        "domain_endpoints": [queries[m] for m in queries if m.startswith("DOMAIN_")],
        "fixture_endpoints": [queries[m] for m in queries if m.startswith("FIXTURE_")],
        "compiler_baseline_assumptions": sorted(assumptions["COMPCERT"]),
        "domain_baseline_assumptions": sorted(baseline),
        "compiler_regressions": {queries[m]: sorted(assumptions[m]) for m in
                                 ("DEEP_REGRESSION", "CURSOR_REGRESSION")},
        "inherited_scan_report_sha256": sha(SCAN),
        "inherited_materialized_report_sha256": sha(numeric.PARENT),
        "inherited_current_cursor_report_sha256": sha(numeric.CURSOR),
        "inherited_compiled_objects_unchanged": True,
        "private_cache_entry_relation_carries_actual_original_load": True,
        "stability_acceptance_derives_actual_cached_source_for_alias_safety": True,
        "alias_guard_is_skipped_on_stability_refusal": True,
        "candidate_and_dependence_checker_are_reused": True,
        "fallback_is_actual_original_repeated_load_source": True,
        "guard_safety_domain_is_original_source_completion_only": True,
        "finite_normal_local_contract_consumed_by_actual_loaded_region_host": True,
        "static_cache_allocation_checked_and_pool_counters_are_integer_typed": True,
        "untrusted_source_and_candidate_proposers": True,
        "self_alias_actual_source_and_full_guard_refusal": True,
        "same_block_adjacent_word_actual_source_and_full_guard_acceptance": True,
        "recursive_three_axis_static_descriptor_and_progress_fixture": True,
        "nonempty_recursive_three_axis_execution_fixture": False,
        "new_compiler_entrypoint": True, "new_extraction": False, "new_native_execution": False,
        "additional_global_axioms": [], "minimal_semantic_kernel_changed": False,
        "audit_source_sha256": sha(audit), "audit_object_sha256": sha(audit.with_suffix(".vo")),
        "verification_script_sha256": sha(ROOT / "scripts/audit_loaded_affine_multi.py"),
        "dependency_helper_sha256": sha(ROOT / "scripts/audit_affine_nest_materialized.py"),
        "inherited_binding_helper_sha256": sha(ROOT / "scripts/audit_loaded_affine_numeric.py"),
        "assumption_parser_sha256": sha(ROOT / "scripts/audit_compiler.py"),
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
    }
    path = WORK / "report.json"
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "passed", "endpoints": len(endpoints), "dependencies": len(closure),
                      "sources": len(report["sources"]),
                      "language_endpoints": len(report["language_endpoints"]),
                      "domain_endpoints": len(report["domain_endpoints"]),
                      "fixture_endpoints": len(report["fixture_endpoints"]),
                      "compiler_assumptions": len(endpoints[ENTRY + "_correct"]),
                      "max_new_assumptions": max(map(len, endpoints.values())),
                      "inherited_compiled_objects_unchanged": True,
                      "report_sha256": sha(path)}, indent=2))


if __name__ == "__main__":
    main()
