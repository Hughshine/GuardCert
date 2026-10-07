"""Audit source-derived recursive body capabilities, safe addresses and write stability."""
import json
from pathlib import Path
import re
import subprocess

import audit_affine_nest_materialized as deep
import audit_loaded_affine_numeric as numeric
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/loaded-affine-body-domain/proof"
LANGUAGE = ["prototype/interface/ClightCellCapabilityTransport.v",
            "prototype/interface/ClightCapableWordSeparation.v"]
DOMAIN = ["prototype/interface/ClightAffineChildBodyDecode.v",
          "prototype/interface/ClightAffineBodyCapabilities.v",
          "prototype/interface/ClightLoadedAffineBodyDomain.v",
          "prototype/interface/ClightLoadedAffineBodyAddress.v",
          "prototype/affine-nest/AffineNestWriteFootprint.v",
          "prototype/interface/ClightLoadedAffineBodyStability.v"]
FIXTURES = ["prototype/interface/ClightLoadedAffineBodyDomainExamples.v"]
BODY = ROOT / "build/loaded-affine-body/proof/report.json"
NUMERIC = ROOT / "build/loaded-affine-numeric/proof/report.json"
DEEP_ENTRY = numeric.DEEP_ENTRY
CURSOR_ENTRY = numeric.CURSOR_ENTRY


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    inherited = {name: json.loads(path.read_text()) for name, path in
                 (("body", BODY), ("numeric", NUMERIC), ("deep", numeric.PARENT), ("cursor", numeric.CURSOR))}
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
    queries = {"COMPCERT": "Compiler.transf_c_program_correct", "KERNEL": "GuardInterface.guardify_preservation",
               "DEEP_REGRESSION": DEEP_ENTRY, "CURSOR_REGRESSION": CURSOR_ENTRY}
    for kind, paths in (("LANGUAGE", LANGUAGE), ("DOMAIN", DOMAIN), ("FIXTURE", FIXTURES)):
        for path in paths:
            for theorem in re.findall(r"^Print Assumptions (\w+)\.", (ROOT / path).read_text(), re.MULTILINE):
                queries[f"{kind}_{len(queries)}"] = f"{Path(path).stem}.{theorem}"
    source = ["From compcert.driver Require Import Compiler.",
              "From GuardInterface Require Import GuardInterface ClightGuardedAffineNestCompiler "
              "ClightGuardedAffineCursorDependentCompiler "
              + " ".join(Path(p).stem for p in LANGUAGE + DOMAIN + FIXTURES if "/interface/" in p) + ".",
              "From GuardAffineNest Require Import AffineNestWriteFootprint."]
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
    assumptions = {marker: names(run.stdout.split(marker + "\n", 1)[1].split(markers[i+1] + "\n", 1)[0])
                   for i, marker in enumerate(markers[:-1])}
    qualify = lambda values: {deep.PRINTER_ALIASES.get(n, n) for n in values}
    assert not assumptions["KERNEL"]
    for marker in ("DEEP_REGRESSION", "CURSOR_REGRESSION"):
        assert qualify(assumptions[marker]) == qualify(inherited["numeric"]["compiler_regressions"][queries[marker]])
    endpoints = {}
    for marker, actual in assumptions.items():
        if marker.startswith(("LANGUAGE_", "DOMAIN_", "FIXTURE_")):
            assert not actual - assumptions["COMPCERT"], (queries[marker], actual - assumptions["COMPCERT"])
            endpoints[queries[marker]] = sorted(actual)
    sources = {**inherited["body"]["sources"], **{s: sha(ROOT / s) for s in closure}}
    report = {
        "status": "compiled", "kind": "loaded-recursive-affine-body-domain-proof",
        "required_closure": closure, "sources": sources,
        "compiled_objects": {s: sha((ROOT / s).with_suffix(".vo")) for s in closure},
        "endpoint_assumptions": endpoints,
        "language_endpoints": [queries[m] for m in queries if m.startswith("LANGUAGE_")],
        "domain_endpoints": [queries[m] for m in queries if m.startswith("DOMAIN_")],
        "fixture_endpoints": [queries[m] for m in queries if m.startswith("FIXTURE_")],
        "compiler_baseline_assumptions": sorted(assumptions["COMPCERT"]),
        "compiler_regressions": {queries[m]: sorted(assumptions[m]) for m in
                                 ("DEEP_REGRESSION", "CURSOR_REGRESSION")},
        "inherited_body_report_sha256": sha(BODY),
        "inherited_numeric_report_sha256": sha(NUMERIC),
        "inherited_materialized_report_sha256": sha(numeric.PARENT),
        "inherited_current_cursor_report_sha256": sha(numeric.CURSOR),
        "inherited_compiled_objects_unchanged": True,
        "parameter_words_are_produced_from_original_source_first_body": True,
        "stronger_initial_prefix_is_produced_without_cached_source_completion": True,
        "recursive_body_model_derived_from_actual_complete_body": True,
        "point_capabilities_derived_from_current_body_and_transported_to_guard_entry": True,
        "mathematical_window_is_not_used_as_memory_permission": True,
        "actual_renamed_point_address_domain_is_produced": True,
        "pointer_equality_uses_valid_aligned_addresses_without_writable_hypothesis": True,
        "write_only_trace_coverage_is_proved": True,
        "point_write_separation_implies_actual_body_bound_preservation": True,
        "reads_may_alias_observed_bound": True,
        "source_domain_requires_finite_normal_completion": True,
        "concrete_alias_domain_and_same_runtime_refusal_fixture": True,
        "recursive_model_and_current_body_point_counts_checked": True,
        "recursive_ready_prefix_fixture_is_symbolic_source_instantiation": True,
        "complete_recursive_body_check_execution_proved": False,
        "materialized_root_short_circuit_scan_implemented": False,
        "recursive_body_check_certificate_producer_implemented": False,
        "new_candidate_certificate": False, "new_compiler_entrypoint": False,
        "new_extraction": False, "new_native_execution": False,
        "new_global_axioms": [], "minimal_semantic_kernel_changed": False,
        "audit_source_sha256": sha(audit), "audit_object_sha256": sha(audit.with_suffix(".vo")),
        "verification_script_sha256": sha(ROOT / "scripts/audit_loaded_affine_body_domain.py"),
        "dependency_helper_sha256": sha(ROOT / "scripts/audit_affine_nest_materialized.py"),
        "inherited_binding_helper_sha256": sha(ROOT / "scripts/audit_loaded_affine_numeric.py"),
        "assumption_parser_sha256": sha(ROOT / "scripts/audit_compiler.py"),
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
    }
    path = WORK / "report.json"
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "passed", "endpoints": len(endpoints), "dependencies": len(closure),
                      "sources": len(sources), "language_endpoints": len(report["language_endpoints"]),
                      "domain_endpoints": len(report["domain_endpoints"]),
                      "fixture_endpoints": len(report["fixture_endpoints"]),
                      "max_new_assumptions": max(map(len, endpoints.values())),
                      "inherited_compiled_objects_unchanged": True,
                      "report_sha256": sha(path)}, indent=2))


if __name__ == "__main__":
    main()
