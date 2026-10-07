"""Audit actual loaded-affine guard execution and cached-source receipt production."""
import json
from pathlib import Path
import re
import subprocess

import audit_affine_nest_materialized as deep
import audit_loaded_affine_numeric as numeric
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/loaded-affine-scan/proof"
LANGUAGE = ["prototype/interface/ClightObservedWordProbe.v",
            "prototype/interface/ClightShortCircuitPrefixLoop.v"]
DOMAIN = ["prototype/interface/ClightAffineObservationLeaf.v",
          "prototype/interface/ClightLoadedAffineWriteTest.v",
          "prototype/interface/ClightLoadedAffineBodyScan.v",
          "prototype/interface/ClightLoadedAffineRootScan.v",
          "prototype/interface/ClightLoadedAffineScanSite.v",
          "prototype/interface/ClightLoadedAffineScanExecution.v",
          "prototype/interface/ClightLoadedAffineScanCertificate.v"]
FIXTURES = ["prototype/interface/ClightLoadedAffineScanExamples.v",
            "prototype/interface/ClightLoadedAffineScanAcceptExample.v"]
BODY_DOMAIN = ROOT / "build/loaded-affine-body-domain/proof/report.json"
BODY = ROOT / "build/loaded-affine-body/proof/report.json"
NUMERIC = ROOT / "build/loaded-affine-numeric/proof/report.json"
DEEP_ENTRY = numeric.DEEP_ENTRY
CURSOR_ENTRY = numeric.CURSOR_ENTRY


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    inherited = {name: json.loads(path.read_text()) for name, path in
                 (("body_domain", BODY_DOMAIN), ("body", BODY), ("numeric", NUMERIC), ("deep", numeric.PARENT), ("cursor", numeric.CURSOR))}
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
    sources = {**inherited["body_domain"]["sources"], **{s: sha(ROOT / s) for s in closure}}
    report = {
        "status": "compiled", "kind": "loaded-recursive-affine-scan-proof",
        "required_closure": closure, "sources": sources,
        "compiled_objects": {s: sha((ROOT / s).with_suffix(".vo")) for s in closure},
        "endpoint_assumptions": endpoints,
        "language_endpoints": [queries[m] for m in queries if m.startswith("LANGUAGE_")],
        "domain_endpoints": [queries[m] for m in queries if m.startswith("DOMAIN_")],
        "fixture_endpoints": [queries[m] for m in queries if m.startswith("FIXTURE_")],
        "compiler_baseline_assumptions": sorted(assumptions["COMPCERT"]),
        "compiler_regressions": {queries[m]: sorted(assumptions[m]) for m in
                                 ("DEEP_REGRESSION", "CURSOR_REGRESSION")},
        "inherited_body_domain_report_sha256": sha(BODY_DOMAIN),
        "inherited_body_report_sha256": sha(BODY),
        "inherited_numeric_report_sha256": sha(NUMERIC),
        "inherited_materialized_report_sha256": sha(numeric.PARENT),
        "inherited_current_cursor_report_sha256": sha(numeric.CURSOR),
        "inherited_compiled_objects_unchanged": True,
        "parameter_words_are_produced_from_original_source_first_body": True,
        "actual_recursive_child_scan_uses_enclosing_private_root_coordinate": True,
        "body_check_domain_is_produced_from_current_source_prefix": True,
        "root_short_circuit_stops_before_increment_and_next_body_on_refusal": True,
        "only_body_acceptance_advances_actual_source_prefix": True,
        "observation_checks_compare_physical_addresses_without_identity_shortcut": True,
        "only_writes_must_be_disjoint_from_loaded_bound": True,
        "initial_capture_numeric_gate_and_stability_scan_form_one_actual_clight_body": True,
        "root_start_zero_and_nonnegative_count_are_checked_at_runtime": True,
        "static_descriptor_checks_source_key_names_child_lowering_and_dispatch_body": True,
        "descriptor_carries_no_per_body_semantic_callback": True,
        "certificate_domain_is_original_source_completion_only": True,
        "certificate_uses_current_materialized_host_and_kernel_without_changes": True,
        "accepted_presumption_constructs_cached_source_execution_and_public_exit_frame": True,
        "cached_source_completion_and_future_stability_are_not_guard_safety_inputs": True,
        "source_domain_requires_finite_normal_completion": True,
        "zero_trip_with_undefined_child_parameters_and_pointer_executes_and_refuses": True,
        "self_alias_source_changes_count_two_to_one_and_actual_complete_guard_refuses": True,
        "same_block_adjacent_word_source_and_actual_complete_guard_accept": True,
        "same_block_acceptance_constructs_actual_cached_source_receipt": True,
        "nonempty_recursive_three_axis_execution_fixture": False,
        "complete_recursive_body_check_execution_proved": True,
        "materialized_root_short_circuit_scan_implemented": True,
        "recursive_body_check_certificate_producer_implemented": True,
        "new_candidate_certificate": False, "new_compiler_entrypoint": False,
        "new_extraction": False, "new_native_execution": False,
        "new_global_axioms": [], "minimal_semantic_kernel_changed": False,
        "audit_source_sha256": sha(audit), "audit_object_sha256": sha(audit.with_suffix(".vo")),
        "verification_script_sha256": sha(ROOT / "scripts/audit_loaded_affine_scan.py"),
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
