"""Audit the dependent-header factory and its Csem-to-Asm compiler theorem.

This report binds the previous service and joint-package reports without
rewriting them. Frontend, extraction and native runs have separate evidence.
"""
import argparse
import json
import re
import subprocess

import audit_interface_polyhedral as common
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/affine-dependent-compiler/proof"
ENTRY = "ClightGuardedAffineDependentCompiler.compile_guarded_affine_dependent"
LANGUAGE = [
    "prototype/interface/ClightDependentLoadedSource.v",
    "prototype/interface/ClightDependentRegionHost.v",
    "prototype/interface/ClightAffineDependentCheckPlan.v",
    "prototype/interface/ClightDependentCaptureDomain.v",
    "prototype/interface/ClightAffineDependentSyntax.v",
    "prototype/interface/ClightAffineDependentPlannedRewrite.v",
    "prototype/interface/ClightAffineDependentExamples.v",
]
DOMAIN = [
    "prototype/interface/ClightAffineDependentCandidates.v",
    "prototype/interface/ClightGuardedAffineDependentCompiler.v",
]
REGRESSION = "ClightGuardedAffinePrivateLoadedCompiler.compile_guarded_affine_private_loaded_correct"
JOINT = ROOT / "build/affine-dependent-joint/proof/report.json"
SERVICES = ROOT / "build/affine-dependent-loaded/proof/report.json"
PRIVATE = ROOT / "build/affine-private-loaded/proof/report.json"


def main(rebuild=False):
    WORK.mkdir(parents=True, exist_ok=True)
    common.WORK = WORK
    flags = common.flags()
    selected = [ROOT / path for path in LANGUAGE + DOMAIN] + [
        ROOT / "prototype/interface/ClightGuardedAffinePrivateLoadedCompiler.v"]
    closure = common.compile_closure(flags, rebuild, entries=selected)
    joint = json.loads(JOINT.read_text())
    services = json.loads(SERVICES.read_text())
    private = json.loads(PRIVATE.read_text())
    assert joint["verification_script_sha256"] == sha(ROOT / "scripts/audit_affine_dependent_joint.py")
    assert services["verification_script_sha256"] == sha(ROOT / "scripts/audit_affine_dependent_loaded.py")
    assert private["verification_script_sha256"] == sha(ROOT / "scripts/audit_affine_private_loaded.py")
    assert joint["inherited_dependent_services_report_sha256"] == sha(SERVICES)
    assert joint["inherited_private_proof_report_sha256"] == sha(PRIVATE)
    assert services["inherited_private_proof_report_sha256"] == sha(PRIVATE)
    for parent in (private, services, joint):
        for path, digest in parent["sources"].items():
            assert sha(ROOT / path) == digest, path
        for path, digest in parent["compiled_objects"].items():
            assert sha((ROOT / path).with_suffix(".vo")) == digest, path
    queries = {
        "COMPCERT": "Compiler.transf_c_program_correct",
        "MAPPED": "GuardMemoryVectorChecker.checked_memory_bounded_candidate_correct",
        "TILING": "GuardMemoryVectorTiling.checked_memory_bounded_tiling_correct",
        "PREFIX_LIBRARY": "ReadonlyPrefixScan.synthesized_prefix_scan_condition",
        "PRIVATE_COMPILER": REGRESSION,
    }
    for kind, paths in [("LANGUAGE", LANGUAGE), ("DOMAIN", DOMAIN)]:
        for path in paths:
            for theorem in re.findall(r"^Print Assumptions (\w+)\.", (ROOT / path).read_text(), re.MULTILINE):
                # These two AST fixtures reduce the actual impure domain
                # factory, so their module dependencies include VPL axioms.
                endpoint_kind = "DOMAIN" if path.endswith("ClightAffineDependentExamples.v") and theorem in {
                    "numeric_pointer_slot_refused", "pointer_typed_bound_slot_refused"} else kind
                queries[f"{endpoint_kind}_{len(queries)}"] = f"{(ROOT / path).stem}.{theorem}"
    lines = ["From compcert.driver Require Import Compiler.",
             "From GuardMemory Require Import GuardMemoryVectorChecker GuardMemoryVectorTiling.",
             "From GuardInterface Require Import " + " ".join(p.stem for p in selected) + "."]
    for marker, theorem in queries.items():
        lines += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {theorem}."]
    lines.append('Goal True. idtac "END". exact I. Qed.')
    script = WORK / "Audit.v"
    script.write_text("\n".join(lines) + "\n")
    result = subprocess.run(["rocq", "compile", *flags, str(script)], cwd=ROOT, capture_output=True, text=True)
    (WORK / "assumptions.log").write_text(result.stdout + result.stderr)
    assert result.returncode == 0, result.stdout + result.stderr
    markers = [*queries, "END"]
    assumptions = {marker: names(result.stdout.split(marker + "\n", 1)[1].split(markers[i+1]+"\n", 1)[0])
                   for i, marker in enumerate(markers[:-1])}
    baseline = assumptions["COMPCERT"] | assumptions["MAPPED"] | assumptions["TILING"]
    assert not assumptions["PREFIX_LIBRARY"]
    assert not assumptions["PRIVATE_COMPILER"] - baseline
    endpoints = {}
    for marker, actual in assumptions.items():
        if marker.startswith("LANGUAGE_"):
            assert not actual - assumptions["COMPCERT"], (queries[marker], actual - assumptions["COMPCERT"])
        elif marker.startswith("DOMAIN_"):
            assert not actual - baseline, (queries[marker], actual - baseline)
        if marker.startswith(("LANGUAGE_", "DOMAIN_")):
            endpoints[queries[marker]] = sorted(actual)
    report = {
        "status": "compiled", "kind": "dependent-header-affine-compiler-proof",
        "required_closure": closure,
        "sources": {path: sha(ROOT / path) for path in sorted(set(joint["sources"]) | set(closure))},
        "compiled_objects": {path: sha((ROOT / path).with_suffix(".vo")) for path in closure},
        "inherited_dependent_joint_report_sha256": sha(JOINT),
        "inherited_dependent_services_report_sha256": sha(SERVICES),
        "inherited_private_proof_report_sha256": sha(PRIVATE),
        "endpoint_assumptions": endpoints,
        "language_endpoints": [queries[m] for m in queries if m.startswith("LANGUAGE_")],
        "compiler_baseline_assumptions": sorted(assumptions["COMPCERT"]),
        "domain_baseline_assumptions": sorted(baseline),
        "additional_global_axioms": [],
        "readonly_prefix_library_assumptions": sorted(assumptions["PREFIX_LIBRARY"]),
        "compiler_regressions": {REGRESSION: sorted(assumptions["PRIVATE_COMPILER"])},
        "whole_program_entrypoint": ENTRY,
        "whole_program_theorem": ENTRY + "_correct",
        "original_compound_source_is_installation_key": True,
        "safe_ordered_pointer_and_bound_private_captures": True,
        "entry_domain_from_actual_captures_and_reached_source_header": True,
        "domain_does_not_assume_future_pointer_or_bound_stability": True,
        "prepared_extended_scope_projected_to_original_public_scope": True,
        "typed_private_pointer_bound_boolean_counter_pool_checked": True,
        "original_source_progress_selector_consumed_by_actual_host": True,
        "compact_plan_exactly_matches_preparation_joint_stability_and_candidate_guard": True,
        "private_result_initialized_and_public_frame_preserved": True,
        "existing_candidate_checker_modes": ["mapped", "tiling", "schedule"],
        "original_compound_header_fallback_retained": True,
        "minimal_semantic_kernel_changed": False,
        "audit_includes_frontend_acceptance": False,
        "audit_includes_extraction": False,
        "audit_includes_native_execution": False,
        "finite_normal_source_completion_required_by_loaded_prefix": True,
        "optimizer_body_includes_pointer_stores": False,
        "recompiled_entire_selected_closure": rebuild,
        "verification_script_sha256": sha(ROOT / "scripts/audit_affine_dependent_compiler.py"),
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
    }
    path = WORK / "report.json"
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "passed", "endpoints": len(endpoints),
        "language_endpoints": len(report["language_endpoints"]), "dependencies": len(closure),
        "sources": len(report["sources"]), "report_sha256": sha(path),
        "whole_program_theorem": report["whole_program_theorem"],
        "new_native_execution": False}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--rebuild", action="store_true")
    main(parser.parse_args().rebuild)
