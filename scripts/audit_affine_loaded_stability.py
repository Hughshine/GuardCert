"""Audit source-order stability services; do not claim compiler installation.

The prior loaded and cached compiler theorems are independent regressions.
Symbolic Clight probe fixtures are proof evidence, not native runs.
"""
import argparse
import json
import re
import subprocess

import audit_interface_polyhedral as common
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/affine-loaded-stability/proof"
LANGUAGE = [
    "prototype/interface/ClightStorePermissions.v",
    "prototype/interface/ClightWordAddressSeparation.v",
    "prototype/interface/ClightLoadedRowPrefix.v",
    "prototype/interface/ClightLoadedRowScan.v",
    "prototype/interface/ClightReadonlyExpressionScan.v",
]
DOMAIN = [
    "adapters/compcert-memory/GuardMemoryWriteReceipts.v",
    "adapters/compcert-memory/GuardMemoryLoadedExternalTransport.v",
    "adapters/compcert-memory/GuardMemoryAffineAddressSpecialization.v",
    "adapters/compcert-memory/GuardMemoryAffineWriteSeparation.v",
    "adapters/compcert-memory/GuardMemoryAffineRowSeparation.v",
    "prototype/interface/ClightAffineWriteSeparationExamples.v",
]
REGRESSIONS = {
    "LOADED_COMPILER": "ClightGuardedAffineLoadedCompiler.compile_guarded_affine_loaded_correct",
    "CACHED_COMPILER": "ClightAffineInnerPointerCompiler.compile_affine_inner_pointer_correct",
}


def main(rebuild=False):
    WORK.mkdir(parents=True, exist_ok=True)
    common.WORK = WORK
    flags = common.flags()
    selected = [ROOT / path for path in LANGUAGE + DOMAIN] + [
        ROOT / "prototype/interface/ClightGuardedAffineLoadedCompiler.v",
        ROOT / "prototype/interface/ClightAffineInnerPointerCompiler.v",
    ]
    closure = common.compile_closure(flags, rebuild, entries=selected)
    inherited = json.loads((ROOT / "build/compcert-guardcert/.guard-build.json").read_text())["proof_sources"]
    for path, digest in inherited.items():
        if path not in closure:
            assert sha(ROOT / path) == digest, path
    queries = {
        "COMPCERT": "Compiler.transf_c_program_correct",
        "MAPPED": "GuardMemoryVectorChecker.checked_memory_bounded_candidate_correct",
        "TILING": "GuardMemoryVectorTiling.checked_memory_bounded_tiling_correct",
        "PREFIX_LIBRARY": "ReadonlyPrefixScan.synthesized_prefix_scan_condition",
        **REGRESSIONS,
    }
    for kind, paths in [("LANGUAGE", LANGUAGE), ("DOMAIN", DOMAIN)]:
        for path in paths:
            for theorem in re.findall(r"^Print Assumptions (\w+)\.", (ROOT / path).read_text(), re.MULTILINE):
                queries[f"{kind}_{len(queries)}"] = f"{(ROOT / path).stem}.{theorem}"
    script = WORK / "Audit.v"
    lines = ["From compcert.driver Require Import Compiler.",
             "From GuardMemory Require Import GuardMemoryVectorChecker GuardMemoryVectorTiling."]
    for namespace, directory in [("GuardMemory", "adapters/compcert-memory"),
                                  ("GuardInterface", "prototype/interface")]:
        modules = [p.stem for p in selected if str(p.parent.relative_to(ROOT)) == directory]
        lines.append(f"From {namespace} Require Import " + " ".join(modules) + ".")
    for marker, theorem in queries.items():
        lines += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {theorem}."]
    lines.append('Goal True. idtac "END". exact I. Qed.')
    script.write_text("\n".join(lines) + "\n")
    result = subprocess.run(["rocq", "compile", *flags, str(script)], cwd=ROOT, capture_output=True, text=True)
    (WORK / "assumptions.log").write_text(result.stdout + result.stderr)
    assert result.returncode == 0, result.stdout + result.stderr
    markers = [*queries, "END"]
    assumptions = {marker: names(result.stdout.split(marker + "\n", 1)[1].split(markers[i + 1] + "\n", 1)[0])
                   for i, marker in enumerate(markers[:-1])}
    baseline = assumptions["COMPCERT"] | assumptions["MAPPED"] | assumptions["TILING"]
    assert not assumptions["PREFIX_LIBRARY"]
    for marker, actual in assumptions.items():
        if marker.startswith("LANGUAGE_"):
            assert not actual - assumptions["COMPCERT"], (queries[marker], actual - assumptions["COMPCERT"])
        elif marker.startswith("DOMAIN_") or marker in REGRESSIONS:
            assert not actual - baseline, (queries[marker], actual - baseline)
    endpoints = {queries[marker]: sorted(assumptions[marker]) for marker in queries
                 if marker.startswith(("LANGUAGE_", "DOMAIN_"))}
    report = {
        "status": "compiled", "kind": "source-order-affine-loaded-stability-services",
        "required_closure": closure,
        "sources": {path: sha(ROOT / path) for path in sorted(set(inherited) | set(closure))},
        "compiled_objects": {path: sha((ROOT / path).with_suffix(".vo")) for path in closure},
        "endpoint_assumptions": endpoints,
        "language_endpoints": [queries[m] for m in queries if m.startswith("LANGUAGE_")],
        "compiler_baseline_assumptions": sorted(assumptions["COMPCERT"]),
        "domain_baseline_assumptions": sorted(baseline),
        "additional_global_axioms": [],
        "readonly_prefix_library_assumptions": sorted(assumptions["PREFIX_LIBRARY"]),
        "compiler_regressions": {queries[m]: sorted(assumptions[m]) for m in REGRESSIONS},
        "actual_store_permission_transport": True,
        "reached_complete_row_supplies_all_write_receipts": True,
        "receipt_does_not_require_observed_bound_stability": True,
        "loaded_prefix_uses_remaining_actual_source_execution": True,
        "row_advance_requires_positive_preservation_evidence": True,
        "source_ghost_steps_are_not_executed_by_guard": True,
        "coordinate_specialized_clight_address_evaluation": True,
        "actual_pointer_equality_including_separate_blocks": True,
        "actual_affine_row_guard_safe_available_sound": True,
        "existing_access_encoding_checker_consumed_by_probe_preparation": True,
        "loaded_to_cached_transport_without_body_pointer_membership": True,
        "generic_language_scans_consume_existing_readonly_prefix_library": True,
        "row_decoder_and_row_domain_are_instance_proof_obligations": True,
        "complete_source_package_to_dynamic_scan_instance_installed": False,
        "new_guard_candidate_connection_installed": False,
        "new_guard_whole_program_endpoint": None,
        "new_guard_frontend_acceptance": False,
        "new_guard_extraction": False,
        "new_guard_native_execution": False,
        "finite_normal_source_completion_required_by_loaded_prefix": True,
        "new_private_snapshot_or_dependent_preloads": False,
        "recompiled_entire_selected_closure": rebuild,
        "verification_script_sha256": sha(ROOT / "scripts/audit_affine_loaded_stability.py"),
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
    }
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "compiled", "endpoints": len(endpoints),
                      "language_endpoints": len(report["language_endpoints"]),
                      "dependencies": len(closure), "sources": len(report["sources"]),
                      "new_dynamic_guard_installed": False,
                      "report_sha256": sha(WORK / "report.json")}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--rebuild", action="store_true")
    main(parser.parse_args().rebuild)
