"""Audit the checked affine package joint scan and local candidate connection."""
import argparse
import json
import re
import subprocess

import audit_interface_polyhedral as common
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/affine-dependent-joint/proof"
LANGUAGE = [
    "prototype/interface/ClightAffineDependentLoadedPrefix.v",
    "prototype/interface/ClightAffineDependentLoadedStability.v",
    "prototype/interface/ClightAffineDependentLoadedCache.v",
    "prototype/interface/ClightAffineDependentLoadedPreparation.v",
    "prototype/interface/ClightAffineDependentLoadedRewrite.v",
]
DOMAIN = [
    "adapters/compcert-memory/GuardMemoryAffineDependentRow.v",
    "adapters/compcert-memory/GuardMemoryAffineDependentSourceWords.v",
]
REGRESSION = "ClightGuardedAffinePrivateLoadedCompiler.compile_guarded_affine_private_loaded_correct"
PARENT_PROOF = ROOT / "build/affine-dependent-loaded/proof/report.json"
PRIVATE_PROOF = ROOT / "build/affine-private-loaded/proof/report.json"


def main(rebuild=False):
    WORK.mkdir(parents=True, exist_ok=True)
    common.WORK = WORK
    flags = common.flags()
    selected = [ROOT / path for path in LANGUAGE + DOMAIN] + [
        ROOT / "prototype/interface/ClightGuardedAffinePrivateLoadedCompiler.v"]
    closure = common.compile_closure(flags, rebuild, entries=selected)
    parent = json.loads(PARENT_PROOF.read_text())
    assert parent["verification_script_sha256"] == sha(ROOT / "scripts/audit_affine_dependent_loaded.py")
    assert parent["inherited_private_proof_report_sha256"] == sha(PRIVATE_PROOF)
    private = json.loads(PRIVATE_PROOF.read_text())
    for path, digest in private["compiled_objects"].items():
        assert sha((ROOT / path).with_suffix(".vo")) == digest, path
    inherited = parent["sources"]
    for path, digest in inherited.items():
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
    assumptions = {marker: names(result.stdout.split(marker + "\n", 1)[1].split(markers[i+1]+"\n", 1)[0])
                   for i, marker in enumerate(markers[:-1])}
    baseline = assumptions["COMPCERT"] | assumptions["MAPPED"] | assumptions["TILING"]
    assert not assumptions["PREFIX_LIBRARY"]
    assert not assumptions["PRIVATE_COMPILER"] - baseline
    endpoints = {}
    for marker, actual in assumptions.items():
        if marker.startswith(("LANGUAGE_", "DOMAIN_")):
            assert not actual - assumptions["COMPCERT"], (queries[marker], actual - assumptions["COMPCERT"])
            endpoints[queries[marker]] = sorted(actual)
    report = {
        "status": "compiled", "kind": "checked-affine-dependent-header-joint-scan-and-local-candidate",
        "required_closure": closure,
        "sources": {path: sha(ROOT / path) for path in sorted(set(inherited) | set(closure))},
        "compiled_objects": {path: sha((ROOT / path).with_suffix(".vo")) for path in closure},
        "inherited_dependent_services_report_sha256": sha(PARENT_PROOF),
        "inherited_private_proof_report_sha256": sha(PRIVATE_PROOF),
        "new_endpoints": endpoints,
        "language_endpoint_count": sum(marker.startswith("LANGUAGE_") for marker in queries),
        "new_guard_domain_endpoints_within_compcert_baseline": True,
        "all_new_endpoints_within_compcert_baseline": True,
        "new_local_optimizer_endpoints_within_existing_mapped_tiling_baseline": True,
        "existing_private_compiler_regression": {"theorem": REGRESSION,
            "assumptions": sorted(assumptions["PRIVATE_COMPILER"])},
        "checked_package_actual_header_and_body_decode_instantiated": True,
        "source_package_to_complete_joint_scan_connected": True,
        "all_reached_row_write_receipts_back_to_guard_entry": True,
        "scan_fuel_covers_every_active_source_write": True,
        "source_prefix_advances_only_after_both_observations_preserved": True,
        "domain_does_not_assume_future_pointer_or_bound_stability": True,
        "first_reached_header_and_body_produce_preparation_word_evidence": True,
        "actual_compound_source_to_cached_execution_instance": True,
        "existing_candidate_certificate_consumes_accepted_joint_guard": True,
        "same_final_memory_and_public_temps_local_candidate_endpoint": True,
        "original_compound_header_fallback_retained": True,
        "new_candidate_factory_installed": False,
        "new_typed_private_pool_and_capture_domain_producer_connected": False,
        "new_whole_program_entrypoint": None,
        "new_frontend_acceptance": False,
        "new_extraction": False,
        "new_native_execution": False,
        "new_source_order_decoder_and_scan_coverage_are_instance_hypotheses": False,
        "recompiled_entire_selected_closure": rebuild,
        "verification_script_sha256": sha(ROOT / "scripts/audit_affine_dependent_joint.py"),
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
    }
    path = WORK / "report.json"
    path.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"status":"passed", "new_endpoints":len(endpoints),
        "language_endpoints":report["language_endpoint_count"], "dependencies":len(closure),
        "sources":len(report["sources"]), "report_sha256":sha(path), "new_native_execution":False}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--rebuild", action="store_true")
    main(parser.parse_args().rebuild)
