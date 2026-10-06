"""Audit dependent-header services; this is not a new compiler/native audit."""
import argparse
import json
import re
import subprocess

import audit_interface_polyhedral as common
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/affine-dependent-loaded/proof"
LANGUAGE = [
    "prototype/interface/ClightDependentBoundSyntax.v",
    "prototype/interface/ClightSignedExpressionProgress.v",
    "prototype/interface/ClightWordChunkSeparation.v",
    "prototype/interface/ClightObservedHeaderPrefix.v",
    "prototype/interface/ClightObservedHeaderCache.v",
    "prototype/interface/ClightDependentSnapshotInsertion.v",
    "prototype/interface/ClightDependentHeaderObservations.v",
    "prototype/interface/ClightDependentHeaderExamples.v",
]
DOMAIN = ["adapters/compcert-memory/GuardMemoryAffineChunkWriteSeparation.v"]
REGRESSION = "ClightGuardedAffinePrivateLoadedCompiler.compile_guarded_affine_private_loaded_correct"
PARENT_PROOF = ROOT / "build/affine-private-loaded/proof/report.json"


def main(rebuild=False):
    WORK.mkdir(parents=True, exist_ok=True)
    common.WORK = WORK
    flags = common.flags()
    selected = [ROOT / path for path in LANGUAGE + DOMAIN] + [
        ROOT / "prototype/interface/ClightGuardedAffinePrivateLoadedCompiler.v"]
    closure = common.compile_closure(flags, rebuild, entries=selected)
    parent = json.loads(PARENT_PROOF.read_text())
    assert parent["verification_script_sha256"] == sha(ROOT / "scripts/audit_affine_private_loaded.py")
    inherited = parent["sources"]
    for path, digest in inherited.items():
        if path not in closure:
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
        "status": "compiled", "kind": "dependent-header-language-and-affine-write-services",
        "required_closure": closure,
        "sources": {path: sha(ROOT / path) for path in sorted(set(inherited) | set(closure))},
        "compiled_objects": {path: sha((ROOT / path).with_suffix(".vo")) for path in closure},
        "inherited_private_proof_report_sha256": sha(PARENT_PROOF),
        "new_endpoints": endpoints,
        "language_endpoint_count": sum(marker.startswith("LANGUAGE_") for marker in queries),
        "new_endpoints_within_compcert_baseline": True,
        "existing_private_compiler_regression": {"theorem": REGRESSION,
            "assumptions": sorted(assumptions["PRIVATE_COMPILER"])},
        "actual_dependent_header_typed_read_receipts": True,
        "checked_compound_header_progress_independent_of_stability": True,
        "safe_ordered_private_pointer_and_bound_capture": True,
        "original_public_scope_preparation_bridge": True,
        "actual_chunk_aware_clight_condition": True,
        "wide_observation_second_word_address_permission_from_load": True,
        "affine_physical_write_sequence_preserves_both_observations_on_accept": True,
        "source_prefix_advances_only_after_all_observations_preserved": True,
        "generic_actual_compound_header_to_cached_execution_bridge": True,
        "concrete_compcert_memory_upper_half_overlap_fixture": True,
        "source_package_to_complete_joint_scan_connected": False,
        "new_candidate_factory_installed": False,
        "new_whole_program_entrypoint": None,
        "new_frontend_acceptance": False,
        "new_extraction": False,
        "new_native_execution": False,
        "prefix_domain_decoder_and_coverage_remain_instance_obligations": True,
        "recompiled_entire_selected_closure": rebuild,
        "verification_script_sha256": sha(ROOT / "scripts/audit_affine_dependent_loaded.py"),
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
