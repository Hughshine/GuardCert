"""Audit the nested-cursor dependent affine compiler and its inherited proofs."""
import argparse
import json
import re
import subprocess

import audit_interface_polyhedral as common
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/affine-cursor-dependent-compiler/proof"
LANGUAGE = [
    "prototype/interface/ClightNestedCursorScan.v",
    "prototype/interface/ClightStagedCheck.v",
]
GUARD = [
    "adapters/compcert-memory/GuardMemoryAffineNestedCursorProbes.v",
    "prototype/interface/ClightAffineDependentCursorScan.v",
    "prototype/interface/ClightAffineDependentCursorResources.v",
    "prototype/interface/ClightAffineDependentCursorRewrite.v",
]
DOMAIN = [
    "prototype/interface/ClightAffineCursorDependentCandidates.v",
    "prototype/interface/ClightGuardedAffineCursorDependentCompiler.v",
]
PARENT = ROOT / "build/affine-dependent-compiler/proof/report.json"
CURSOR_PARENT = ROOT / "build/affine-cursor-scan/proof/report.json"
ENTRY = "ClightGuardedAffineCursorDependentCompiler.compile_guarded_affine_cursor_dependent"
REGRESSION = "ClightGuardedAffineDependentCompiler.compile_guarded_affine_dependent_correct"


def bound_parent(path, script):
    parent = json.loads(path.read_text())
    assert parent["status"] == "compiled"
    assert parent["verification_script_sha256"] == sha(ROOT / script)
    for source, digest in parent["sources"].items():
        assert sha(ROOT / source) == digest, source
    for source, digest in parent["compiled_objects"].items():
        assert sha((ROOT / source).with_suffix(".vo")) == digest, source
    return parent


def main(rebuild=False):
    WORK.mkdir(parents=True, exist_ok=True)
    common.WORK = WORK
    flags = common.flags()
    selected = [ROOT / path for path in LANGUAGE + GUARD + DOMAIN] + [
        ROOT / "prototype/interface/ClightGuardedAffineDependentCompiler.v"]
    closure = common.compile_closure(flags, rebuild, entries=selected)
    parent = bound_parent(PARENT, "scripts/audit_affine_dependent_compiler.py")
    cursor = bound_parent(CURSOR_PARENT, "scripts/audit_affine_cursor_scan.py")
    assert cursor["inherited_dependent_compiler_report_sha256"] == sha(PARENT)
    for key, path in [
        ("inherited_dependent_joint_report_sha256", "build/affine-dependent-joint/proof/report.json"),
        ("inherited_dependent_services_report_sha256", "build/affine-dependent-loaded/proof/report.json"),
        ("inherited_private_proof_report_sha256", "build/affine-private-loaded/proof/report.json"),
    ]:
        assert parent[key] == sha(ROOT / path), path
    queries = {
        "COMPCERT": "Compiler.transf_c_program_correct",
        "MAPPED": "GuardMemoryVectorChecker.checked_memory_bounded_candidate_correct",
        "TILING": "GuardMemoryVectorTiling.checked_memory_bounded_tiling_correct",
        "PREFIX_LIBRARY": "ReadonlyPrefixScan.synthesized_prefix_scan_condition",
        "COMPILER_REGRESSION": REGRESSION,
    }
    for kind, paths in [("LANGUAGE", LANGUAGE), ("GUARD", GUARD), ("DOMAIN", DOMAIN)]:
        for path in paths:
            for theorem in re.findall(r"^Print Assumptions (\w+)\.", (ROOT / path).read_text(), re.MULTILINE):
                queries[f"{kind}_{len(queries)}"] = f"{(ROOT / path).stem}.{theorem}"
    lines = [
        "From compcert.driver Require Import Compiler.",
        "From GuardMemory Require Import GuardMemoryVectorChecker GuardMemoryVectorTiling GuardMemoryAffineNestedCursorProbes.",
        "From GuardInterface Require Import ReadonlyPrefixScan ClightGuardedAffineDependentCompiler "
        + " ".join((ROOT / p).stem for p in LANGUAGE + GUARD + DOMAIN if p.startswith("prototype/")) + ".",
    ]
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
    assert not assumptions["COMPILER_REGRESSION"] - baseline
    assert sorted(assumptions["COMPILER_REGRESSION"]) == parent["endpoint_assumptions"][REGRESSION]
    endpoints = {}
    for marker, actual in assumptions.items():
        if marker.startswith(("LANGUAGE_", "GUARD_", "DOMAIN_")):
            permitted = assumptions["COMPCERT"] if marker.startswith(("LANGUAGE_", "GUARD_")) else baseline
            assert not actual - permitted, (queries[marker], actual - permitted)
            endpoints[queries[marker]] = sorted(actual)
    assert sorted(endpoints[ENTRY + "_correct"]) == parent["endpoint_assumptions"][REGRESSION]
    report = {
        "status": "compiled", "kind": "nested-cursor-dependent-affine-compiler-proof",
        "whole_program_entrypoint": ENTRY,
        "required_closure": closure,
        "sources": {path: sha(ROOT / path) for path in sorted(set(cursor["sources"]) | set(closure))},
        "compiled_objects": {path: sha((ROOT / path).with_suffix(".vo")) for path in closure},
        "inherited_dependent_compiler_report_sha256": sha(PARENT),
        "inherited_cursor_services_report_sha256": sha(CURSOR_PARENT),
        "endpoint_assumptions": endpoints,
        "language_endpoints": [queries[m] for m in queries if m.startswith("LANGUAGE_")],
        "guard_service_endpoints": [queries[m] for m in queries if m.startswith("GUARD_")],
        "compiler_baseline_assumptions": sorted(assumptions["COMPCERT"]),
        "domain_baseline_assumptions": sorted(baseline),
        "additional_global_axioms": [],
        "compiler_regressions": {REGRESSION: sorted(assumptions["COMPILER_REGRESSION"])},
        "readonly_prefix_library_assumptions": sorted(assumptions["PREFIX_LIBRARY"]),
        "actual_nested_private_cursor_loops": True,
        "loop_spec_equals_inherited_full_stability_condition": True,
        "actual_checked_package_fills_scan_callbacks": True,
        "finite_resource_checker_avoids_expanded_scan_spec": True,
        "guard_cursors_disjoint_from_candidate_counters": True,
        "short_circuit_staged_dispatch_preserves_public_frame": True,
        "original_compound_source_key_and_fallback_retained": True,
        "new_factory_connected": True,
        "new_whole_program_entrypoint": True,
        "new_extraction": False,
        "new_frontend_acceptance": False,
        "new_native_execution": False,
        "minimal_semantic_kernel_changed": False,
        "recompiled_entire_selected_closure": rebuild,
        "verification_script_sha256": sha(ROOT / "scripts/audit_affine_cursor_dependent.py"),
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
    }
    path = WORK / "report.json"
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "passed", "endpoints": len(endpoints),
        "language_endpoints": len(report["language_endpoints"]),
        "guard_service_endpoints": len(report["guard_service_endpoints"]),
        "dependencies": len(closure), "sources": len(report["sources"]),
        "report_sha256": sha(path), "whole_program_entrypoint": ENTRY,
        "new_factory_connected": True, "new_native_execution": False}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rebuild", action="store_true")
    main(parser.parse_args().rebuild)
