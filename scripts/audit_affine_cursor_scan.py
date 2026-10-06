"""Audit actual short-circuit cursor scans and dependent affine row reuse.

The existing dependent compiler remains a bound regression. This report does
not claim that its factories generate the new scans or that new native runs
have been performed.
"""
import argparse
import json
import re
import subprocess

import audit_interface_polyhedral as common
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/affine-cursor-scan/proof"
LANGUAGE = [
    "prototype/interface/ClightBoundedCheckLoop.v",
    "prototype/interface/ClightCursorSpecialization.v",
    "prototype/interface/ClightCursorCheckBody.v",
    "prototype/interface/ClightCursorBoundedScan.v",
    "prototype/interface/ClightCursorScanExamples.v",
]
DOMAIN = [
    "adapters/compcert-memory/GuardMemoryAffineCursorProbes.v",
    "adapters/compcert-memory/GuardMemoryAffineCursorRow.v",
]
PARENT = ROOT / "build/affine-dependent-compiler/proof/report.json"
REGRESSION = "ClightGuardedAffineDependentCompiler.compile_guarded_affine_dependent_correct"


def main(rebuild=False):
    WORK.mkdir(parents=True, exist_ok=True)
    common.WORK = WORK
    flags = common.flags()
    selected = [ROOT / path for path in LANGUAGE + DOMAIN] + [
        ROOT / "prototype/interface/ClightGuardedAffineDependentCompiler.v"]
    closure = common.compile_closure(flags, rebuild, entries=selected)
    parent = json.loads(PARENT.read_text())
    assert parent["verification_script_sha256"] == sha(ROOT / "scripts/audit_affine_dependent_compiler.py")
    for path, digest in parent["sources"].items():
        assert sha(ROOT / path) == digest, path
    for path, digest in parent["compiled_objects"].items():
        assert sha((ROOT / path).with_suffix(".vo")) == digest, path
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
    for kind, paths in [("LANGUAGE", LANGUAGE), ("DOMAIN", DOMAIN)]:
        for path in paths:
            for theorem in re.findall(r"^Print Assumptions (\w+)\.", (ROOT / path).read_text(), re.MULTILINE):
                queries[f"{kind}_{len(queries)}"] = f"{(ROOT / path).stem}.{theorem}"
    lines = [
        "From compcert.driver Require Import Compiler.",
        "From GuardMemory Require Import GuardMemoryVectorChecker GuardMemoryVectorTiling "
        + " ".join((ROOT / p).stem for p in DOMAIN) + ".",
        "From GuardInterface Require Import ReadonlyPrefixScan ClightGuardedAffineDependentCompiler "
        + " ".join((ROOT / p).stem for p in LANGUAGE) + ".",
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
        if marker.startswith(("LANGUAGE_", "DOMAIN_")):
            assert not actual - assumptions["COMPCERT"], (queries[marker], actual - assumptions["COMPCERT"])
            endpoints[queries[marker]] = sorted(actual)
    report = {
        "status": "compiled", "kind": "short-circuit-cursor-affine-row-proof",
        "required_closure": closure,
        "sources": {path: sha(ROOT / path) for path in sorted(set(parent["sources"]) | set(closure))},
        "compiled_objects": {path: sha((ROOT / path).with_suffix(".vo")) for path in closure},
        "inherited_dependent_compiler_report_sha256": sha(PARENT),
        "endpoint_assumptions": endpoints,
        "language_endpoints": [queries[m] for m in queries if m.startswith("LANGUAGE_")],
        "compiler_baseline_assumptions": sorted(assumptions["COMPCERT"]),
        "domain_baseline_assumptions": sorted(baseline),
        "additional_global_axioms": [],
        "compiler_regressions": {REGRESSION: sorted(assumptions["COMPILER_REGRESSION"])},
        "readonly_prefix_library_assumptions": sorted(assumptions["PREFIX_LIBRARY"]),
        "runtime_code_uses_private_column_cursor_loop": True,
        "private_cursor_and_result_initialized_by_actual_code": True,
        "reject_exits_before_next_activity_probe_or_increment": True,
        "actual_undefined_later_probe_fixture": True,
        "row_scan_logical_spec_equals_previous_row_condition": True,
        "actual_row_acceptance_preserves_both_header_observations": True,
        "actual_row_domain_supplies_logical_check_availability": True,
        "caller_obligations": [
            "private resource freshness and public read scope",
            "original row domain including actual reached-write receipts",
            "outer prefix advancement and all-row coverage",
            "source/factory placement and whole-program host installation",
        ],
        "new_outer_loop_scan": False,
        "new_factory_connected": False,
        "new_whole_program_entrypoint": False,
        "new_extraction": False,
        "new_frontend_acceptance": False,
        "new_native_execution": False,
        "minimal_semantic_kernel_changed": False,
        "recompiled_entire_selected_closure": rebuild,
        "verification_script_sha256": sha(ROOT / "scripts/audit_affine_cursor_scan.py"),
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
    }
    path = WORK / "report.json"
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "passed", "endpoints": len(endpoints),
        "language_endpoints": len(report["language_endpoints"]), "dependencies": len(closure),
        "sources": len(report["sources"]), "report_sha256": sha(path),
        "new_factory_connected": False, "new_native_execution": False}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rebuild", action="store_true")
    main(parser.parse_args().rebuild)
