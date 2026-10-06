"""Audit loaded affine pointer proof support, without claiming a new compiler pass.

The selected closure includes the existing affine-inner compiler as a regression.
The new source cache bridge, guard composition and retained-prefix local contract
are audited separately from that compiler's extraction and native evidence.
"""
import argparse
import json
import re
import subprocess

import audit_interface_polyhedral as common
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/affine-loaded-pointer/proof"
LANGUAGE = [
    "prototype/interface/ClightSourcePreloadObservation.v",
    "prototype/interface/ClightAffineLoadedBoundTransport.v",
]
DOMAIN = [
    "adapters/compcert-memory/GuardMemoryObservationStability.v",
    "adapters/compcert-memory/GuardMemoryObservationExclusion.v",
    "adapters/compcert-memory/GuardMemoryAffinePointerLoadedSource.v",
    "prototype/interface/ClightAffineLoadedPointerExample.v",
    "prototype/interface/ClightAffineLoadedPointerRewrite.v",
]
REGRESSION = "ClightAffineInnerPointerCompiler.compile_affine_inner_pointer_correct"


def main(rebuild=False):
    WORK.mkdir(parents=True, exist_ok=True)
    common.WORK = WORK
    flags = common.flags()
    selected = [ROOT / path for path in LANGUAGE + DOMAIN] + [
        ROOT / "prototype/interface/ClightAffineInnerPointerCompiler.v"]
    closure = common.compile_closure(flags, rebuild, entries=selected)
    inherited = json.loads((ROOT / "build/compcert-guardcert/.guard-build.json").read_text())["proof_sources"]
    for path, digest in inherited.items():
        if path not in closure:
            assert sha(ROOT / path) == digest, path
    queries = {
        "COMPCERT": "Compiler.transf_c_program_correct",
        "MAPPED": "GuardMemoryVectorChecker.checked_memory_bounded_candidate_correct",
        "TILING": "GuardMemoryVectorTiling.checked_memory_bounded_tiling_correct",
        "COMPILER_REGRESSION": REGRESSION,
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
    for marker, actual in assumptions.items():
        if marker.startswith("LANGUAGE_"):
            assert not actual - assumptions["COMPCERT"], (queries[marker], actual - assumptions["COMPCERT"])
        elif marker.startswith("DOMAIN_") or marker == "COMPILER_REGRESSION":
            assert not actual - baseline, (queries[marker], actual - baseline)
    endpoints = {queries[marker]: sorted(assumptions[marker]) for marker in queries
                 if marker.startswith(("LANGUAGE_", "DOMAIN_"))}
    report = {
        "status": "compiled", "kind": "affine-loaded-pointer-local-proof-support",
        "required_closure": closure,
        "sources": {path: sha(ROOT / path) for path in sorted(set(inherited) | set(closure))},
        "compiled_objects": {path: sha((ROOT / path).with_suffix(".vo")) for path in closure},
        "endpoint_assumptions": endpoints,
        "language_endpoints": [queries[m] for m in queries if m.startswith("LANGUAGE_")],
        "compiler_baseline_assumptions": sorted(assumptions["COMPCERT"]),
        "domain_baseline_assumptions": sorted(baseline),
        "additional_global_axioms": [],
        "existing_compiler_regression": REGRESSION,
        "existing_compiler_assumptions": sorted(assumptions["COMPILER_REGRESSION"]),
        "retained_source_preload_value_receipt": True,
        "first_loaded_source_body_words_without_stability_assumption": True,
        "actual_physical_write_separation_implies_observation_preservation": True,
        "conservative_affine_box_cell_exclusion_checker": True,
        "modular_pointer_byte_separation_including_wrapped_order": True,
        "loaded_source_to_cached_clight_execution": True,
        "triangle_source_body_consumer_and_written_cell_refusal": True,
        "kernel_sequencing_used_by_actual_combined_condition": True,
        "same_checked_candidate_certificate_consumed_after_source_cache_bridge": True,
        "retained_prefix_projected_region_contract": True,
        "finite_normal_source_completion_required_by_guard_domain": True,
        "cache_is_existing_public_source_preload": True,
        "arbitrary_bound_pointer_supported_by_generic_transport": True,
        "concrete_rule_bound_is_write_buffer_cell_zero": True,
        "multiple_dependent_preload_pass_installed": False,
        "affine_loaded_pointer_source_selector_installed": False,
        "whole_program_entrypoint_for_new_loaded_rule": None,
        "new_loaded_rule_extraction": False,
        "new_loaded_rule_native_execution": False,
        "recompiled_entire_selected_closure": rebuild,
        "verification_script_sha256": sha(ROOT / "scripts/audit_affine_loaded_pointer.py"),
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
    }
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "compiled", "endpoints": len(endpoints), "dependencies": len(closure),
                      "source_digests": len(report["sources"]), "language_endpoints": len(report["language_endpoints"]),
                      "compiler_regression_assumptions": len(assumptions["COMPILER_REGRESSION"]),
                      "additional_global_axioms": 0, "report_sha256": sha(WORK / "report.json"),
                      "new_loaded_rule_installed": False}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rebuild", action="store_true")
    main(parser.parse_args().rebuild)
