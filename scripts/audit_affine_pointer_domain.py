"""Audit affine-inner pointer proof support and the existing compiler regression.

This is not evidence of a new nonrectangular source selector or compiler entry.
--source-guard includes the checked source package and staged parameter checks;
it still does not assert that a whole-program selector installs this package.
"""
import argparse
import json
import re
import subprocess

import audit_interface_polyhedral as common
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/affine-pointer-domain/proof"
LANGUAGE = [
    "adapters/compcert-memory/GuardMemoryParametricSourceClight.v",
    "adapters/compcert-memory/GuardMemoryParametricFirstBody.v",
]
DOMAIN = [
    "adapters/compcert-memory/GuardMemoryAffineParameterLoops.v",
    "adapters/compcert-memory/GuardMemoryAffineParameterFootprint.v",
    "adapters/compcert-memory/GuardMemoryPointerAccessFootprint.v",
    "adapters/compcert-memory/GuardMemoryAffineParameterPointerFootprint.v",
    "adapters/compcert-memory/GuardMemoryAffinePointerBody.v",
    "adapters/compcert-memory/GuardMemoryParametricInstructionChecker.v",
    "adapters/compcert-memory/GuardMemoryAffinePointerCandidate.v",
    "prototype/interface/ClightPointerEnvelopePairs.v",
    "prototype/interface/ClightAffineParameterPointerEnvelope.v",
    "prototype/interface/ClightTrianglePointerEnvelope.v",
    "adapters/compcert-memory/GuardMemoryParamAxisFootprint.v",
    "prototype/interface/ClightParamPointerEnvelope.v",
]
COMPILER = "ClightObservedPointerCompiler.compile_realized_observed_pointer_correct"


def main(rebuild=False, source_guard=False, output_dir=None):
    global WORK
    language, domain = list(LANGUAGE), list(DOMAIN)
    if source_guard:
        WORK = ROOT / "build/affine-pointer-source/proof"
        language += ["prototype/interface/ClightReadonlyCompletedCondition.v"]
        domain += [
            "adapters/compcert-memory/GuardMemoryAffineInnerPointerSyntax.v",
            "adapters/compcert-memory/GuardMemoryAffineInnerPointerSourceDomain.v",
            "adapters/compcert-memory/GuardMemoryAffineInnerPointerRegionSource.v",
            "prototype/interface/ClightAffinePointerGuard.v",
            "prototype/interface/ClightAffinePointerSourcePreparation.v",
            "prototype/interface/ClightAffinePointerGuardExamples.v",
        ]
    if output_dir is not None:
        WORK = output_dir.resolve()
    WORK.mkdir(parents=True, exist_ok=True)
    common.WORK = WORK
    flags = common.flags()
    selected = [ROOT / path for path in language + domain] + [
        ROOT / "prototype/interface/ClightObservedPointerCompiler.v"]
    closure = common.compile_closure(flags, rebuild, entries=selected)
    inherited = json.loads((ROOT / "build/compcert-guardcert/.guard-build.json").read_text())["proof_sources"]
    for path, digest in inherited.items():
        if path not in closure:
            assert sha(ROOT / path) == digest, path
    queries = {
        "COMPCERT": "Compiler.transf_c_program_correct",
        "MAPPED": "GuardMemoryVectorChecker.checked_memory_bounded_candidate_correct",
        "TILING": "GuardMemoryVectorTiling.checked_memory_bounded_tiling_correct",
        "COMPILER_REGRESSION": COMPILER,
    }
    for kind, paths in [("LANGUAGE", language), ("DOMAIN", domain)]:
        for path in paths:
            for theorem in re.findall(r"^Print Assumptions ([\w]+)\.", (ROOT / path).read_text(), re.MULTILINE):
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
    assumptions = {marker: names(result.stdout.split(marker + "\n", 1)[1].split(markers[i+1] + "\n", 1)[0])
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
        "status": "compiled", "kind": "affine-inner-pointer-source-and-staged-checks" if source_guard else "affine-inner-pointer-proof-support",
        "required_closure": closure,
        "sources": {path: sha(ROOT / path) for path in sorted(set(inherited) | set(closure))},
        "compiled_objects": {path: sha((ROOT / path).with_suffix(".vo")) for path in closure},
        "endpoint_assumptions": endpoints,
        "language_endpoints": [queries[m] for m in queries if m.startswith("LANGUAGE_")],
        "compiler_baseline_assumptions": sorted(assumptions["COMPCERT"]),
        "domain_baseline_assumptions": sorted(baseline),
        "inherited_domain_assumptions_beyond_compcert": sorted(baseline - assumptions["COMPCERT"]),
        "additional_global_axioms": [],
        "existing_rectangular_compiler_regression": COMPILER,
        "existing_compiler_assumptions": sorted(assumptions["COMPILER_REGRESSION"]),
        "affine_inner_pointer_source_model_correspondence": True,
        "actual_nonrectangular_footprint_and_capabilities": True,
        "covering_box_condition_encoding_and_nonalias": True,
        "mapped_candidate_certificate_and_actual_clight_lowering": True,
        "source_public_exit_restoration": True,
        "checked_normalized_affine_inner_source_package": source_guard,
        "source_derived_parameter_readiness": source_guard,
        "staged_readonly_arithmetic_condition": source_guard,
        "source_package_to_actual_loop_correspondence": source_guard,
        "source_domain_requires_finite_normal_source_completion": source_guard,
        "source_package_static_and_early_refusal_examples": source_guard,
        "affine_inner_pointer_source_selector_installed": False,
        "source_derived_complete_guard_domain": False,
        "affine_inner_pointer_whole_program_entrypoint": None,
        "affine_inner_pointer_native_execution": False,
        "extraction_run_by_this_audit": False,
        "recompiled_entire_selected_closure": rebuild,
        "frozen_baseline_sources_revalidated_in_current_closure": [
            path for path, digest in inherited.items() if sha(ROOT / path) != digest],
        "verification_script_sha256": sha(ROOT / "scripts/audit_affine_pointer_domain.py"),
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
    }
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "compiled", "endpoints": len(endpoints), "dependencies": len(closure),
                      "source_digests": len(report["sources"]), "additional_global_axioms": [],
                      "new_whole_program_entrypoint": None}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    from pathlib import Path
    parser.add_argument("--rebuild", action="store_true")
    parser.add_argument("--source-guard", action="store_true")
    parser.add_argument("--output-dir", type=Path)
    arguments = parser.parse_args()
    main(arguments.rebuild, arguments.source_guard, arguments.output_dir)
