"""Compile the Clight read-only adapter and compare its inherited assumptions."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

from audit_compiler import names

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build" / "interface-clight"
DEPENDENCIES = [
    "theories/SemanticFacts.v", "theories/ClightCondition.v",
    "theories/ClightTempFrame.v", "theories/ClightPureExpr.v",
]
MODULES = [
    "prototype/interface/ClightReadonlyRewrite.v",
    "prototype/interface/ClightRegionBoundary.v",
    "prototype/interface/ClightPreloadExample.v",
    "prototype/interface/ClightPreloadSynthesis.v",
    "prototype/interface/ClightAdministrative.v",
    "prototype/interface/ClightQuietDeterminacy.v",
    "prototype/interface/ClightLoopBridge.v",
    "prototype/interface/ClightPrivateCandidateExample.v",
    "prototype/interface/ClightReadonlyTreeFacts.v",
    "prototype/interface/ClightReadonlyTreeSynthesis.v",
    "prototype/interface/ClightConditionComposition.v",
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def compcert_flags():
    flags = ["-Q", "theories", "Guard", "-Q", "prototype/interface", "GuardInterface"]
    for folder in ("lib", "common", "x86", "x86_64", "cfrontend", "backend", "driver"):
        flags += ["-R", f"vendor/CompCert/{folder}", f"compcert.{folder}"]
    return flags + ["-R", "vendor/CompCert/flocq", "Flocq"]


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    # Bind reuse to the source manifest of the existing proved compiler.
    # This does not rebuild that compiler or claim the new adapter is used by it.
    manifest_path = ROOT / "build/compcert-guardcert/.guard-build.json"
    manifest = json.loads(manifest_path.read_text())
    reused = manifest["proof_sources"]
    for filename, digest in reused.items():
        if sha(ROOT / filename) != digest:
            raise SystemExit(f"Reused dependency source changed: {filename}; rebuild the compiler baseline")
    interface = json.loads((ROOT / "build/interface/report.json").read_text())
    for filename, digest in interface["sources"].items():
        if sha(ROOT / filename) != digest:
            raise SystemExit(f"Pure interface changed: {filename}; run make interface-proof")
    flags = compcert_flags()
    sections = []
    for filename in DEPENDENCIES + MODULES:
        result = subprocess.run(["rocq", "compile", *flags, filename], cwd=ROOT,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        sections.append(f"Compiling {filename}\n{result.stdout}")
        (WORK / "proof.log").write_text("\n".join(sections))
        if result.returncode:
            raise SystemExit(f"Clight interface failed: {filename}; see {WORK / 'proof.log'}")
        print(f"Compiled {filename}", flush=True)
    endpoints = []
    for filename in MODULES:
        module = Path(filename).stem
        endpoints += [f"{module}.{name}" for name in
                      re.findall(r"^Print Assumptions ([\w]+)\.", (ROOT / filename).read_text(), re.MULTILINE)]
    source = WORK / "Audit.v"
    imports = " ".join(Path(filename).stem for filename in MODULES)
    lines = ["From Guard Require Import ClightCondition.",
             f"From GuardInterface Require Import {imports}.",
             'Goal True. idtac "BASELINE". exact I. Qed.',
             "Print Assumptions ClightCondition.fragment_language."]
    for index, endpoint in enumerate(endpoints):
        lines += [f'Goal True. idtac "ENDPOINT_{index}". exact I. Qed.', f"Print Assumptions {endpoint}."]
    lines += ['Goal True. idtac "END". exact I. Qed.']
    source.write_text("\n".join(lines) + "\n")
    result = subprocess.run(["rocq", "compile", *flags, str(source)], cwd=ROOT,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (WORK / "assumptions.log").write_text(result.stdout)
    if result.returncode:
        raise SystemExit(f"Assumption audit failed; see {WORK / 'assumptions.log'}")
    baseline = names(result.stdout.split("BASELINE\n", 1)[1].split("ENDPOINT_0\n", 1)[0])
    if len(baseline) != 6:
        raise SystemExit(f"Unexpected Clight baseline: {sorted(baseline)}")
    inherited = {}
    for index, endpoint in enumerate(endpoints):
        next_marker = f"ENDPOINT_{index + 1}" if index + 1 < len(endpoints) else "END"
        assumptions = names(result.stdout.split(f"ENDPOINT_{index}\n", 1)[1].split(next_marker + "\n", 1)[0])
        if assumptions - baseline:
            raise SystemExit(f"Additional assumptions at {endpoint}: {sorted(assumptions - baseline)}")
        inherited[endpoint] = sorted(assumptions)
    report = {
        "status": "compiled",
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
        "new_clight_modules_compiled": len(MODULES),
        "existing_dependencies_recompiled": len(DEPENDENCIES),
        "inherited_dependency_sources_checked": len(reused),
        "baseline_source_manifest_sha256": sha(manifest_path),
        "pure_interface_report_sha256": sha(ROOT / "build/interface/report.json"),
        "sources": {filename: sha(ROOT / filename) for filename in DEPENDENCIES + MODULES},
        "compiled_objects": {filename: sha((ROOT / filename).with_suffix(".vo")) for filename in MODULES},
        "inherited_clight_baseline": sorted(baseline),
        "endpoint_assumptions": inherited,
        "additional_global_axioms": [],
        "actual_clight_readonly_dispatch_proved": True,
        "every_reachable_test_safety_proved": True,
        "dependent_readonly_check_algebra_instantiated": True,
        "conditional_preload_fixture_proved": True,
        "preload_domain_derived_from_terminating_source_fixture": True,
        "preload_atom_has_formula_synthesis_certificate": True,
        "local_private_candidate_observation_example_proved": True,
        "private_candidate_global_adapter_included_in_this_audit": False,
        "write_frame_interface_is_complete_read_coverage": False,
        "full_clight_equivalence_context_adapter_proved": False,
        "compcert_compiler_uses_new_readonly_api": False,
        "native_execution_run": False,
    }
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Clight adapter audited: {len(endpoints)} endpoints; no assumptions beyond the 6 inherited baseline names")


if __name__ == "__main__":
    main()
