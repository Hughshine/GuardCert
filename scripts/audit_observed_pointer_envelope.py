"""Audit source-observed affine separation and its finite Clight region consumer.

This is a proof-library checkpoint, not a compiler or native-runtime report.
The optimization's conditional local certificate is an explicit rule argument.
"""
import argparse
import json
import re
import subprocess

import audit_interface_polyhedral as closure_audit
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/interface-pointer-envelope"
MODULES = ["ClightSourceObservation", "ClightPrivateScanShortcut", "ClightAffinePointerEnvelope",
           "ClightParamPointerEnvelope", "ClightObservedPointerPreservation", "ClightObservedPointerCandidate"]
CONTRACT = "ClightObservedPointerCandidate.check_observed_param_pointer_candidate_sound"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rebuild", action="store_true", help="recompile the entire required user closure")
    arguments = parser.parse_args()
    WORK.mkdir(parents=True, exist_ok=True)
    baseline_path = ROOT / "build/compcert-guardcert/.guard-build.json"
    inherited = json.loads(baseline_path.read_text())["proof_sources"]
    for filename, digest in inherited.items():
        assert sha(ROOT / filename) == digest, ("baseline changed", filename)
    compile_flags = closure_audit.flags()
    closure_audit.WORK, closure_audit.ENTRY = WORK, CONTRACT
    closure = closure_audit.compile_closure(compile_flags, arguments.rebuild)
    endpoints = []
    for module in MODULES:
        source = ROOT / "prototype/interface" / (module + ".v")
        endpoints.extend(module + "." + name for name in
                         re.findall(r"^Print Assumptions ([\w]+)\.", source.read_text(), re.MULTILINE))
    queries = {"COMPCERT": "Compiler.transf_c_program_correct",
               **{f"ENDPOINT_{i}": endpoint for i, endpoint in enumerate(endpoints)}}
    audit = WORK / "Audit.v"
    lines = ["From compcert.driver Require Import Compiler.",
             "From GuardInterface Require Import " + " ".join(MODULES) + "."]
    for marker, theorem in queries.items():
        lines += [f'Goal True. idtac "{marker}". exact I. Qed.', "Print Assumptions " + theorem + "."]
    lines.append('Goal True. idtac "END". exact I. Qed.')
    audit.write_text("\n".join(lines) + "\n")
    result = subprocess.run(["rocq", "compile", *compile_flags, str(audit)], cwd=ROOT,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (WORK / "assumptions.log").write_text(result.stdout)
    assert result.returncode == 0, "assumption compilation failed; see assumptions.log"
    markers = [*queries, "END"]
    sections = {marker: names(result.stdout.split(marker + "\n", 1)[1].split(markers[i + 1] + "\n", 1)[0])
                for i, marker in enumerate(markers[:-1])}
    baseline = sections["COMPCERT"]
    assert baseline, "empty CompCert baseline"
    checked = {}
    for i, endpoint in enumerate(endpoints):
        actual = sections[f"ENDPOINT_{i}"]
        assert not actual - baseline, (endpoint, sorted(actual - baseline))
        checked[endpoint] = sorted(actual)
    report = {
        "status": "compiled",
        "contract": CONTRACT,
        "proof_endpoints": len(endpoints),
        "sources": {**inherited, **{path: sha(ROOT / path) for path in closure}},
        "compiled_objects": {path: sha((ROOT / path).with_suffix(".vo")) for path in closure},
        "required_user_closure": closure,
        "baseline_manifest_sha256": sha(baseline_path),
        "inherited_compcert_assumptions": sorted(baseline),
        "endpoint_assumptions": checked,
        "additional_global_axioms": [],
        "conditional_local_rule": "supplied private_scan_preserving_rule; reused candidate and scan",
        "source_observation": "ordinary source load prefix, retained before dispatch",
        "entry_derivation": "coefficient-sign affine envelopes covering the actual source footprint",
        "physical_separation": "common-base Mint32 cells with modular pointer arithmetic",
        "static_refusal": "false shortcut; original scan retained",
        "dynamic_refusal": "unequal bases or inseparable envelopes; original scan retained",
        "finite_clight_region_contract_proved": True,
        "checked_fragment_lowering_proved": True,
        "new_compiler_entrypoint_proved": False,
        "new_guard_installed_in_extracted_compiler": False,
        "native_execution_run": False,
        "performance_measured": False,
        "verification_script_sha256": sha(ROOT / "scripts/audit_observed_pointer_envelope.py"),
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
    }
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Observed pointer envelope audited: {len(endpoints)} endpoints, {len(closure)} user dependencies; "
          f"{len(baseline)} CompCert assumptions, no additions", flush=True)


if __name__ == "__main__":
    main()
