"""Compile and audit the current nested compiler without historical proof reports."""
import argparse
import json
import re
import subprocess

import audit_affine_nest_materialized as deep
import audit_interface_polyhedral as common
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/nested-stability-shared/proof"
ENTRY = "ClightGuardedNestedStabilityCompiler.compile_ncs_stability_regions"
CORRECT = ENTRY + "_correct"
LANGUAGE = ["ClightInitializedBooleanAnd", "ClightGuardedNestedStabilityCompiler"]
DOMAIN = ["ClightNestedConstantStability", "ClightNestedStabilityMulti",
          "ClightNestedStabilityCertificate", "ClightNestedStabilityPreservation", "ClightNestedStabilityFactory"]
FIXTURES = ["ClightNestedStabilityExample"]
MODULES = LANGUAGE + DOMAIN + FIXTURES
HELPERS = ["scripts/audit_nested_stability.py",
           "scripts/audit_affine_nest_materialized.py", "scripts/audit_interface_polyhedral.py",
           "scripts/audit_interface_clight.py", "scripts/audit_compiler.py", "scripts/polcert_core.py"]
KIND = "standalone-nested-stability-shared-compiler"


def validate():
    report = json.loads((WORK / "report.json").read_text())
    assert report["status"] == "compiled" and report["kind"] == KIND
    assert report["whole_program_entrypoint"] == ENTRY
    assert report["historical_proof_reports_required"] is False
    assert not report["additional_global_axioms"] and not report["kernel_assumptions"]
    assert report["toolchain"] == subprocess.check_output(["rocq", "--version"], text=True).strip()
    for name, digest in report["sources"].items():
        assert sha(ROOT / name) == digest, name
    for name, digest in report["compiled_objects"].items():
        assert sha((ROOT / name).with_suffix(".vo")) == digest, name
    for name, digest in report["verification_helpers"].items():
        assert sha(ROOT / name) == digest, name
    for name, digest in report["audit_artifacts"].items():
        assert sha(WORK / name) == digest, name
    baseline = set().union(*(set(v) for v in report["baseline_assumptions"].values()))
    assert set(report["endpoint_assumptions"][CORRECT]) == baseline
    for endpoint, actual in report["endpoint_assumptions"].items():
        assert set(actual) <= baseline, endpoint
    assert set(report["endpoint_assumptions"]) == set(report["queried_endpoints"])
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    report_path = WORK / "report.json"
    if args.validate or report_path.exists():
        if report_path.exists() and json.loads(report_path.read_text()).get("kind") != KIND:
            raise SystemExit("Use an independent source tree: refusing to replace a historical proof report.")
        report = validate()
        print(json.dumps({"status": "validated", "endpoints": len(report["endpoint_assumptions"]),
                          "report_sha256": sha(report_path)}, indent=2))
        return
    WORK.mkdir(parents=True, exist_ok=True)
    deep.WORK = WORK
    entries = [ROOT / "prototype/interface" / (m + ".v") for m in MODULES]
    entries += [ROOT / "prototype/affine-nest" / (m + ".v") for m in
                ["AffineNestPropose", "AffineNestRangeProposal", "AffineNestMultiProposal"]]
    entries += [ROOT / "adapters/compcert-memory" / (m + ".v") for m in
                ["GuardMemoryScalarTiling", "GuardMemoryNamedMappedChecker", "GuardMemoryNamedChecker"]]
    closure = deep.compile_closure(deep.flags(), entries=entries)
    endpoints = []
    for module in MODULES:
        code = (ROOT / "prototype/interface" / (module + ".v")).read_text()
        assert not re.search(r"\b(Admitted|Abort|Axiom|Parameter)\b", code), module
        endpoints += [module + "." + n for n in
                      re.findall(r"^Print Assumptions (\w+)\.", code, re.MULTILINE)]
    queries = {**common.BASELINES, "KERNEL": "GuardInterface.guardify_preservation",
               **{f"ENDPOINT_{i}": e for i, e in enumerate(endpoints)}}
    lines = ["From compcert.driver Require Import Compiler.",
             "From compcert.common Require Import Memory.",
             "From Guard Require Import ClightCondition.",
             "From GuardMemory Require Import GuardMemoryNamedMappedChecker GuardMemoryNamedChecker.",
             "From GuardInterface Require Import GuardInterface " + " ".join(MODULES) + "."]
    for short, qualified in deep.PRINTER_ALIASES.items():
        lines.append(f"Goal {short}={qualified}. reflexivity. Qed.")
    for marker, theorem in queries.items():
        lines += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {theorem}."]
    lines.append('Goal True. idtac "END". exact I. Qed.')
    audit = WORK / "Audit.v"
    audit.write_text("\n".join(lines) + "\n")
    run = subprocess.run(["rocq", "compile", *deep.flags(), str(audit)], cwd=ROOT,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (WORK / "assumptions.log").write_text(run.stdout)
    assert run.returncode == 0, run.stdout[-2500:]
    markers = [*queries, "END"]
    qualify = lambda values: sorted({deep.PRINTER_ALIASES.get(n, n) for n in values})
    sections = {marker: qualify(names(run.stdout.split(marker + "\n", 1)[1]
                                      .split(markers[i+1] + "\n", 1)[0]))
                for i, marker in enumerate(markers[:-1])}
    baseline = set().union(*(set(sections[m]) for m in common.BASELINES))
    assert not sections["KERNEL"]
    checked = {e: sections[f"ENDPOINT_{i}"] for i, e in enumerate(endpoints)}
    for endpoint, actual in checked.items():
        assert set(actual) <= baseline, (endpoint, set(actual) - baseline)
    assert set(checked[CORRECT]) == baseline
    upstream = ROOT / "vendor/CompCert"
    # Bind all upstream proof sources, including parser/export dependencies of extraction.
    upstream_sources = sorted(p for p in upstream.rglob("*.v"))
    sources = {**{str(p.relative_to(ROOT)): sha(p) for p in upstream_sources},
               **{p: sha(ROOT / p) for p in closure}}
    for name in ["toolchain.lock.json", "adapters/polcert-optimizer/source.lock.json",
                 "adapters/polcert-optimizer/source.patch", "vendor/CompCert/.guard-source.json",
                 "vendor/CompCert/Makefile.config"]:
        sources[name] = sha(ROOT / name)
    locked = json.loads((ROOT / "adapters/polcert-optimizer/source.lock.json").read_text())
    for patch in locked["patches"]:
        sources[patch["path"]] = sha(ROOT / patch["path"])
    objects = {p: sha((ROOT / p).with_suffix(".vo")) for p in closure}
    objects |= {str(p.relative_to(ROOT)): sha(p.with_suffix(".vo")) for p in upstream_sources
                if p.with_suffix(".vo").is_file()}
    report = {"status": "compiled", "kind": KIND, "historical_proof_reports_required": False,
              "whole_program_entrypoint": ENTRY, "whole_program_correctness": CORRECT,
              "required_closure": closure, "sources": sources, "compiled_objects": objects,
              "queried_endpoints": endpoints, "endpoint_assumptions": checked,
              "baseline_assumptions": {m: sections[m] for m in common.BASELINES},
              "kernel_assumptions": sections["KERNEL"], "additional_global_axioms": [],
              "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
              "verification_helpers": {p: sha(ROOT / p) for p in HELPERS},
              "audit_artifacts": {n: sha(WORK / n) for n in ["Audit.v", "Audit.vo", "assumptions.log",
                                 "required-closure.json", "dependencies.txt", "dependency-warnings.txt"]}}
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "compiled", "closure": len(closure),
                      "endpoints": len(endpoints), "baseline_globals": len(baseline),
                      "report_sha256": sha(report_path)}, indent=2))


if __name__ == "__main__":
    main()
