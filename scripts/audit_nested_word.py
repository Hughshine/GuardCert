"""Audit the same-word residual check, actual loop effects, and cached-model producer."""
import argparse
import json
import re
import subprocess

import audit_affine_nest_materialized as deep
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/nested-word/proof"
LANGUAGE = ["ClightWordObservationControl"]
DOMAIN = ["ClightNestedConstantWordModel", "ClightNestedConstantWordCheck"]
FIXTURES = ["ClightNestedConstantWordExample"]
MODULES = LANGUAGE + DOMAIN + FIXTURES
HELPERS = ["scripts/audit_nested_word.py", "scripts/audit_affine_nest_materialized.py",
           "scripts/audit_interface_polyhedral.py", "scripts/audit_interface_clight.py",
           "scripts/audit_compiler.py"]


def validate():
    report = json.loads((WORK / "report.json").read_text())
    assert report["status"] == "compiled" and not report["additional_global_axioms"]
    assert not report["kernel_assumptions"]
    for p, digest in report["sources"].items():
        assert sha(ROOT / p) == digest, p
    for p, digest in report["compiled_objects"].items():
        assert sha((ROOT / p).with_suffix(".vo")) == digest, p
    for p, digest in report["helpers"].items():
        assert sha(ROOT / p) == digest, p
    for p, digest in report["artifacts"].items():
        assert sha(WORK / p) == digest, p
    assert report["toolchain"] == subprocess.check_output(["rocq", "--version"], text=True).strip()
    expected = [m + "." + n for m in MODULES for n in
                re.findall(r"^Print Assumptions (\w+)\.",
                           (ROOT / "prototype/interface" / (m + ".v")).read_text(), re.MULTILINE)]
    assert set(expected) == set(report["endpoint_assumptions"])
    baseline = set().union(*(set(a) for a in report["baseline_assumptions"].values()))
    assert len(baseline) == 6
    for endpoint, actual in report["endpoint_assumptions"].items():
        assert set(actual) <= baseline, endpoint
    assert report["actual_residual_check_execution_proved"]
    assert report["original_body_to_cached_model_producer_proved"]
    assert report["actual_check_exit_ports_frame_produced"]
    assert not report["compiler_shortcut_installed"] and not report["guard_cost_measured"]
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate:
        report = validate()
        print(json.dumps({"status": "validated", "endpoints": len(report["endpoint_assumptions"]),
                          "report_sha256": sha(WORK / "report.json")}, indent=2))
        return
    WORK.mkdir(parents=True, exist_ok=True)
    deep.WORK = WORK
    roots = [ROOT / "prototype/interface" / (m + ".v") for m in MODULES]
    for path in roots:
        assert not re.search(r"\b(Admitted|Abort|Axiom|Parameter)\b", path.read_text()), path
    closure = deep.compile_closure(deep.flags(), entries=roots)
    endpoints = [m + "." + n for m in MODULES for n in
                 re.findall(r"^Print Assumptions (\w+)\.",
                            (ROOT / "prototype/interface" / (m + ".v")).read_text(), re.MULTILINE)]
    baseline = {"CLIGHT": "ClightCondition.fragment_language",
                "STORE_SAME": "Mem.load_store_same", "STORE_OTHER": "Mem.load_store_other"}
    queries = {**baseline, "KERNEL": "GuardInterface.guardify_preservation",
               **{f"ENDPOINT_{i}": e for i, e in enumerate(endpoints)}}
    lines = ["From compcert.common Require Import Memory.",
             "From Guard Require Import ClightCondition.",
             "From GuardInterface Require Import GuardInterface " + " ".join(MODULES) + "."]
    for marker, endpoint in queries.items():
        lines += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {endpoint}."]
    lines.append('Goal True. idtac "END". exact I. Qed.')
    audit = WORK / "Audit.v"
    audit.write_text("\n".join(lines) + "\n")
    run = subprocess.run(["rocq", "compile", *deep.flags(), str(audit)], cwd=ROOT,
                         capture_output=True, text=True)
    (WORK / "assumptions.log").write_text(run.stdout + run.stderr)
    assert run.returncode == 0, run.stderr[-1800:]
    markers = [*queries, "END"]
    sections = {m: sorted(names(run.stdout.split(m + "\n", 1)[1]
                               .split(markers[i + 1] + "\n", 1)[0]))
                for i, m in enumerate(markers[:-1])}
    allowed = set().union(*(set(sections[m]) for m in baseline))
    actual = {e: sections[f"ENDPOINT_{i}"] for i, e in enumerate(endpoints)}
    assert len(allowed) == 6 and not sections["KERNEL"]
    for e, a in actual.items():
        assert set(a) <= allowed, (e, set(a) - allowed)
    upstream = ROOT / "vendor/CompCert"
    sources = {str(p.relative_to(ROOT)): sha(p) for p in upstream.rglob("*.v")}
    sources |= {p: sha(ROOT / p) for p in closure}
    objects = {p: sha((ROOT / p).with_suffix(".vo")) for p in closure}
    objects |= {str(p.relative_to(ROOT)): sha(p.with_suffix(".vo"))
                for p in upstream.rglob("*.v") if p.with_suffix(".vo").exists()}
    report = {"status": "compiled", "sources": sources, "compiled_objects": objects,
              "required_dependencies": len(closure), "endpoint_assumptions": actual,
              "baseline_assumptions": {m: sections[m] for m in baseline},
              "kernel_assumptions": sections["KERNEL"], "additional_global_axioms": [],
              "actual_residual_check_execution_proved": True,
              "original_body_to_cached_model_producer_proved": True,
              "actual_check_exit_ports_frame_produced": True,
              "safety_input": "existing original-source numeric/preparation receipt",
              "compiler_shortcut_installed": False, "guard_cost_measured": False,
              "new_native_execution": False,
              "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
              "helpers": {p: sha(ROOT / p) for p in HELPERS},
              "artifacts": {p: sha(WORK / p) for p in
                            ["Audit.v", "Audit.vo", "assumptions.log", "dependencies.txt",
                             "dependency-warnings.txt", "required-closure.json"]}}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "compiled", "endpoints": len(endpoints), "dependencies": len(closure),
                      "baseline_globals": len(allowed), "report_sha256": sha(WORK / "report.json")}, indent=2))


if __name__ == "__main__":
    main()
