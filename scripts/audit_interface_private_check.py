"""Audit private-check determinacy and its use by the actual parametric pointer scan."""
import json
import subprocess

import audit_interface_polyhedral as user_audit
from audit_compiler import names
from audit_interface_clight import ROOT, sha


def main():
    work = ROOT / "build/interface-private-check"
    work.mkdir(parents=True, exist_ok=True)
    user_audit.WORK = work
    user_audit.ENTRY = "ClightParamPointerCheckFacts.param_axis_pointer_guard_all_executions"
    flags = user_audit.flags()
    closure = user_audit.compile_closure(flags)
    inherited = json.loads((ROOT / "build/compcert-guardcert/.guard-build.json").read_text())["proof_sources"]
    for filename, digest in inherited.items():
        assert sha(ROOT / filename) == digest, filename
    queries = {
        "COMPCERT": "Compiler.transf_c_program_correct",
        "LANGUAGE": "ClightQuietDeterminacy.quiet_execution_determinate",
        "DOMAIN_BASELINE": "GuardMemoryParamAxisGuard.memory_param_axis_pointer_guard_execution",
        "UNIQUE": "ClightPrivateCheckFacts.projected_check_execution_unique",
        "ALL": "ClightPrivateCheckFacts.projected_check_witness_all",
        "SCAN_QUIET": "ClightParamPointerCheckFacts.param_axis_pointer_guard_quiet",
        "SCAN_ALL": "ClightParamPointerCheckFacts.param_axis_pointer_guard_all_executions",
    }
    script = work / "Audit.v"
    lines = ["From compcert.driver Require Import Compiler.",
             "From GuardMemory Require Import GuardMemoryParamAxisGuard.",
             "From GuardInterface Require Import ClightQuietDeterminacy ClightPrivateCheckFacts ClightParamPointerCheckFacts."]
    for marker, theorem in queries.items():
        lines += [f'Goal True. idtac "{marker}". exact I. Qed.', "Print Assumptions " + theorem + "."]
    lines.append('Goal True. idtac "END". exact I. Qed.')
    script.write_text("\n".join(lines) + "\n")
    result = subprocess.run(["rocq", "compile", *flags, script], cwd=ROOT, capture_output=True, text=True)
    (work / "assumptions.log").write_text(result.stdout + result.stderr)
    assert result.returncode == 0, result.stdout + result.stderr
    markers = [*queries, "END"]
    assumptions = {marker: names(result.stdout.split(marker + "\n", 1)[1].split(markers[i+1] + "\n", 1)[0])
                   for i, marker in enumerate(markers[:-1])}
    baseline = assumptions["COMPCERT"] | assumptions["DOMAIN_BASELINE"]
    for marker in ["LANGUAGE", "UNIQUE", "ALL"]:
        assert not assumptions[marker] - assumptions["COMPCERT"], (marker, assumptions[marker] - assumptions["COMPCERT"])
    for marker in ["SCAN_QUIET", "SCAN_ALL"]:
        assert not assumptions[marker] - baseline, (marker, assumptions[marker] - baseline)
    sources = {filename: sha(ROOT / filename) for filename in sorted(set(inherited) | set(closure))}
    report = {"status": "compiled", "kind": "completed-private-check-language-facts",
              "sources": sources, "required_closure": closure,
              "compiler_baseline_assumptions": sorted(assumptions["COMPCERT"]),
              "domain_baseline_assumptions": sorted(assumptions["DOMAIN_BASELINE"]),
              "inherited_domain_assumptions_beyond_compcert": sorted(assumptions["DOMAIN_BASELINE"] - assumptions["COMPCERT"]),
              "endpoint_assumptions": {queries[marker]: sorted(assumptions[marker]) for marker in ["UNIQUE", "ALL", "SCAN_QUIET", "SCAN_ALL"]},
              "additional_global_axioms": [], "exact_dispatch_proved_here": False,
              "private_scan_installed_here": False}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "language_facts": 2, "domain_facts": 2, "dependencies": len(closure),
                      "source_digests": len(sources), "additional_global_axioms": []}))


if __name__ == "__main__":
    main()
