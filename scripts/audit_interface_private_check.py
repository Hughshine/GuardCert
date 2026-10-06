"""Audit actual private-scan dispatch and original-entry premise transport."""
import json
import re
import subprocess

import audit_interface_polyhedral as user_audit
from audit_compiler import names
from audit_interface_clight import ROOT, sha


def main():
    work = ROOT / "build/interface-private-check"
    work.mkdir(parents=True, exist_ok=True)
    user_audit.WORK = work
    user_audit.ENTRY = "ClightParamPointerScanBridge.param_axis_pointer_prefix_all_executions"
    flags = user_audit.flags()
    closure = user_audit.compile_closure(flags)
    inherited = json.loads((ROOT / "build/compcert-guardcert/.guard-build.json").read_text())["proof_sources"]
    for filename, digest in inherited.items():
        assert sha(ROOT / filename) == digest, filename
    queries = {
        "COMPCERT": "Compiler.transf_c_program_correct",
        "LANGUAGE": "ClightQuietDeterminacy.quiet_execution_determinate",
        "DOMAIN_BASELINE": "GuardMemoryParamAxisGuard.memory_param_axis_pointer_guard_execution",
    }
    language_modules = ["ClightPrivateCheckFacts", "ClightPrivateScan"]
    domain_modules = ["ClightParamPointerCheckFacts", "ClightParamPointerEntryFacts", "ClightParamPointerScanBridge"]
    for kind, modules in [("LANGUAGE_ENDPOINT", language_modules), ("DOMAIN_ENDPOINT", domain_modules)]:
        for module in modules:
            for theorem in re.findall(r"^Print Assumptions ([\w]+)\.",
                                      (ROOT / "prototype/interface" / (module + ".v")).read_text(), re.MULTILINE):
                queries[kind + "_" + str(len(queries))] = module + "." + theorem
    script = work / "Audit.v"
    lines = ["From compcert.driver Require Import Compiler.",
             "From GuardMemory Require Import GuardMemoryParamAxisGuard.",
             "From GuardInterface Require Import ClightQuietDeterminacy " + " ".join(language_modules + domain_modules) + "."]
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
    for marker in queries:
        if marker == "LANGUAGE" or marker.startswith("LANGUAGE_ENDPOINT"):
            assert not assumptions[marker] - assumptions["COMPCERT"], (marker, assumptions[marker] - assumptions["COMPCERT"])
        elif marker.startswith("DOMAIN_ENDPOINT"):
            assert not assumptions[marker] - baseline, (marker, assumptions[marker] - baseline)
    sources = {filename: sha(ROOT / filename) for filename in sorted(set(inherited) | set(closure))}
    endpoints = {queries[marker]: sorted(assumptions[marker]) for marker in queries if "_ENDPOINT_" in marker}
    report = {"status": "compiled", "kind": "private-scan-dispatch-and-entry-facts",
              "sources": sources, "required_closure": closure,
              "compiler_baseline_assumptions": sorted(assumptions["COMPCERT"]),
              "domain_baseline_assumptions": sorted(assumptions["DOMAIN_BASELINE"]),
              "inherited_domain_assumptions_beyond_compcert": sorted(assumptions["DOMAIN_BASELINE"] - assumptions["COMPCERT"]),
              "endpoint_assumptions": endpoints,
              "additional_global_axioms": [], "exact_dispatch_statement_proved_here": True,
              "original_entry_presumption_proved_here": True, "initialization_transport_proved_here": True,
              "guard_host_instantiated_here": False, "private_scan_installed_here": False}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"],
                      "language_facts": sum(marker.startswith("LANGUAGE_ENDPOINT") for marker in queries),
                      "domain_facts": sum(marker.startswith("DOMAIN_ENDPOINT") for marker in queries), "dependencies": len(closure),
                      "source_digests": len(sources), "additional_global_axioms": []}))


if __name__ == "__main__":
    main()
