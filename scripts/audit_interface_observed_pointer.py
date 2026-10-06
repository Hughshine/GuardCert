"""Audit source-observed pointer envelopes and their actual Csem-to-Asm entry."""
import argparse
import json
import re
import subprocess
from pathlib import Path

import audit_interface_polyhedral as user_audit
from audit_compiler import names
from audit_interface_clight import ROOT, sha


def main(realization=False, work=None):
    work = work or ROOT / ("build/interface-pointer-realization" if realization else "build/interface-observed-pointer")
    work.mkdir(parents=True, exist_ok=True)
    user_audit.WORK = work
    user_audit.ENTRY = ("ClightObservedPointerCompiler.compile_realized_observed_pointer" if realization
                        else "ClightObservedPointerCompiler.compile_preserving_observed_pointer")
    flags = user_audit.flags()
    inherited = json.loads((ROOT / "build/compcert-guardcert/.guard-build.json").read_text())["proof_sources"]
    changed = [filename for filename, digest in inherited.items() if sha(ROOT / filename) != digest]
    entries = [ROOT / "prototype/interface" / (user_audit.ENTRY.split(".")[0] + ".v")]
    entries += [ROOT / filename for filename in changed]
    closure = user_audit.compile_closure(flags, entries=entries)
    for filename, digest in inherited.items():
        if filename not in closure:
            assert sha(ROOT / filename) == digest, filename
    queries = {
        "COMPCERT": "Compiler.transf_c_program_correct",
        "LANGUAGE": "ClightQuietDeterminacy.quiet_execution_determinate",
        "DOMAIN_BASELINE": "GuardMemoryParamAxisGuard.memory_param_axis_pointer_guard_execution",
        "MAPPED_BASELINE": "GuardMemoryVectorChecker.checked_memory_bounded_candidate_correct",
        "TILING_BASELINE": "GuardMemoryVectorTiling.checked_memory_bounded_tiling_correct",
    }
    language_modules = ["ClightPrivateCheckFacts", "ClightPrivateScan", "ClightPrivateScanSafety",
                        "ClightPrivateScanHost", "ClightPrivateScanPreservation",
                        "ClightSourceObservation", "ClightPrivateScanShortcut", "ClightAffinePointerEnvelope",
                        "ClightSequenceContracts", "ClightObservedPointerSyntax", "ClightSequenceProgressSelector",
                        "ClightPrivateScanShortcutRealization"]
    domain_modules = ["ClightParamPointerCheckFacts", "ClightParamPointerEntryFacts", "ClightParamPointerScanBridge",
                      "ClightParamPointerCertificate", "ClightParamPointerPreservation",
                      "ClightParamPointerCandidates", "ClightParamPointerCompiler", "ClightParamPointerEnvelope", "ClightPointerEnvelopePairs",
                      "ClightObservedPointerPreservation", "ClightObservedPointerCandidate",
                      "ClightObservedPointerCandidates", "ClightObservedPointerCompiler"]
    for kind, modules in [("LANGUAGE_ENDPOINT", language_modules), ("DOMAIN_ENDPOINT", domain_modules)]:
        for module in modules:
            for theorem in re.findall(r"^Print Assumptions ([\w]+)\.",
                                      (ROOT / "prototype/interface" / (module + ".v")).read_text(), re.MULTILINE):
                queries[kind + "_" + str(len(queries))] = module + "." + theorem
    script = work / "Audit.v"
    lines = ["From compcert.driver Require Import Compiler.",
             "From GuardMemory Require Import GuardMemoryParamAxisGuard GuardMemoryVectorChecker GuardMemoryVectorTiling.",
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
    baseline = set().union(*(assumptions[marker] for marker in
                            ["COMPCERT", "DOMAIN_BASELINE", "MAPPED_BASELINE", "TILING_BASELINE"]))
    for marker in queries:
        if marker == "LANGUAGE" or marker.startswith("LANGUAGE_ENDPOINT"):
            assert not assumptions[marker] - assumptions["COMPCERT"], (marker, assumptions[marker] - assumptions["COMPCERT"])
        elif marker.startswith("DOMAIN_ENDPOINT"):
            assert not assumptions[marker] - baseline, (marker, assumptions[marker] - baseline)
    sources = {filename: sha(ROOT / filename) for filename in sorted(set(inherited) | set(closure))}
    endpoints = {queries[marker]: sorted(assumptions[marker]) for marker in queries if "_ENDPOINT_" in marker}
    report = {"status": "compiled", "kind": "source-observed-pointer-envelope-compiler",
              "sources": sources, "required_closure": closure,
              "compiler_baseline_assumptions": sorted(assumptions["COMPCERT"]),
              "domain_baseline_assumptions": sorted(baseline),
              "inherited_domain_assumptions_beyond_compcert": sorted(baseline - assumptions["COMPCERT"]),
              "endpoint_assumptions": endpoints,
              "additional_global_axioms": [], "exact_dispatch_statement_proved_here": True,
              "original_entry_presumption_proved_here": True, "initialization_transport_proved_here": True,
              "guard_host_instantiated_here": True, "private_scan_installed_here": True,
              "readonly_envelope_shortcut_installed_here": True,
              "normalized_source_observation_binding_proved_here": True,
              "retained_quiet_suffix_proved_here": True,
              "actual_source_footprint_coverage_proved_here": True,
              "extraction_run_by_this_audit": False, "native_execution_run_by_this_audit": False, "performance_measured": False,
              "verification_script_sha256": sha(ROOT / "scripts/audit_interface_observed_pointer.py"),
              "frozen_baseline_sources_revalidated_in_current_closure": changed,
              "check_safe_interpretation": "inductive reached-expression and finite loop-continuation judgment",
              "kernel_preservation_consumed_here": "GuardInterface.guardify_preservation",
              "whole_program_entrypoint": user_audit.ENTRY,
              "whole_program_correctness": user_audit.ENTRY+"_correct",
              "realization_modes": ["direct", "shared-fallback"] if realization else ["direct"],
              "shared_fallback_shortcut_installed_here": realization,
              "simulation": "Csem to Asm backward simulation",
              "local_scope": "completed silent normal regions with projected public exits and memory equivalence"}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"],
                      "language_facts": sum(marker.startswith("LANGUAGE_ENDPOINT") for marker in queries),
                      "domain_facts": sum(marker.startswith("DOMAIN_ENDPOINT") for marker in queries), "dependencies": len(closure),
                      "source_digests": len(sources), "additional_global_axioms": []}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--realization", action="store_true")
    parser.add_argument("--output-dir", type=Path, help="keep a fresh audit separate from frozen stage reports")
    arguments = parser.parse_args()
    main(arguments.realization, arguments.output_dir)
