"""Bind identity-trace extraction and the two exact original timeout replays."""
import json
from pathlib import Path
import re

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_combined_residual_traced_corpus import checked

BUILD = ROOT / "build/double-tree-model/compiler-attempts/native-combined-residual-quiet-v1"
FOCUS = ROOT / "build/double-tree-combined-residual/quiet-timeout-attempts/original-tiled-v1/report.json"
PROBE = ROOT / "build/double-tree-combined-residual/trace-erasure-probe-v1"
PROFILE = ROOT / "build/double-tree-residual/compiler-profile-jacobi-v1"
WORK = ROOT / "build/double-tree-combined-residual/quiet-summary-v1"
PORTABLE = ROOT / "docs/double-tree-combined-residual-quiet.json"


def main():
    bindings = {}
    build = checked(BUILD / "report.json", bindings)
    focus = checked(FOCUS, bindings)
    prior = checked(ROOT / "build/double-tree-model/compiler-attempts/native-combined-residual-v2/report.json", bindings)
    if (build["whole_program_entrypoint"] != prior["whole_program_entrypoint"]
            or build["actual_source_Csem_to_Asm_theorem"] != prior["actual_source_Csem_to_Asm_theorem"]
            or not build["VPL_identity_trace_inlined_by_standard_extraction"]
            or focus["native_matches"] != 2):
        raise ValueError("Require the same proved compiler and both successful original replays")
    for name, digest in prior["bindings"].items():
        if name.endswith((".v", ".vo")) and name in build["bindings"]:
            if build["bindings"][name] != digest:
                raise ValueError("Changed Rocq semantic/proof input: " + name)
    extraction = permitted(BUILD / "ExtractSelectedDouble.v").read_text()
    if (extraction.count("Extraction Inline Debugging.trace.") != 1
            or "Extract Constant Debugging.trace =>" in extraction):
        raise ValueError("Use standard inlining of the imported identity definition")
    process = json.loads(permitted(PROBE / "process.json").read_text())
    output = permitted(PROBE / "compile.stdout").read_text()
    extracted_probe = permitted(PROBE / "probe.ml").read_text()
    if (process["returncode"] or output.count("Closed under the global context") != 1
            or not re.search(r"let trace_probe n =\s+n\s*$", extracted_probe)):
        raise ValueError("Require the closed identity experiment and its erased OCaml body")
    modules = sorted((BUILD / "extraction").glob("*.ml"))
    for path in modules:
        text = permitted(path).read_text()
        if re.search(r"\bDebugging\.trace\b|\btrace (OFF|INFO|DEBUG)\b|\bGuardMemoryPhaseTrace\.trace\b", text):
            raise ValueError("VPL diagnostic trace remains callable: " + str(path))
    for path in [Path(__file__), *modules,
                 *[p for p in PROBE.rglob("*") if p.is_file()],
                 *[p for p in PROFILE.rglob("*") if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    cases = [{"case": row["case"], "source_sha256": row["source_sha256"],
              "status": row["status"], "compiler_seconds": row["compiler"]["elapsed_seconds"],
              "prior_timeout_seconds": row["prior_compiler"]["elapsed_seconds"],
              "tree_installed": row["tree_installed"], "typed_installed": row["typed_installed"]}
             for row in focus["results"]]
    summary = {"status": "identity-trace-erased-and-original-replays-match",
               "compiler_entrypoint": build["whole_program_entrypoint"],
               "whole_program_theorem": build["actual_source_Csem_to_Asm_theorem"],
               "compiler": build["compiler"], "compiler_sha256": build["compiler_sha256"],
               "Rocq_semantic_and_proof_inputs_unchanged": True,
               "trace_identity_probe_closed": True,
               "trace_message_evaluation_erased_by_standard_extraction": True,
               "extracted_and_native_modules_bound": len(modules),
               "fine_grained_VPL_phase_trace_available": False,
               "original_timeout_replays": cases,
               "prior_timeouts_retained": True,
               "compiler_cost_controlled_or_exact_speedup_established": False,
               "runtime_guard_cost_measured": False,
               "requested_tiling_support_established_by_replays": False,
               "complete_quiet_corpus_results_added_by_this_report": False,
               "full_goal_complete": False}
    with PORTABLE.open("x") as output:
        output.write(json.dumps(summary, indent=2) + "\n")
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    WORK.mkdir(parents=True, exist_ok=False)
    (WORK / "report.json").write_text(json.dumps({**summary, "bindings": bindings}, indent=2) + "\n")
    print(json.dumps({"status": summary["status"], "original_replays": len(cases),
                      "extracted_and_native_modules": len(modules), "bindings": len(bindings)}))


if __name__ == "__main__":
    main()
