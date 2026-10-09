"""Audit the actual-source double OpenScop/prepared pipeline proof."""

import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_original_matmul_pipeline_loop as parent
import audit_original_matmul_typed as typed
import polcert_core
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/original-matmul/prepared-proof-v1"
AST = ROOT / "build/original-matmul/source-prepared-v1"
MODULE_NAMES = ["GuardMemoryDoublePrepared"]
MODULES = [ROOT / f"adapters/compcert-memory/{name}.v" for name in MODULE_NAMES]
SOURCES = [*MODULES, AST / "OriginalMatmulPrepared.v"]


def validate():
    report = json.loads((WORK / "report.json").read_text())
    for name, digest in report["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError(f"Changed proof input: {name}")
    if report["status"] != "compiled" or report["additional_global_axioms"]:
        raise ValueError("Invalid loop proof checkpoint")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate:
        report = validate()
        print(json.dumps({"status": "validated", "bindings": len(report["bindings"]),
                          "report_sha256": sha(WORK / "report.json")}))
        return
    if WORK.exists():
        raise ValueError("Audit checkpoint already exists")
    baseline = parent.validate()
    allowed = set(baseline["allowed_parent_globals"])
    if len(allowed) != 42:
        raise ValueError("Wrong inherited compiler baseline")
    bindings = dict(baseline["bindings"])
    bindings[str((parent.WORK / "report.json").relative_to(ROOT))] = sha(parent.WORK / "report.json")
    source_report = json.loads((AST / "report.json").read_text())
    if source_report["status"] != "compiled" or not source_report["actual_selected_source_execution_to_pipeline_input"]:
        raise ValueError("Actual source-loop proof missing")
    for name, digest in source_report["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError(f"Changed source-loop proof input: {name}")
        bindings[name] = digest
    bindings[str((AST / "report.json").relative_to(ROOT))] = sha(AST / "report.json")
    polcert_core.select_profile("optimizer")
    flags = [*polcert_core.load_flags(), "-Q", str(ROOT / "adapters/compcert-memory"), "GuardMemory",
             "-Q", str(ROOT / "prototype/interface"), "GuardInterface",
             "-R", str(ROOT / "vendor/CompCert/export"), "compcert.export",
             "-Q", str(typed.AST), "GuardOriginalMatmul", "-Q", str(parent.parent.AST), "GuardOriginalMatmulNest",
             "-Q", str(parent.AST), "GuardOriginalMatmulPipeline",
             "-Q", str(AST), "GuardOriginalMatmulPrepared"]
    WORK.mkdir()
    endpoints = []
    for source in SOURCES:
        content = permitted(source).read_text()
        if re.search(r"\b(?:Admitted|Abort|Axiom)\b", content):
            raise ValueError(f"Unproved source: {source}")
        endpoints += [source.stem + "." + name for name in
                      re.findall(r"^Print Assumptions ([\w.]+)\.", content, re.MULTILINE)]
    frontier, seen, level = SOURCES, set(), 0
    while frontier:
        current = sorted(set(frontier) - seen)
        if not current:
            break
        seen.update(current)
        for source in current:
            source = permitted(source)
            obj = permitted(source.with_suffix(".vo"))
            if not obj.exists() or obj.stat().st_mtime < source.stat().st_mtime:
                raise ValueError(f"Uncompiled source: {source}")
            for path in [source, obj]:
                bindings[str(path.relative_to(ROOT))] = sha(path)
        run = subprocess.run(["rocq", "dep", *flags, *map(str, current)], cwd=ROOT,
                             capture_output=True, text=True, check=True)
        (WORK / f"dependencies-{level}.log").write_text(run.stdout + run.stderr)
        frontier = []
        for line in run.stdout.splitlines():
            if ": " not in line:
                continue
            for token in line.split(": ", 1)[1].split():
                if token.endswith(".vo"):
                    obj = permitted(ROOT / token)
                    bindings[str(obj.relative_to(ROOT))] = sha(obj)
                    source = permitted(obj.with_suffix(".v"))
                    if source.exists() and source not in seen:
                        frontier.append(source)
        level += 1
    markers = [f"ORIGINAL_MATMUL_PREPARED_ENDPOINT_{index}" for index in range(len(endpoints) + 1)]
    code = [f"From GuardMemory Require Import {' '.join(MODULE_NAMES)}.",
            "From GuardOriginalMatmulPrepared Require Import OriginalMatmulPrepared."]
    for marker, endpoint in zip(markers, endpoints):
        code += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {endpoint}."]
    code += [f'Goal True. idtac "{markers[-1]}". exact I. Qed.']
    (WORK / "Audit.v").write_text("\n".join(code) + "\n")
    run = subprocess.run(["rocq", "compile", *flags, str(WORK / "Audit.v")], cwd=ROOT, capture_output=True, text=True)
    (WORK / "assumptions.log").write_text(run.stdout + run.stderr)
    if run.returncode:
        raise ValueError(run.stderr)
    actual = {endpoint: sorted(names(run.stdout.split(markers[index] + "\n", 1)[1]
                                   .split(markers[index + 1] + "\n", 1)[0]))
              for index, endpoint in enumerate(endpoints)}
    added = sorted(set().union(*map(set, actual.values())) - allowed)
    if added:
        raise ValueError(f"New globals: {added}")
    attempts = []
    for directory in [ROOT / "build/original-matmul/prepared-attempts", AST / "attempts"]:
        for source in sorted(directory.glob("*.v")):
            log = source.with_suffix(".log")
            if not log.exists():
                raise ValueError(f"Missing attempt log: {source}")
            attempts.append({"source": str(source.relative_to(ROOT)), "log": str(log.relative_to(ROOT)),
                             "compiled": "Error:" not in log.read_text()})
            for path in [source, log]:
                bindings[str(path.relative_to(ROOT))] = sha(path)
    for path in [Path(__file__), ROOT / "scripts/compile_matmul_prepared.py",
                 ROOT / "scripts/prove_original_matmul_prepared.py", ROOT / "scripts/polcert_core.py",
                 ROOT / "scripts/audit_word_store_sequence.py", ROOT / "scripts/audit_compiler.py",
                 ROOT / "toolchain.lock.json", *WORK.iterdir()]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "compiled", "kind": "original-matmul-double-openscop-import-validation-prepared-codegen",
              "new_modules": [str(path.relative_to(ROOT)) for path in MODULES],
              "new_source_lines": sum(len(path.read_text().splitlines()) for path in MODULES),
              "endpoints": endpoints, "endpoint_assumptions": actual,
              "additional_global_axioms": added, "allowed_parent_globals": sorted(allowed),
              "closed_endpoints": sum(not globals for globals in actual.values()),
              "maximum_endpoint_globals": max(map(len, actual.values())),
              "reachable_source_count": len(seen), "attempts": attempts,
              "actual_original_selected_region_exact": True, "actual_pipeline_input_from_original_selected_source": True,
              "prepared_pipeline_directions": "generated wrapped Loop execution to source wrapped Loop execution",
              "source_to_exportable_pipeline_request_proved": True, "external_phase_runner_is_data_only": True,
              "actual_DoubleAssignment_validator_and_prepared_codegen": True,
              "fixed_parameter_source_candidate_execution_bridge_complete": False,
              "exact_final_memory_and_all_public_iterator_exits": True,
              "source_M_zero_retains_j_and_k": True, "source_N_zero_retains_k": True,
              "header_stability_proved_from_global_block_separation": True,
              "per_iteration_entry_facts_derived_from_static_and_loop_invariant": True,
              "N_entry_load_premise_only_when_M_positive": True,
              "K_entry_load_premise_only_when_M_and_N_positive": True,
              "body_reads_licensed_by_original_execution_not_preloaded": True,
              "entry_header_definedness_and_ranges_still_logical_premises": True,
              "I64_complete_three_loop_nest_correspondence": True,
              "nonnegative_I64_scope": True, "total_progress_or_divergence_proved": False,
              "new_private_capture_or_emitted_guard": False, "external_double_scheduler_installed": False,
              "source_user_entry_premises_automatically_produced": False,
              "selected_compiler_connected": False, "new_native_optimized_case": False,
              "complete_program_Csem_to_Asm_endpoint_added": False, "full_goal_complete": False,
              "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(), "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "compiled", "source_lines": report["new_source_lines"],
                      "endpoints": len(endpoints), "closed_endpoints": report["closed_endpoints"],
                      "maximum_endpoint_globals": report["maximum_endpoint_globals"],
                      "reachable_sources": len(seen), "bindings": len(bindings),
                      "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
