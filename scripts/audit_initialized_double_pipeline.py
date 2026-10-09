"""Audit actual initialized-source capture and final checked pipeline bridges."""

import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_initialized_double_nests as parent
import compile_matmul_installation as compiler
import prove_initialized_double_entry as entry
import prove_initialized_double_pipeline as pipeline
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/double-initialized-nests/pipeline-audit-v1"
MODULE_NAMES = ["GuardMemoryDoublePipelineTransport", "GuardMemoryDoubleLiteralPrepared",
                "GuardMemoryDoubleInitializedPipeline", "GuardMemoryDoubleInitializedEntry"]
MODULES = [ROOT / "adapters/compcert-memory" / (name + ".v") for name in MODULE_NAMES]
MODULES += [pipeline.WORK / "OriginalInitializedDoublePipeline.v",
            entry.WORK / "OriginalInitializedDoubleEntry.v"]


def validate():
    report = json.loads((WORK / "report.json").read_text())
    if report["status"] != "compiled" or report["additional_global_axioms"]:
        raise ValueError("Invalid initialized pipeline checkpoint")
    for name, digest in report["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError("Changed proof input: " + name)
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
    binding_path = entry.WORK / "report.json"
    binding = json.loads(binding_path.read_text())
    if binding["status"] != "compiled" or binding["actual_original_cases"] != ["mxv", "matmul-init"]:
        raise ValueError("Expected both original source entry bridges")
    bindings = dict(baseline["bindings"])
    for name, digest in binding["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError("Changed original source proof input: " + name)
        bindings[name] = digest
    for path in [parent.WORK / "report.json", binding_path]:
        bindings[str(path.relative_to(ROOT))] = sha(path)
    flags = entry.flags()
    WORK.mkdir(parents=True)
    endpoints = []
    for source in MODULES:
        content = permitted(source).read_text()
        if re.search(r"\b(?:Admitted|Abort|Axiom)\b", content):
            raise ValueError("Unproved source: " + str(source))
        endpoints += [source.stem + "." + name for name in
                      re.findall(r"^Print Assumptions ([\w.]+)\.", content, re.MULTILINE)]
    frontier, seen, level = MODULES, set(), 0
    while frontier:
        current = sorted(set(frontier) - seen)
        if not current:
            break
        seen.update(current)
        for source in current:
            source = permitted(source)
            obj = permitted(source.with_suffix(".vo"))
            if not obj.exists() or obj.stat().st_mtime < source.stat().st_mtime:
                raise ValueError("Uncompiled source: " + str(source))
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
    markers = [f"DOUBLE_INITIALIZED_PIPELINE_ENDPOINT_{index}" for index in range(len(endpoints)+1)]
    code = ["From GuardMemory Require Import " + " ".join(MODULE_NAMES) + ".",
            "From GuardInitializedPipelineProof Require Import OriginalInitializedDoublePipeline.",
            "From GuardInitializedEntryProof Require Import OriginalInitializedDoubleEntry."]
    for marker, endpoint in zip(markers, endpoints):
        code += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {endpoint}."]
    code += [f'Goal True. idtac "{markers[-1]}". exact I. Qed.']
    (WORK / "Audit.v").write_text("\n".join(code)+"\n")
    run = subprocess.run(["rocq", "compile", *flags, str(WORK / "Audit.v")], cwd=ROOT,
                         capture_output=True, text=True)
    (WORK / "assumptions.log").write_text(run.stdout + run.stderr)
    if run.returncode:
        raise ValueError(run.stderr)
    actual = {endpoint: sorted(names(run.stdout.split(markers[index]+"\n", 1)[1]
                                    .split(markers[index+1]+"\n", 1)[0]))
              for index, endpoint in enumerate(endpoints)}
    added = sorted(set().union(*map(set, actual.values()))-allowed)
    if added:
        raise ValueError("New globals: " + str(added))
    attempts = []
    for metadata in sorted(compiler.WORK.glob("*.json")):
        item = json.loads(metadata.read_text())
        if Path(item["source"]) not in {path.relative_to(ROOT) for path in MODULES}:
            continue
        snapshot, log = metadata.with_suffix(".v"), metadata.with_suffix(".log")
        if not log.exists() or sha(snapshot) != item["source_sha256"]:
            raise ValueError("Incomplete attempt: " + str(metadata))
        attempts.append({"metadata": str(metadata.relative_to(ROOT)), "returncode": item["returncode"]})
        for path in [snapshot, log, metadata]:
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    wrapper_attempts = []
    for directory in [pipeline.WORK / "attempts", entry.WORK / "attempts"]:
        for metadata in sorted(directory.glob("*.json")):
            item = json.loads(metadata.read_text())
            snapshot, log = metadata.with_suffix(".v"), metadata.with_suffix(".log")
            if not log.exists() or sha(snapshot) != item["source_sha256"]:
                raise ValueError("Changed wrapper attempt: " + str(metadata))
            wrapper_attempts.append({"metadata": str(metadata.relative_to(ROOT)),
                                     "returncode": item["returncode"],
                                     "interrupted": item["returncode"] == 130})
            for path in [metadata, log, snapshot]:
                bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    for source in MODULES[:len(MODULE_NAMES)]:
        if re.search(r"\b(?:MxvSource|MatmulInitSource|98)\b", source.read_text()):
            raise ValueError("Benchmark-specific generic module: " + str(source))
    for path in [Path(__file__), ROOT / "toolchain.lock.json", *WORK.iterdir()]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "compiled", "kind": "actual-initialized-source-safe-entry-and-final-pipeline-bridges",
              "new_modules": [str(path.relative_to(ROOT)) for path in MODULES],
              "new_source_lines": sum(len(path.read_text().splitlines()) for path in MODULES),
              "endpoints": endpoints, "endpoint_assumptions": actual,
              "additional_global_axioms": added, "allowed_parent_globals": sorted(allowed),
              "closed_endpoints": sum(not assumptions for assumptions in actual.values()),
              "maximum_endpoint_globals": max(map(len, actual.values())),
              "reachable_source_count": len(seen), "attempts": attempts, "wrapper_attempts": wrapper_attempts,
              "actual_original_case_bindings": ["mxv", "matmul-init"],
              "structural_transport_to_actual_pipeline_Loop": True,
              "literal_OpenScop_export_preserves_original_typed_instructions": True,
              "original_source_execution_licenses_entry_header_read": True,
              "actual_capture_produces_accepted_count_and_source_model_without_numeric_entry_premises": True,
              "capture_acceptance_and_refusal_preserve_public_source_execution": True,
              "accepted_final_candidate_execution_at_actual_parameter": True,
              "candidate_acceptance_existence_or_nonidentity_effect_proved": False,
              "numeric_entry_premises_passed_to_C_user": False,
              "Csem_installation_or_new_native_optimized_case": False,
              "generic_kernel_or_host_changed": False,
              "original_corpus_nonidentity_optimized_cases": 1, "full_goal_complete": False,
              "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
              "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    validate()
    print(json.dumps({"status": "compiled", "source_lines": report["new_source_lines"],
                      "endpoints": len(endpoints), "closed_endpoints": report["closed_endpoints"],
                      "maximum_endpoint_globals": report["maximum_endpoint_globals"],
                      "reachable_sources": len(seen), "bindings": len(bindings),
                      "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
