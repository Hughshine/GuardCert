"""Audit complete initialized nests, literal-source transport and source progress."""

import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_initialized_double_reductions as parent
import compile_matmul_installation as compiler
import prove_initialized_double_raw_nests as source_proof
import prove_initialized_double_nests as canonical
import export_initialized_double_raw_sources as exported
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/double-initialized-nests/proof-v1"
MODULE_NAMES = ["GuardMemoryDoubleInitializedNestData", "GuardMemoryDoubleInitializedNestModel",
                "GuardMemoryDoubleInitializedNestExit", "GuardMemoryDoubleInitializedNestSyntax",
                "GuardMemoryDoubleInitializedNestSource", "GuardMemoryDoubleInitializedNestProgress",
                "GuardMemoryDoubleInitializedRawNest", "GuardMemoryDoubleInitializedRawNestProgress"]
MODULES = [ROOT / "adapters/compcert-memory" / (name + ".v") for name in MODULE_NAMES]
MODULES += [canonical.WORK / "OriginalInitializedDoubleNests.v",
            source_proof.WORK / "OriginalInitializedDoubleRawNests.v"]


def validate():
    report = json.loads((WORK / "report.json").read_text())
    if report["status"] != "compiled" or report["additional_global_axioms"]:
        raise ValueError("Invalid initialized nest checkpoint")
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
    binding_path = source_proof.WORK / "report.json"
    binding = json.loads(binding_path.read_text())
    if binding["status"] != "compiled" or binding["actual_original_cases"] != ["mxv", "matmul-init"]:
        raise ValueError("Expected both literal original initialized nests")
    bindings = dict(baseline["bindings"])
    for name, digest in binding["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError("Changed original source proof input: " + name)
        bindings[name] = digest
    for path in [parent.WORK / "report.json", binding_path]:
        bindings[str(path.relative_to(ROOT))] = sha(path)
    flags = source_proof.flags()
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
    markers = [f"DOUBLE_INITIALIZED_NEST_ENDPOINT_{index}" for index in range(len(endpoints)+1)]
    code = ["From GuardMemory Require Import " + " ".join(MODULE_NAMES) + ".",
            "From GuardInitializedNestProof Require Import OriginalInitializedDoubleNests.",
            "From GuardInitializedRawNestProof Require Import OriginalInitializedDoubleRawNests."]
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
        attempts.append({"source": str(snapshot.relative_to(ROOT)), "log": str(log.relative_to(ROOT)),
                         "metadata": str(metadata.relative_to(ROOT)), "returncode": item["returncode"]})
        for path in [snapshot, log, metadata]:
            bindings[str(path.relative_to(ROOT))] = sha(path)
    wrapper_attempts = []
    for directory in [canonical.WORK / "attempts", source_proof.WORK / "attempts"]:
        for metadata in sorted(directory.glob("*.json")):
            item = json.loads(metadata.read_text())
            snapshot, log = metadata.with_suffix(".v"), metadata.with_suffix(".log")
            if not log.exists():
                raise ValueError("Missing wrapper attempt log: " + str(metadata))
            if snapshot.exists() and sha(snapshot) != item["source_sha256"]:
                raise ValueError("Changed wrapper attempt: " + str(metadata))
            wrapper_attempts.append({"metadata": str(metadata.relative_to(ROOT)),
                                     "returncode": item["returncode"], "exported_AST": not snapshot.exists()})
            for path in [metadata, log, *([snapshot] if snapshot.exists() else [])]:
                bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    rejected_export = ROOT / "build/double-initialized-nests/raw-source-v1"
    for path in rejected_export.rglob("*"):
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    for source in MODULES[:len(MODULE_NAMES)]:
        if re.search(r"\b(?:MxvSource|MatmulInitSource|98)\b", source.read_text()):
            raise ValueError("Benchmark-specific generic module: " + str(source))
    for path in [Path(__file__), ROOT / "toolchain.lock.json", *WORK.iterdir()]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "compiled", "kind": "checked-complete-initialized-double-nests-and-literal-progress",
              "new_modules": [str(path.relative_to(ROOT)) for path in MODULES],
              "new_source_lines": sum(len(path.read_text().splitlines()) for path in MODULES),
              "endpoints": endpoints, "endpoint_assumptions": actual,
              "additional_global_axioms": added, "allowed_parent_globals": sorted(allowed),
              "closed_endpoints": sum(not assumptions for assumptions in actual.values()),
              "maximum_endpoint_globals": max(map(len, actual.values())),
              "reachable_source_count": len(seen), "attempts": attempts, "wrapper_attempts": wrapper_attempts,
              "actual_original_case_bindings": ["mxv", "matmul-init"], "outer_control_dimensions": [1, 2],
              "arbitrary_depth_same_header_canonical_and_literal_nest_descriptors": True,
              "ordinary_actual_AST_descriptors_without_semantic_callbacks": True,
              "full_marked_source_model_finite_normal_equivalence": True,
              "full_public_I64_exits_including_unreached_inner_temporaries": True,
              "header_stability_from_checked_global_writes": True,
              "all_point_resolution_produced_from_captured_range_and_actual_100_extent_geometry": True,
              "literal_frontend_skip_transport_preserves_all_finite_traces_and_outcomes": True,
              "literal_and_canonical_small_step_source_progress": True,
              "source_progress_requires_accepted_range_or_header_stability": False,
              "generic_library_hardcodes_benchmark_names_identifiers_or_tensor_rank": False,
              "access_bounds_infer_allocation_or_load_store_permission": False,
              "entry_header_load_and_range_still_logical_premises": True,
              "new_runtime_condition_or_compiler_installation": False,
              "source_user_supplies_semantic_callbacks": False,
              "generic_kernel_or_host_changed": False,
              "original_corpus_nonidentity_optimized_cases": 1,
              "new_native_or_cost_evidence": False, "full_goal_complete": False,
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
