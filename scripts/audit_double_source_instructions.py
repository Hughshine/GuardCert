"""Audit actual I64 indices, tensor addresses and typed instruction encoding."""

import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_double_assignment_factory as parent
import compile_matmul_installation as compiler
import prove_double_source_instructions as source_proof
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/double-source-instructions/proof-v1"
MODULE_NAMES = ["GuardMemoryLongSourceAffine", "GuardMemoryDoubleSourceAccess",
                "GuardMemoryDoubleAffineSourceAccess", "GuardMemoryDoubleSourceInstruction"]
MODULES = [ROOT / "adapters/compcert-memory" / (name + ".v") for name in MODULE_NAMES]
MODULES += [source_proof.WORK / "OriginalDoubleSourceInstructions.v"]


def validate():
    report = json.loads((WORK / "report.json").read_text())
    if report["status"] != "compiled" or report["additional_global_axioms"]:
        raise ValueError("Invalid typed source instruction checkpoint")
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
    binding = json.loads((source_proof.WORK / "report.json").read_text())
    if binding["status"] != "compiled" or binding["actual_assignment_nodes_compiled"] != 4:
        raise ValueError("Expected all four original source nodes")
    bindings = dict(baseline["bindings"])
    for name, digest in binding["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError("Changed original source proof input: " + name)
        bindings[name] = digest
    for path in [parent.WORK / "report.json", source_proof.WORK / "report.json"]:
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
    markers = [f"DOUBLE_SOURCE_INSTRUCTION_ENDPOINT_{index}" for index in range(len(endpoints)+1)]
    code = ["From GuardMemory Require Import " + " ".join(MODULE_NAMES) + ".",
            "From GuardDoubleInstrProof Require Import OriginalDoubleSourceInstructions."]
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
    for path in [Path(__file__), ROOT / "toolchain.lock.json", *WORK.iterdir()]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "compiled", "kind": "actual-double-source-instruction-data-compiler",
              "new_modules": [str(path.relative_to(ROOT)) for path in MODULES],
              "new_source_lines": sum(len(path.read_text().splitlines()) for path in MODULES),
              "endpoints": endpoints, "endpoint_assumptions": actual,
              "additional_global_axioms": added, "allowed_parent_globals": sorted(allowed),
              "closed_endpoints": sum(not assumptions for assumptions in actual.values()),
              "maximum_endpoint_globals": max(map(len, actual.values())),
              "reachable_source_count": len(seen), "attempts": attempts,
              "actual_original_case_bindings": ["mxv", "matmul-init"],
              "actual_assignment_nodes_compiled": 4, "source_control_dimensions": [1, 2, 2, 3],
              "source_read_counts": [0, 3, 0, 3],
              "source_and_model_directions_proved": True,
              "I64_affine_source_preserves_actual_tree_and_signed_I32_literals": True,
              "tensor_rank_or_source_global_identifiers_hardcoded_in_generic_library": False,
              "layouts_and_accesses_generated_from_actual_AST": True,
              "read_address_receipts_produced_under_checked_metadata_and_dynamic_resolution": True,
              "modular_correspondence_is_a_no_wrap_certificate": False,
              "destination_store_permission_inferred_from_metadata": False,
              "point_bounds_resolution_still_required": True,
              "source_user_supplies_semantic_callbacks": False,
              "generic_kernel_or_host_changed": False, "new_runtime_condition_generated": False,
              "new_complete_source_loop_or_compiler_endpoint": False,
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
