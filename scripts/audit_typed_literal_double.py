"""Audit literal-bound factory installation and its actual current-program compiler."""
import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_fixed_double_installation as parent
import compile_matmul_installation as compiler
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/typed-literal-double/proof-v1"
PORTABLE = ROOT / "docs/typed-literal-double.json"
STEMS = ["GuardMemorySignedLongBoundControl", "GuardMemorySignedBoundLoadedProgress",
    "GuardMemorySignedBoundRawProgress", "GuardMemorySignedBoundRangeProgress"] + [
    "GuardMemoryLiteralDoubleTree"+suffix for suffix in
    ["Data", "Syntax", "Decode", "Cache", "Source", "Progress", "Facts", "Scope", "Execution"]]
INTERFACE_STEMS = ["LiteralDoubleTreeFactory", "LiteralDoubleTreeCompiler", "TypedLiteralCombinedDoubleCompiler"]
MODULES = [ROOT / "adapters/compcert-memory" / (name + ".v") for name in STEMS] + [
    ROOT / "prototype/interface" / (name + ".v") for name in INTERFACE_STEMS]
KIND = "actual-I32-or-I64-literal-bound-current-program-csem-to-asm"
ENTRY = "TypedLiteralCombinedDoubleCompiler.compile_selected_typed_literal_combined_double_program"

FORBIDDEN = {"GuardMemoryDoubleHeaderAffineAccess", "GuardMemorySignedChildLoops",
    "GuardMemorySignedChildSource", "ClightWordColumnPrefix", "ClightWordColumnScan",
    "ClightWordColumnSourceExample", "ClightWordComponentFrame", "CompCertWordObservationChoices",
    "HeaderDoubleQuotientFactoryTrace", "check_double_tiled_contexts", "compile_signed_child_width"}
FACTS = {
    "new_complete_compiler_endpoint": ENTRY+"_correct",
    "new_source_tree_factory_installed": True,
    "factory_discharges_source_model_and_entry_obligations": True,
    "literal_model_parameters_are_actual_C_globals": False,
    "constant_path_requires_dynamic_header_reads": False,
    "actual_I32_source_literals_and_I64_bounds_supported": True,
    "implicit_signed_arithmetic_conversion_and_progress_proved": True,
    "static_refusal_retains_original_source": True,
    "normalization_and_all_passes_use_actual_intermediate_program": True,
    "new_native_source_family_added": False,
    "dynamic_bound_source_family_extended": False,
    "OLO_compact_entry_condition_algorithm_complete": False,
    "kernel_changed": False,
    "additional_host_laws": False,
    "full_goal_complete": False,
}
IMPORTED_ENDPOINTS = {}



def owned(path):
    path = permitted(path)
    if path.stem in FORBIDDEN:
        raise ValueError("Foreign source is not an input: " + str(path))
    return path


def endpoints():
    result = []
    for source in MODULES:
        text = owned(source).read_text()
        if re.search(r"\b(?:Admitted|Abort)\s*\.|^\s*(?:Axiom|Parameter)\s+\w+", text, re.M):
            raise ValueError("Unproved source: " + str(source))
        for name in re.findall(r"^Print Assumptions ([\w.]+)\.", text, re.M):
            if name in IMPORTED_ENDPOINTS:
                result.append(IMPORTED_ENDPOINTS[name])
                continue
            if not re.search(r"\b(?:Theorem|Lemma|Example|Corollary|Definition|Record)\s+"
                             + re.escape(name) + r"\b", text):
                raise ValueError("Missing declaration: " + name)
            result.append(source.stem + "." + name)
    return result


def validate():
    report = json.loads(owned(WORK / "report.json").read_text())
    if (report["status"] != "compiled" or report["kind"] != KIND
            or report["endpoints"] != endpoints() or report["additional_global_axioms"]
            or any(report[key] != value for key, value in FACTS.items())):
        raise ValueError("Invalid endpoint service proof report")
    for name, digest in report["bindings"].items():
        if sha(owned(ROOT / name)) != digest:
            raise ValueError("Changed bound file: " + name)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate:
        report = validate()
        print(json.dumps({"status": "validated", "bindings": len(report["bindings"])}))
        return
    baseline = parent.validate()
    for name in baseline["bindings"]:
        owned(ROOT / name)
    allowed = set(baseline["allowed_parent_globals"])
    WORK.mkdir(parents=True, exist_ok=False)
    bindings = dict(baseline["bindings"])
    bindings[str((parent.WORK / "report.json").relative_to(ROOT))] = sha(parent.WORK / "report.json")
    flags = compiler.lowering.flags()
    frontier, seen, level = MODULES, set(), 0
    while frontier:
        current = sorted(set(frontier) - seen)
        if not current:
            break
        seen.update(current)
        for source in current:
            source, obj = owned(source), owned(source.with_suffix(".vo"))
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
                    obj = owned(ROOT / token)
                    bindings[str(obj.relative_to(ROOT))] = sha(obj)
                    source = owned(obj.with_suffix(".v"))
                    if source.exists() and source not in seen:
                        frontier.append(source)
        level += 1
    queried = endpoints()
    markers = [f"SOURCE_ENDPOINT_{i}" for i in range(len(queried) + 1)]
    code = ["From GuardMemory Require Import " + " ".join(STEMS) + ".",
            "From GuardInterface Require Import " + " ".join(INTERFACE_STEMS) + "."]
    for marker, endpoint in zip(markers, queried):
        code += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {endpoint}."]
    code += [f'Goal True. idtac "{markers[-1]}". exact I. Qed.']
    (WORK / "Audit.v").write_text("\n".join(code) + "\n")
    run = subprocess.run(["rocq", "compile", *flags, str(WORK / "Audit.v")], cwd=ROOT,
                         capture_output=True, text=True)
    (WORK / "assumptions.log").write_text(run.stdout + run.stderr)
    if run.returncode:
        raise ValueError(run.stderr)
    actual = {endpoint: sorted(names(run.stdout.split(markers[i] + "\n", 1)[1]
                                    .split(markers[i + 1] + "\n", 1)[0]))
              for i, endpoint in enumerate(queried)}
    added = sorted(set().union(*map(set, actual.values())) - allowed)
    if added:
        raise ValueError("New globals: " + str(added))
    attempts = []
    for source in MODULES:
        succeeded = False
        for metadata in sorted(compiler.WORK.glob(source.stem + "-v*.json")):
            item = json.loads(owned(metadata).read_text())
            if sha(owned(metadata.with_suffix(".v"))) != item["source_sha256"]:
                raise ValueError("Changed attempt: " + str(metadata))
            if item["returncode"] == 0:
                succeeded = True
                if item["source_sha256"] != sha(source):
                    raise ValueError("Successful proof source changed: " + str(source))
            attempts.append({"module": source.stem, "compiled": item["returncode"] == 0,
                             "metadata": str(metadata.relative_to(ROOT))})
            for path in [metadata, metadata.with_suffix(".v"), metadata.with_suffix(".log")]:
                bindings[str(path.relative_to(ROOT))] = sha(owned(path))
        if not succeeded:
            raise ValueError("No recorded successful compilation: " + str(source))
    for path in [Path(__file__), ROOT / "scripts/compile_matmul_installation.py",
                 ROOT / "toolchain.lock.json", *WORK.iterdir()]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(owned(path))
    report = {"status": "compiled", "kind": KIND,
              "new_modules": [str(p.relative_to(ROOT)) for p in MODULES],
              "new_source_lines": sum(len(owned(p).read_text().splitlines()) for p in MODULES),
              "endpoints": queried, "imported_endpoints": sorted(IMPORTED_ENDPOINTS.values()),
              "new_endpoint_count": len(queried)-len(IMPORTED_ENDPOINTS), "endpoint_assumptions": actual, "additional_global_axioms": added,
              "allowed_parent_globals": sorted(allowed), "closed_endpoints": sum(not x for x in actual.values()),
              "maximum_endpoint_globals": max(map(len, actual.values())), "reachable_source_count": len(seen),
              "attempts": attempts, "baseline_compiler_endpoint": baseline["baseline_compiler_endpoint"], **FACTS, "bindings": bindings}
    portable = {k: v for k, v in report.items()
                if k not in {"bindings", "endpoint_assumptions", "allowed_parent_globals"}}
    portable["report"] = str((WORK / "report.json").relative_to(ROOT))
    with PORTABLE.open("x") as out:
        out.write(json.dumps(portable, indent=2) + "\n")
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "compiled", "source_lines": report["new_source_lines"],
                      "endpoints": len(queried), "closed": report["closed_endpoints"],
                      "maximum_globals": report["maximum_endpoint_globals"], "bindings": len(bindings)}))


if __name__ == "__main__":
    main()
