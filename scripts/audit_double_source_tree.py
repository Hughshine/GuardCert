"""Audit checked whole-source trees, raw header effects and independent source progress."""

import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_signed_range_source as parent
import compile_matmul_installation as compiler
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/double-source-tree/proof-v1"
PORTABLE = ROOT / "docs/double-source-tree.json"
MODULES = [ROOT / "theories/ClightStructuredMemoryFrame.v"] + [ROOT / "adapters/compcert-memory" / (name+".v") for name in [
    "GuardMemoryDoubleSourceTreeData", "GuardMemoryDoubleRawEffects", "GuardMemoryDoubleSourceTreeEffects",
    "GuardMemoryDoubleSourceTreeProgress", "GuardMemoryDoubleSourceTreeDecode", "GuardMemoryDoubleSourceTreeCertificates"]]
KIND = "checked-whole-source-tree-raw-effects-progress-checkpoint"


def endpoints():
    queried = []
    for source in MODULES:
        content = permitted(source).read_text()
        if re.search(r"\b(?:Admitted|Abort|Axiom|Parameter)\b", content):
            raise ValueError("Unproved service source: " + str(source))
        for name in re.findall(r"^Print Assumptions ([\w.]+)\.", content, re.MULTILINE):
            if not re.search(r"\b(?:Theorem|Lemma|Example|Corollary|Definition|Record)\s+"
                             + re.escape(name) + r"\b", content):
                raise ValueError("Missing declaration: " + name)
            queried.append(source.stem + "." + name)
    return queried


def validate():
    report = json.loads(permitted(WORK / "report.json").read_text())
    if (report["status"] != "compiled" or report["kind"] != KIND
            or report["additional_global_axioms"]
            or report["endpoints"] != endpoints()
            or report["installed_factory_consumes_new_source_tree"]):
        raise ValueError("Invalid whole source tree checkpoint")
    for path, digest in report["bindings"].items():
        if sha(permitted(ROOT / path)) != digest:
            raise ValueError("Changed service input: " + path)
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
    baseline = parent.validate()
    allowed = set(baseline["allowed_parent_globals"])
    if len(allowed) != 42:
        raise ValueError("Wrong inherited compiler baseline")
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
    queried = endpoints()
    markers = [f"RECTANGULAR_INSTALLATION_ENDPOINT_{i}" for i in range(len(queried) + 1)]
    code = []
    for prefix, directory in [("Guard", "theories"), ("GuardMemory", "adapters/compcert-memory"), ("GuardInterface", "prototype/interface")]:
        active = [path.stem for path in MODULES if path.parent == ROOT / directory]
        if active:
            code.append("From " + prefix + " Require Import " + " ".join(active) + ".")
    for marker, endpoint in zip(markers, queried):
        code += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {endpoint}."]
    code += [f'Goal True. idtac "{markers[-1]}". exact I. Qed.']
    (WORK / "Audit.v").write_text("\n".join(code) + "\n")
    run = subprocess.run(["rocq", "compile", *flags, str(WORK / "Audit.v")],
                         cwd=ROOT, capture_output=True, text=True)
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
    for metadata in sorted(path for source in MODULES for path in compiler.WORK.glob(source.stem+"-v*.json")):
        item = json.loads(permitted(metadata).read_text())
        if Path(item["source"]) not in {path.relative_to(ROOT) for path in MODULES}:
            continue
        snapshot, log = metadata.with_suffix(".v"), metadata.with_suffix(".log")
        if sha(permitted(snapshot)) != item["source_sha256"]:
            raise ValueError("Changed attempt: " + str(metadata))
        attempts.append({"source": str(snapshot.relative_to(ROOT)),
                         "log": str(log.relative_to(ROOT)),
                         "metadata": str(metadata.relative_to(ROOT)),
                         "compiled": item["returncode"] == 0})
        for path in [snapshot, log, metadata]:
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    for path in [Path(__file__), Path(compiler.__file__), ROOT / "toolchain.lock.json", *WORK.iterdir()]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    fixtures_path = ROOT / "build/double-source-tree/source-attempts/source-v2/report.json"
    fixtures = json.loads(permitted(fixtures_path).read_text())
    if fixtures["status"] != "checked" or len(fixtures["cases"]) != 3:
        raise ValueError("Original source-tree checks incomplete")
    for path,digest in fixtures["bindings"].items():
        if sha(permitted(ROOT / path)) != digest:
            raise ValueError("Changed source-tree fixture: " + path)
        bindings[path] = digest
    bindings[str(fixtures_path.relative_to(ROOT))] = sha(fixtures_path)
    failed = ROOT / "build/double-source-tree/source-attempts/source-v1"
    failed_report = json.loads(permitted(failed / "report.json").read_text())
    snapshot = permitted(failed / "check-script.py")
    if sha(snapshot) != failed_report["bindings"]["scripts/check_double_source_trees.py"]:
        raise ValueError("Changed initial fixture helper snapshot")
    for path in failed.rglob("*"):
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "compiled", "kind": KIND,
              "new_modules": [str(path.relative_to(ROOT)) for path in MODULES],
              "new_source_lines": sum(len(permitted(path).read_text().splitlines()) for path in MODULES),
              "endpoints": queried, "endpoint_assumptions": actual,
              "additional_global_axioms": added, "allowed_parent_globals": sorted(allowed),
              "closed_endpoints": sum(not values for values in actual.values()),
              "maximum_endpoint_globals": max(map(len, actual.values())),
              "reachable_source_count": len(seen), "attempts": attempts,
              "kernel_changed": False, "new_host_contract": False,
              "checked_actual_statement_reconstruction": True,
              "sequences_and_heterogeneous_loop_depth_preserved": True,
              "shared_parameter_and_layout_registries_checked": True,
              "raw_source_global_write_block_proved": True,
              "header_loads_preserved_without_accepted_point_resolution": True,
              "actual_source_store_permissions_preserved": True,
              "strict_source_progress_independent_of_guard_acceptance": True,
              "checked_decoder_produces_progress_header_and_layout_certificates": True,
              "new_language_structured_effect_service": True,
              "original_marked_source_checks": [{key: item[key] for key in ["case", "source_tree_summaries"]}
                                                 for item in fixtures["cases"]],
              "source_check_report": str(fixtures_path.relative_to(ROOT)),
              "initial_missing_Pos_import_probe_failure_retained": True,
              "installed_factory_consumes_new_source_tree": False,
              "new_tree_source_model_execution_correspondence_proved": False,
              "path_sensitive_multi_header_capture_installed": False,
              "all_source_model_premises_closed_by_new_factory": False,
              "new_complete_compiler_endpoint_added": False,
              "native_source_coverage_added": False,
              "native_or_cost_evidence_added_by_audit": False,
              "inclusive_source_progress_proved": False,
              "mixed_statement_region_optimization_installed": False,
              "full_goal_complete": False,
              "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
              "bindings": bindings}
    portable = {key: value for key,value in report.items() if key not in {"bindings","endpoint_assumptions","allowed_parent_globals"}}
    portable["report"] = str((WORK / "report.json").relative_to(ROOT))
    portable["report_bindings_before_portable"] = len(bindings)
    with PORTABLE.open("x") as out:
        out.write(json.dumps(portable, indent=2)+"\n")
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(permitted(PORTABLE))
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "compiled", "source_lines": report["new_source_lines"],
                      "endpoints": len(queried), "closed_endpoints": report["closed_endpoints"],
                      "maximum_endpoint_globals": report["maximum_endpoint_globals"],
                      "reachable_sources": len(seen), "bindings": len(bindings)}))


if __name__ == "__main__":
    main()
