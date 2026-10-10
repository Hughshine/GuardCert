"""Audit generated whole-tree capture, source-licensed safety, acceptance receipts and fallback replay."""

import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_double_tree_correspondence as parent
import compile_matmul_installation as compiler
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/double-tree-capture/proof-v1"
PORTABLE = ROOT / "docs/double-tree-capture.json"
STEMS = ["GuardMemoryDoubleTreeCaptureLicense", "GuardMemoryDoubleTreeCaptureData",
         "GuardMemoryDoubleTreeCaptureControl", "GuardMemoryDoubleTreeCaptureReceipt",
         "GuardMemoryDoubleTreeCaptureSource", "GuardMemoryDoubleTreeCaptureFacts",
         "GuardMemoryDoubleTreeCapturePrepared", "GuardMemoryDoubleTreeCaptureBoundaryCases"]
MODULES = [ROOT / "adapters/compcert-memory" / (name + ".v") for name in STEMS]
KIND = "generated-path-sensitive-whole-source-tree-capture-checkpoint"
FIXTURES = ROOT / "build/double-tree-capture/source-attempts/source-v1/report.json"


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
    if (report["status"] != "compiled" or report["kind"] != KIND or report["additional_global_axioms"]
            or report["endpoints"] != endpoints() or not report["generated_source_licensed_capture_execution_proved"]
            or report["installed_factory_closes_new_dynamic_premises"] or report["full_goal_complete"]):
        raise ValueError("Invalid generated source-tree capture checkpoint")
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
    fixtures = json.loads(permitted(FIXTURES).read_text())
    if fixtures["status"] != "checked" or len(fixtures["cases"]) != 3:
        raise ValueError("Original conditional-correspondence instances incomplete")
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
            source, obj = permitted(source), permitted(source.with_suffix(".vo"))
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
    code = ["From GuardMemory Require Import " + " ".join(STEMS) + "."]
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
                                   .split(markers[i + 1] + "\n", 1)[0])) for i, endpoint in enumerate(queried)}
    added = sorted(set().union(*map(set, actual.values())) - allowed)
    if added:
        raise ValueError("New globals: " + str(added))
    attempts = []
    for metadata in sorted(path for source in MODULES for path in compiler.WORK.glob(source.stem + "-v*.json")):
        item = json.loads(permitted(metadata).read_text())
        if Path(item["source"]) not in {path.relative_to(ROOT) for path in MODULES}:
            continue
        snapshot, log = metadata.with_suffix(".v"), metadata.with_suffix(".log")
        if sha(permitted(snapshot)) != item["source_sha256"]:
            raise ValueError("Changed attempt: " + str(metadata))
        attempts.append({"source": str(snapshot.relative_to(ROOT)), "log": str(log.relative_to(ROOT)),
                         "metadata": str(metadata.relative_to(ROOT)), "compiled": item["returncode"] == 0})
        for path in [snapshot, log, metadata]:
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    for path, digest in fixtures["bindings"].items():
        if sha(permitted(ROOT / path)) != digest:
            raise ValueError("Changed original correspondence fixture: " + path)
        bindings[path] = digest
    bindings[str(FIXTURES.relative_to(ROOT))] = sha(FIXTURES)
    for path in [Path(__file__), Path(compiler.__file__), ROOT / "toolchain.lock.json", *WORK.iterdir()]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "compiled", "kind": KIND,
              "new_modules": [str(path.relative_to(ROOT)) for path in MODULES],
              "new_source_lines": sum(len(permitted(path).read_text().splitlines()) for path in MODULES),
              "endpoints": queried, "endpoint_assumptions": actual, "additional_global_axioms": added,
              "allowed_parent_globals": sorted(allowed), "closed_endpoints": sum(not values for values in actual.values()),
              "maximum_endpoint_globals": max(map(len, actual.values())), "reachable_source_count": len(seen), "attempts": attempts,
              "kernel_changed": False, "new_host_contract": False,
              "generated_source_licensed_capture_execution_proved": True,
              "raw_later_sibling_load_transport_consumed": True,
              "unreached_children_and_refused_suffixes_skip_header_reads": True,
              "readonly_memory_and_private_temporary_frame_proved": True,
              "accepted_active_header_words_and_I64_bound_ranges_proved": True,
              "original_source_fallback_replay_and_public_exits_proved": True,
              "source_preexecution_emitted": False,
              "shared_headers_recaptured": True, "OLO_compact_condition_algorithm_complete": False,
              "original_capture_instances": fixtures["cases"],
              "source_check_report": str(FIXTURES.relative_to(ROOT)),
              "installed_factory_closes_new_dynamic_premises": False,
              "path_sensitive_capture_installed_in_whole_program_compiler": False,
              "final_shared_cache_parameter_vector_correspondence_proved": False,
              "point_resolution_and_candidate_machine_ranges_derived": False,
              "new_complete_compiler_endpoint_added": False, "native_source_coverage_added": False,
              "new_cost_evidence": False, "mixed_statement_optimization_installed": False, "full_goal_complete": False,
              "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(), "bindings": bindings}
    portable = {key: value for key, value in report.items() if key not in {"bindings", "endpoint_assumptions", "allowed_parent_globals"}}
    portable["report"] = str((WORK / "report.json").relative_to(ROOT))
    portable["report_bindings_before_portable"] = len(bindings)
    with PORTABLE.open("x") as out:
        out.write(json.dumps(portable, indent=2) + "\n")
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "compiled", "source_lines": report["new_source_lines"], "endpoints": len(queried),
                      "closed_endpoints": report["closed_endpoints"], "maximum_endpoint_globals": report["maximum_endpoint_globals"],
                      "reachable_sources": len(seen), "bindings": len(bindings)}))


if __name__ == "__main__":
    main()
