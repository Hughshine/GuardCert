"""Audit source-licensed store-sequence conditions and one loaded-loop prefix step."""
import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_affine_nest_materialized as language
from audit_compiler import names
from audit_interface_clight import ROOT, sha

MODULES = ["prototype/interface/ClightWordStoreSequence.v",
           "prototype/interface/ClightWordStoreSequenceFactory.v",
           "prototype/interface/ClightWordStoreSequenceLoaded.v",
           "prototype/interface/ClightWordStoreSequenceExample.v"]
BASELINE = ROOT / "build/multi-tensor-affine-versioned/proof/report.json"
DEFAULT_WORK = ROOT / "build/multi-word-sequence/proof-v1"
FORBIDDEN = {"ClightWordColumnPrefix", "ClightWordColumnScan",
             "ClightWordColumnSourceExample", "ClightWordComponentFrame",
             "ClightWordComponentScan", "CompCertWordObservationChoices"}
KIND = "actual-store-sequence-guard-and-loaded-source-prefix-step"
FACTS = {
    "kernel_changed": False,
    "host_contract_changed": False,
    "assignment_list_length_fixed": False,
    "store_indices_use_modular_word_arithmetic": True,
    "static_AST_checker_produces_body_obligations": True,
    "later_RHS_reads_use_real_intermediate_memory": True,
    "only_access_permissions_transported_backwards": True,
    "guard_AST_depends_on_runtime_values": False,
    "check_preserves_memory_and_nonflag_temps": True,
    "source_cached_execution_assumed_for_check_licensing": False,
    "loaded_single_axis_prefix_advance_added": True,
    "actual_Clight_source_and_guard_execution_fixtures_proved": True,
    "undefined_entry_read_becomes_defined_after_first_store": True,
    "second_store_header_alias_refused": True,
    "new_complete_nested_loaded_driver": False,
    "new_compiler_or_Csem_to_Asm_endpoint": False,
    "new_native_C_or_assembly_evidence": False,
    "compact_conditions_or_cost_evidence_added": False,
    "source_user_supplies_semantic_callbacks": False,
    "language_and_domain_instantiation_still_require_proofs": True,
}


def permitted(path):
    path = Path(path).resolve()
    assert path.is_relative_to(ROOT), str(path)
    assert path.stem not in FORBIDDEN, "Foreign work is not an input: " + str(path)
    assert not path.is_relative_to(ROOT / "knowledge-base"), str(path)
    return path


def baseline_inputs():
    report = json.loads(BASELINE.read_text())
    assert report["status"] == "compiled" and not report["additional_global_axioms"]
    assert report["compiler_baseline_global_count"] == len(report["compiler_assumptions"]) == 42
    for path, digest in report["bindings"].items():
        assert sha(permitted(ROOT / path)) == digest, path
    return {"report": str(BASELINE.relative_to(ROOT)), "report_sha256": sha(BASELINE),
            "bound_files": len(report["bindings"]),
            "allowed_globals": report["compiler_assumptions"]}


def endpoints():
    return [Path(path).stem + "." + name for path in MODULES for name in
            re.findall(r"^Print Assumptions (\w+)\.", permitted(ROOT / path).read_text(), re.MULTILINE)]


def discover(work, flags):
    """Follow only reachable imports, checking names before reading any source."""
    frontier = [permitted(ROOT / path) for path in MODULES]
    seen = set()
    bindings = {}
    level = 0
    while frontier:
        current = sorted(set(frontier) - seen)
        if not current:
            break
        seen.update(current)
        for source in current:
            obj = permitted(source.with_suffix(".vo"))
            assert obj.exists() and obj.stat().st_mtime >= source.stat().st_mtime, str(source)
            bindings[source] = sha(source)
            bindings[obj] = sha(obj)
        dep = subprocess.run(["rocq", "dep", *flags, *map(str, current)], cwd=ROOT,
                             capture_output=True, text=True)
        (work / f"dependencies-{level}.txt").write_text(dep.stdout)
        (work / f"dependency-warnings-{level}.txt").write_text(dep.stderr)
        assert dep.returncode == 0, dep.stderr
        frontier = []
        for line in dep.stdout.splitlines():
            if ": " not in line:
                continue
            for token in line.split(": ", 1)[1].split():
                if not token.endswith(".vo"):
                    continue
                obj = permitted(ROOT / token)
                bindings[obj] = sha(obj)
                source = permitted(obj.with_suffix(".v"))
                if source.exists() and source not in seen:
                    frontier.append(source)
        level += 1
    (work / "reachable-sources.json").write_text(json.dumps(
        sorted(str(path.relative_to(ROOT)) for path in seen), indent=2) + "\n")
    return bindings


def validate(work=DEFAULT_WORK):
    report = json.loads((work / "report.json").read_text())
    assert report["status"] == "compiled" and report["kind"] == KIND
    assert report["baseline_binding_check"] == baseline_inputs()
    assert report["queried_endpoints"] == endpoints()
    assert set(report["endpoint_assumptions"]) == set(endpoints())
    assert not report["additional_global_axioms"]
    assert all(report[key] == value for key, value in FACTS.items())
    allowed = set(report["baseline_binding_check"]["allowed_globals"])
    assert all(set(values) <= allowed for values in report["endpoint_assumptions"].values())
    assert report["toolchain"] == subprocess.check_output(["rocq", "--version"], text=True).strip()
    for path, digest in report["bindings"].items():
        assert sha(permitted(ROOT / path)) == digest, path
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, default=DEFAULT_WORK)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    work = permitted(args.work)
    if args.validate or (work / "report.json").exists():
        report = validate(work)
        print(json.dumps({"status": "validated", "endpoints": len(report["queried_endpoints"]),
                          "report_sha256": sha(work / "report.json")}))
        return
    baseline = baseline_inputs()
    work.mkdir(parents=True, exist_ok=False)
    flags = language.flags()
    for path in MODULES:
        assert not re.search(r"\b(Admitted|Abort|Axiom|Parameter)\b",
                             permitted(ROOT / path).read_text()), path
    before = discover(work, flags)
    queried = endpoints()
    lines = ["From GuardInterface Require Import " + " ".join(Path(path).stem for path in MODULES) + "."]
    markers = [f"STORE_SEQUENCE_ENDPOINT_{i}" for i in range(len(queried))] + ["STORE_SEQUENCE_END"]
    for marker, endpoint in zip(markers, queried):
        lines += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {endpoint}."]
    lines += [f'Goal True. idtac "{markers[-1]}". exact I. Qed.']
    (work / "Audit.v").write_text("\n".join(lines) + "\n")
    audit = subprocess.run(["rocq", "compile", *flags, str(work / "Audit.v")],
                           cwd=ROOT, capture_output=True, text=True)
    (work / "assumptions.log").write_text(audit.stdout + audit.stderr)
    assert audit.returncode == 0, audit.stderr
    actual = {endpoint: sorted(names(audit.stdout.split(markers[i] + "\n", 1)[1]
                                     .split(markers[i + 1] + "\n", 1)[0]))
              for i, endpoint in enumerate(queried)}
    allowed = set(baseline["allowed_globals"])
    assert all(set(values) <= allowed for values in actual.values()), actual
    assert baseline == baseline_inputs(), "Historical baseline changed"
    assert all(sha(path) == digest for path, digest in before.items()), "Reachable proof input changed"
    bindings = dict(before)
    for helper in (Path(__file__), ROOT / "scripts/compile_word_store_sequence_sources.py"):
        bindings[helper] = sha(helper)
    for path in work.rglob("*"):
        if path.is_file():
            bindings[path] = sha(path)
    report = {"status": "compiled", "kind": KIND, **FACTS,
              "baseline_binding_check": baseline,
              "baseline_transitive_parent_audits_rerun": False,
              "new_modules_reachable_dependency_closure_bound": True,
              "queried_endpoints": queried, "endpoint_assumptions": actual,
              "additional_global_axioms": [],
              "closed_endpoints": sum(not values for values in actual.values()),
              "maximum_endpoint_globals": max(map(len, actual.values())),
              "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
              "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()}}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate(work)
    print(json.dumps({"status": "compiled", "endpoints": len(queried),
                      "closed_endpoints": report["closed_endpoints"],
                      "maximum_endpoint_globals": report["maximum_endpoint_globals"],
                      "bindings": len(bindings), "report_sha256": sha(work / "report.json")}), flush=True)


if __name__ == "__main__":
    main()
