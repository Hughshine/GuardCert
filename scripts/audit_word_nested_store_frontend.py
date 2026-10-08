"""Audit original loaded source to checked candidate, region guarantee and selected compiler."""
import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_affine_nest_materialized as language
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

MODULES = ["prototype/interface/ClightWordNestedStoreFrontend.v",
           "prototype/interface/ClightSelectedWordNestedStoreFrontendCompiler.v"]
PARENT = ROOT / "build/multi-word-nested-affine/proof-v1/report.json"
DEFAULT_WORK = ROOT / "build/multi-word-nested-frontend/proof-v1"
KIND = "administrative-frontend-to-loaded-affine-selected-compiler"
FACTS = {
    "kernel_changed": False,
    "host_contract_changed": False,
    "actual_source_rank": 2,
    "frontend_administrative_skips_normalized_by_proved_language_service": True,
    "normalization_preserves_temporary_scope": True,
    "fallback_keeps_original_loaded_observations": True,
    "fallback_only_administrative_AST_normalization": True,
    "ordinary_metadata_and_candidate_proposers_quantified": True,
    "source_user_semantic_callback_API_added": False,
    "original_frontend_progress_still_checked_by_host": True,
    "projected_guarantee_transported_to_original_frontend_source": True,
    "new_Csem_to_Asm_endpoint": True,
    "new_native_or_cost_evidence": False,
}

def parent_inputs():
    report = json.loads(PARENT.read_text())
    assert report["status"] == "compiled" and not report["additional_global_axioms"]
    assert report["new_modules_reachable_dependency_closure_bound"]
    for path, digest in report["bindings"].items():
        assert sha(permitted(ROOT / path)) == digest, path
    allowed = report["parent_binding_check"]["allowed_globals"]
    assert len(allowed) == 42
    return {"report": str(PARENT.relative_to(ROOT)), "report_sha256": sha(PARENT),
            "bound_files": len(report["bindings"]), "allowed_globals": allowed}


def endpoints():
    return [Path(path).stem + "." + name for path in MODULES for name in
            re.findall(r"^Print Assumptions (\w+)\.", permitted(ROOT / path).read_text(), re.MULTILINE)]


def discover(work, flags):
    frontier = [permitted(ROOT / path) for path in MODULES]
    seen, bindings, level = set(), {}, 0
    while frontier:
        current = sorted(set(frontier) - seen)
        if not current:
            break
        seen.update(current)
        for source in current:
            obj = permitted(source.with_suffix(".vo"))
            assert obj.exists() and obj.stat().st_mtime >= source.stat().st_mtime, str(source)
            bindings[source], bindings[obj] = sha(source), sha(obj)
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
                if token.endswith(".vo"):
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
    assert report["parent_binding_check"] == parent_inputs()
    assert report["queried_endpoints"] == endpoints()
    assert set(report["endpoint_assumptions"]) == set(endpoints())
    assert not report["additional_global_axioms"]
    assert all(report[key] == value for key, value in FACTS.items())
    allowed = set(report["parent_binding_check"]["allowed_globals"])
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
    parent = parent_inputs()
    work.mkdir(parents=True, exist_ok=False)
    flags = language.flags()
    for file in MODULES:
        assert not re.search(r"\b(Admitted|Abort|Axiom|Parameter)\b", permitted(ROOT / file).read_text()), file
    before = discover(work, flags)
    queried = endpoints()
    lines = ["From GuardInterface Require Import " + " ".join(Path(path).stem for path in MODULES) + "."]
    markers = [f"NESTED_AFFINE_ENDPOINT_{i}" for i in range(len(queried))] + ["NESTED_AFFINE_END"]
    for marker, endpoint in zip(markers, queried):
        lines += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {endpoint}."]
    lines += [f'Goal True. idtac "{markers[-1]}". exact I. Qed.']
    (work / "Audit.v").write_text("\n".join(lines) + "\n")
    audit = subprocess.run(["rocq", "compile", *flags, str(work / "Audit.v")], cwd=ROOT,
                           capture_output=True, text=True)
    (work / "assumptions.log").write_text(audit.stdout + audit.stderr)
    assert audit.returncode == 0, audit.stderr
    actual = {endpoint: sorted(names(audit.stdout.split(markers[i] + "\n", 1)[1]
                                     .split(markers[i + 1] + "\n", 1)[0]))
              for i, endpoint in enumerate(queried)}
    allowed = set(parent["allowed_globals"])
    assert all(set(values) <= allowed for values in actual.values()), actual
    assert parent == parent_inputs(), "Historical parent changed"
    assert all(sha(path) == digest for path, digest in before.items()), "Reachable proof input changed"
    bindings = dict(before)
    for helper in (Path(__file__), ROOT / "scripts/compile_word_nested_store_frontend_sources.py"):
        bindings[helper] = sha(helper)
    for path in work.rglob("*"):
        if path.is_file():
            bindings[path] = sha(path)
    report = {"status": "compiled", "kind": KIND, **FACTS,
              "parent_binding_check": parent,
              "parent_endpoints_inherited_from_frozen_report": True,
              "historical_transitive_audits_rerun": False,
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
                      "bound_files": len(report["bindings"]), "report_sha256": sha(work / "report.json")}))


if __name__ == "__main__":
    main()
