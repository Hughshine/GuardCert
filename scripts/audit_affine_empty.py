"""Audit header-only empty affine rewrites and their selected Csem-to-Asm installation.

Bind the reachable language/domain proofs and preserved attempts. This stage
connects actual original-source checks, candidate verification, guarded fallback
and selected installation. Native execution and cost are separate evidence.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess

import prepare_loaded_affine_compat as language
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

MODULES = ['prototype/interface/ClightAffineEmptyWidth.v', 'prototype/interface/ClightAffineEmptyExecution.v', 'prototype/interface/ClightAffineEmptySnapshotCondition.v', 'prototype/interface/ClightAffineEmptySnapshotSource.v', 'prototype/interface/ClightAffineEmptyRestore.v', 'prototype/interface/ClightAffineOuterEmpty.v', 'prototype/interface/ClightAffineEmptySnapshotRewrite.v', 'prototype/interface/ClightAffineEmptySnapshotCapture.v', 'prototype/interface/ClightAffineEmptySnapshotBuilder.v', 'prototype/interface/ClightSelectedEmptySnapshotCompiler.v']
PARENT=ROOT / "build/affine-observation/proof-v1/report.json"
DEFAULT_WORK=ROOT / "build/affine-empty/proof-v1"
KIND="header-only-empty-affine-selected-installation"
FACTS={'kernel_changed': False, 'host_contract_changed': False, 'underlying_candidate_validators_changed': False, 'original_loaded_source_receipts_produce_header_words': True, 'header_only_affine_endpoint_condition': True, 'negative_child_widths_supported': True, 'outer_empty_skips_child_observation': True, 'all_empty_bypasses_body_input_definedness': True, 'actual_public_empty_exits_proved': True, 'actual_original_fallback': True, 'selected_Csem_to_Asm_endpoint_connected': True, 'existing_registry_has_static_priority': True, 'previously_handled_sites_receive_no_new_runtime_empty_branch': True, 'new_source_user_semantic_callback_API_added': False, 'new_native_acceptance_evidence_in_this_proof_report': False, 'full_goal_complete': False}


def parent_inputs():
    language.validate()
    report = json.loads(PARENT.read_text())
    assert report["status"] == "compiled" and not report["additional_global_axioms"]
    assert report["new_modules_reachable_dependency_closure_bound"]
    for path, digest in report["bindings"].items():
        assert sha(permitted(ROOT / path)) == digest, path
    allowed = report["parent_binding_check"]["allowed_globals"]
    assert len(allowed) == 42
    return {"report": str(PARENT.relative_to(ROOT)), "report_sha256": sha(PARENT),
            "bound_files": len(report["bindings"]), "allowed_globals": allowed,
            "compatibility_report_sha256": sha(language.WORK / "report.json")}


def endpoints():
    result = []
    for path in MODULES:
        source = permitted(ROOT / path).read_text()
        declared = set(re.findall(r"^(?:Theorem|Lemma|Definition|Example) (\w+)\b", source, re.MULTILINE))
        for name in re.findall(r"^Print Assumptions (\w+)\.", source, re.MULTILINE):
            if name in declared:
                result.append(Path(path).stem + "." + name)
    return result


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
    lines = []
    for prefix, namespace in (("adapters/compcert-memory/", "GuardMemory"),
                              ("prototype/interface/", "GuardInterface")):
        selected = [Path(path).stem for path in MODULES if path.startswith(prefix)]
        if selected:
            lines.append("From " + namespace + " Require Import " + " ".join(selected) + ".")
    markers = [f"AFFINE_EMPTY_ENDPOINT_{i}" for i in range(len(queried))] + ["AFFINE_EMPTY_END"]
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
    attempts = []
    for snapshot in sorted((ROOT / "build/affine-empty/source-build").glob("*.v")):
        log = snapshot.with_suffix(".log")
        assert log.exists(), snapshot
        success = "Error:" not in log.read_text()
        attempts.append({"source": str(snapshot.relative_to(ROOT)),
                         "log": str(log.relative_to(ROOT)),
                         "successful": success,
                         "diagnostic_kind": "compiled" if success else "proof-source-rejected"})
        bindings[snapshot], bindings[log] = sha(snapshot), sha(log)
    for helper in (Path(__file__), ROOT / "scripts/compile_affine_empty.py",
                   ROOT / "scripts/prepare_loaded_affine_compat.py", language.WORK / "report.json"):
        bindings[helper] = sha(helper)
    for file in MODULES:
        obj = ROOT / Path(file).with_suffix(".vo")
        successful = [snapshot for snapshot in (ROOT / "build/affine-empty/source-build").glob(Path(file).stem + "-*.v")
                      if snapshot.read_bytes() == (ROOT / file).read_bytes()
                      and snapshot.with_suffix(".log").exists()
                      and "Error:" not in snapshot.with_suffix(".log").read_text()
                      and snapshot.stat().st_mtime <= obj.stat().st_mtime]
        assert len(successful) == 1, (file, successful)
        for path in (successful[0], successful[0].with_suffix(".log")):
            bindings[path] = sha(path)
    for path in work.rglob("*"):
        if path.is_file():
            bindings[path] = sha(path)
    report = {"status": "compiled", "kind": KIND, **FACTS,
              "parent_binding_check": parent,
              "parent_endpoints_inherited_from_frozen_report": True,
              "historical_transitive_audits_rerun": False,
              "new_modules_reachable_dependency_closure_bound": True,
              "queried_endpoints": queried, "endpoint_assumptions": actual,
              "preserved_source_build_attempts": attempts,
              "preserved_failed_audit_runs": [],
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
