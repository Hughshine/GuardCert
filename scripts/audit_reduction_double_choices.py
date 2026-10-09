"""Audit generic pure double-assignment-nest factory and annotation-sensitive Csem-to-Asm compiler."""

import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_reduction_double_installation as parent
import compile_matmul_installation as compiler
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/double-reduction-nests/choices-proof-v1"
MODULES = [ROOT / "prototype/interface/ReductionDoubleWitnessCompiler.v",
           ROOT / "prototype/interface/ReductionDoubleChoicesCompiler.v"]
ENTRY = "ReductionDoubleChoicesCompiler.compile_selected_reduction_choices_program"


def validate():
    report = json.loads((WORK / "report.json").read_text())
    if report["status"] != "compiled" or report["additional_global_axioms"]:
        raise ValueError("Invalid whole-program original matmul installation checkpoint")
    for name, digest in report["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError(f"Changed proof input: {name}")
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
    flags = compiler.lowering.flags()
    WORK.mkdir(parents=True)
    endpoints = []
    for source in MODULES:
        content = permitted(source).read_text()
        if re.search(r"\b(?:Admitted|Abort|Axiom)\b", content):
            raise ValueError(f"Unproved source: {source}")
        module = "ScopedSelectedRegionProof." if source.stem == "ClightScopedSelectedRegionProof" else ""
        endpoints += [source.stem + "." + module + name for name in
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
    markers = [f"ORIGINAL_MATMUL_INSTALLATION_ENDPOINT_{index}" for index in range(len(endpoints) + 1)]
    code = ["From GuardInterface Require Import ReductionDoubleWitnessCompiler ReductionDoubleChoicesCompiler."]
    for marker, endpoint in zip(markers, endpoints):
        code += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {endpoint}."]
    code += [f'Goal True. idtac "{markers[-1]}". exact I. Qed.']
    (WORK / "Audit.v").write_text("\n".join(code) + "\n")
    run = subprocess.run(["rocq", "compile", *flags, str(WORK / "Audit.v")], cwd=ROOT,
                         capture_output=True, text=True)
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
    for metadata in sorted(compiler.WORK.glob("*.json")):
        item = json.loads(metadata.read_text())
        if Path(item["source"]) not in {path.relative_to(ROOT) for path in MODULES}:
            continue
        source, log = metadata.with_suffix(".v"), metadata.with_suffix(".log")
        if not source.exists() or not log.exists() or sha(source) != item["source_sha256"]:
            raise ValueError(f"Incomplete attempt: {metadata}")
        attempts.append({"source": str(source.relative_to(ROOT)), "log": str(log.relative_to(ROOT)),
                         "metadata": str(metadata.relative_to(ROOT)), "compiled": item["returncode"] == 0})
        for path in [source, log, metadata]:
            bindings[str(path.relative_to(ROOT))] = sha(path)
    for path in [Path(__file__), Path(compiler.__file__), ROOT / "toolchain.lock.json", *WORK.iterdir()]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status":"compiled", "kind":"per-site-untrusted-coordinate-witness-choices-scoped-csem-to-asm",
              "new_modules":[str(path.relative_to(ROOT)) for path in MODULES],
              "new_source_lines":sum(len(path.read_text().splitlines()) for path in MODULES),
              "endpoints":endpoints, "endpoint_assumptions":actual,
              "additional_global_axioms":added, "allowed_parent_globals":sorted(allowed),
              "closed_endpoints":sum(not globals for globals in actual.values()),
              "maximum_endpoint_globals":max(map(len,actual.values())),
              "reachable_source_count":len(seen), "attempts":attempts,
              "whole_program_entrypoint":ENTRY, "whole_program_theorem":ENTRY+"_correct",
              "actual_program_source_metadata_checked":True,
              "source_family":"nonempty I64 nests with one stable global bound and one checked double assignment; no per-row initializer required",
              "common_bound_limit_proposed_and_rechecked_from_actual_footprints":True,
              "bound_proposal_maximality_assumed":False,
              "actual_tensor_layout_span_and_local_scope_checked":True,
              "fixed_benchmark_identifiers_or_layouts_in_new_factory":False,
              "private_names_allocated_from_actual_public_scope":True,
              "scratch_pool_count_is_a_resource_parameter":True,
              "safe_capture_produced_from_original_execution":True,
              "capture_acceptance_produces_count_and_all_point_bounds":True,
              "fallback_source_and_public_exits_preserved":True,
              "independent_actual_source_progress_producer":True,
              "source_model_guard_lowering_and_host_premises_discharged_in_factory":True,
              "source_user_supplies_semantic_callbacks":False,
              "actual_PolCert_Pluto_candidate_pipeline_consumed":True,
              "multiple_annotated_sites_and_existing_double_routes_compose":True, "per_site_coordinate_witness_choices_rechecked":True,
              "complete_program_Csem_to_Asm_endpoint_added":True,
              "generic_kernel_changed":False,
              "new_native_or_cost_evidence":False,
              "installed_original_benchmark_coverage_increased":False,
              "full_goal_complete":False,
              "toolchain":subprocess.check_output(["rocq","--version"],text=True).strip(),
              "bindings":bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "compiled", "source_lines": report["new_source_lines"],
                      "endpoints": len(endpoints), "closed_endpoints": report["closed_endpoints"],
                      "maximum_endpoint_globals": report["maximum_endpoint_globals"],
                      "reachable_sources": len(seen), "bindings": len(bindings),
                      "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
