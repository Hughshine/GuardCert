"""Bind sequential source-tree and established typed-double pass composition."""
import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_double_tree_residual as parent
import compile_matmul_installation as compiler
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/double-tree-combined-residual/proof-v1"
PORTABLE = ROOT / "docs/double-tree-combined-residual.json"
STEMS = []
INTERFACES = ["CombinedDoubleTreeResidualCompiler"]
MODULES = [ROOT / "prototype/interface/CombinedDoubleTreeResidualCompiler.v"]
ENTRY = "CombinedDoubleTreeResidualCompiler.compile_selected_combined_residual_double_program_correct"


def endpoints():
    result = []
    for source in MODULES:
        text = permitted(source).read_text()
        if re.search(r"\b(?:Admitted|Abort)\s*\.|^\s*(?:Axiom|Parameter)\s+\w+", text, re.M):
            raise ValueError("Unproved source: "+str(source))
        for name in re.findall(r"^Print Assumptions ([\w.]+)\.", text, re.M):
            if not re.search(r"\b(?:Theorem|Lemma|Example|Corollary|Definition|Record)\s+"
                             +re.escape(name)+r"\b", text):
                raise ValueError("Missing declaration: "+name)
            result.append(source.stem+"."+name)
    return result


def validate():
    report = json.loads(permitted(WORK / "report.json").read_text())
    if (report["status"] != "compiled" or report["endpoints"] != endpoints()
            or report["additional_global_axioms"] or report["complete_compiler_endpoint"] != ENTRY
            or report["full_goal_complete"]):
        raise ValueError("Invalid body-pruning compiler proof report")
    for name, digest in report["bindings"].items():
        if sha(permitted(ROOT/name)) != digest:
            raise ValueError("Changed bound file: "+name)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate:
        report = validate()
        print(json.dumps({"status":"validated","bindings":len(report["bindings"])}))
        return
    if permitted(ROOT / "theories/ResidualGuard.v").read_bytes() != permitted(ROOT / "theories/ResidualGuardCurrent.v").read_bytes():
        raise ValueError("Residual library successor must be a byte-identical dependency rebuild")
    baseline = parent.validate()
    allowed = set(baseline["allowed_parent_globals"])
    WORK.mkdir(parents=True, exist_ok=False)
    bindings = dict(baseline["bindings"])
    bindings[str((parent.WORK/"report.json").relative_to(ROOT))] = sha(parent.WORK/"report.json")
    bindings["theories/ResidualGuard.v"] = sha(permitted(ROOT / "theories/ResidualGuard.v"))
    flags = compiler.lowering.flags()
    frontier, seen, level = MODULES, set(), 0
    while frontier:
        current = sorted(set(frontier)-seen)
        if not current:
            break
        seen.update(current)
        for source in current:
            source, obj = permitted(source), permitted(source.with_suffix(".vo"))
            if not obj.exists() or obj.stat().st_mtime < source.stat().st_mtime:
                raise ValueError("Uncompiled source: "+str(source))
            for path in [source,obj]:
                bindings[str(path.relative_to(ROOT))] = sha(path)
        run = subprocess.run(["rocq","dep",*flags,*map(str,current)], cwd=ROOT,
                             capture_output=True,text=True,check=True)
        (WORK/f"dependencies-{level}.log").write_text(run.stdout+run.stderr)
        frontier = []
        for line in run.stdout.splitlines():
            if ": " not in line:
                continue
            for token in line.split(": ",1)[1].split():
                if token.endswith(".vo"):
                    obj = permitted(ROOT/token)
                    bindings[str(obj.relative_to(ROOT))] = sha(obj)
                    source = permitted(obj.with_suffix(".v"))
                    if source.exists() and source not in seen:
                        frontier.append(source)
        level += 1
    queried = endpoints()
    markers = [f"SOURCE_ENDPOINT_{i}" for i in range(len(queried)+1)]
    code = ["From GuardInterface Require Import "+" ".join(INTERFACES)+"."]
    for marker,endpoint in zip(markers,queried):
        code += [f'Goal True. idtac "{marker}". exact I. Qed.',f"Print Assumptions {endpoint}."]
    code += [f'Goal True. idtac "{markers[-1]}". exact I. Qed.']
    (WORK/"Audit.v").write_text("\n".join(code)+"\n")
    run = subprocess.run(["rocq","compile",*flags,str(WORK/"Audit.v")],cwd=ROOT,capture_output=True,text=True)
    (WORK/"assumptions.log").write_text(run.stdout+run.stderr)
    if run.returncode:
        raise ValueError(run.stderr)
    actual = {endpoint: sorted(names(run.stdout.split(markers[i]+"\n",1)[1].split(markers[i+1]+"\n",1)[0]))
              for i,endpoint in enumerate(queried)}
    added = sorted(set().union(*map(set,actual.values()))-allowed)
    if added:
        raise ValueError("New globals: "+str(added))
    attempts = []
    for source in MODULES:
        for metadata in sorted(compiler.WORK.glob(source.stem+"-v*.json")):
            item = json.loads(permitted(metadata).read_text())
            if sha(permitted(metadata.with_suffix(".v"))) != item["source_sha256"]:
                raise ValueError("Changed attempt: "+str(metadata))
            attempts.append({"module":source.stem,"compiled":item["returncode"]==0,
                             "metadata":str(metadata.relative_to(ROOT))})
            for path in [metadata,metadata.with_suffix(".v"),metadata.with_suffix(".log")]:
                bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    for path in [Path(__file__),ROOT/"toolchain.lock.json",*WORK.iterdir()]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status":"compiled","new_modules":[str(p.relative_to(ROOT)) for p in MODULES],
              "new_source_lines":sum(len(permitted(p).read_text().splitlines()) for p in MODULES),
              "endpoints":queried,"endpoint_assumptions":actual,"additional_global_axioms":added,
              "allowed_parent_globals":sorted(allowed),"closed_endpoints":sum(not x for x in actual.values()),
              "maximum_endpoint_globals":max(map(len,actual.values())),"reachable_source_count":len(seen),
              "attempts":attempts,"complete_compiler_endpoint":ENTRY,
              "complete_compiler_direction":"Csem-to-Asm-backward-simulation",
              "actual_source_loop_passed_to_untrusted_adapter":True,
              "common_original_schedule_coordinates_reused":True,
              "per_statement_constant_point_shifts_reused":True,
              "affine_reference_is_checked_before_proved_postpass":True,
              "actual_residual_loop_is_lowered_through_proved_machine_compiler":True,
              "loop_binder_branch_and_interval_facts_are_proved":True,
              "established_typed_double_pipeline_runs_on_actual_intermediate_program":True,
              "generic_formula_residualization_reused":True,
              "generic_library_successor_byte_identical":True,
              "adjacent_equal_guards_factored_under_immutable_model_environment":True,
              "OLO_compact_entry_condition_algorithm_complete":False,
              "actual_pruned_loop_revalidated_by_polyhedral_checker":False,
              "runtime_maximum_bound_selected_by_complementary_guards":True,
              "factory_and_current_program_host_consume_new_checker":True,
              "domain_partition_or_many_to_one_point_matching_added":False,
              "new_native_acceptance_established_by_proof_audit":False,
              "kernel_changed":False,"additional_host_laws":False,"full_goal_complete":False,"bindings":bindings}
    portable = {k:v for k,v in report.items() if k not in {"bindings","endpoint_assumptions","allowed_parent_globals"}}
    portable["report"] = str((WORK/"report.json").relative_to(ROOT))
    with PORTABLE.open("x") as out:
        out.write(json.dumps(portable,indent=2)+"\n")
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    validate()
    print(json.dumps({"status":"compiled","source_lines":report["new_source_lines"],"endpoints":len(queried),
                      "closed":report["closed_endpoints"],"maximum_globals":report["maximum_endpoint_globals"],
                      "bindings":len(bindings)}))


if __name__ == "__main__":
    main()
