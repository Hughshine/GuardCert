"""Check whole marked source trees on original exported Clight, without installing an optimizer."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess

import audit_signed_range_source as parent
import compile_matmul_installation as compiler
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

CASES = ["fusion1", "multi-stmt-stencil-seq", "tricky3"]
FRONT = ROOT / "build/original-matmul/frontend-v1"


def command(argv, cwd, log, env):
    with permitted(log).open("x") as out:
        result = subprocess.run(argv, cwd=cwd, env=env, stdout=out, stderr=subprocess.STDOUT)
    return {"command": list(map(str, argv)), "returncode": result.returncode,
            "log": str(log.relative_to(ROOT))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not re.fullmatch(r"[a-z0-9-]+", args.attempt):
        raise ValueError("Use a simple attempt name")
    baseline = parent.validate()
    source_report = json.loads(permitted(ROOT / "build/benchmark-alignment/probe-v1/report.json").read_text())
    frontend = json.loads(permitted(FRONT / "report.json").read_text())
    tool = permitted(FRONT / "tools/clightgen")
    if frontend["bindings"][str(tool.relative_to(ROOT))] != sha(tool):
        raise ValueError("Changed exported frontend")
    work = permitted(ROOT / "build/double-source-tree/source-attempts" / args.attempt)
    work.mkdir(parents=True, exist_ok=False)
    (work / "check-script.py").write_bytes(Path(__file__).read_bytes())
    env = {key: value for key, value in os.environ.items() if not key.startswith("GUARDCERT_")}
    bindings = {str(Path(__file__).relative_to(ROOT)): sha(Path(__file__)),
                str((work / "check-script.py").relative_to(ROOT)): sha(work / "check-script.py"),
                str(tool.relative_to(ROOT)): sha(tool),
                str((FRONT / "report.json").relative_to(ROOT)): sha(FRONT / "report.json"),
                str((parent.WORK / "report.json").relative_to(ROOT)): sha(parent.WORK / "report.json")}
    bindings.update({path: digest for path, digest in frontend["bindings"].items()
                     if "/runtime/" in path})
    for path, digest in bindings.items():
        if sha(permitted(ROOT / path)) != digest:
            raise ValueError("Changed frontend input: " + path)
    cases = []
    for name in CASES:
        case = work / name
        case.mkdir()
        source = permitted(ROOT / "build/benchmark-alignment/probe-v1" / name / "marked.c")
        if sha(source) != source_report["bindings"][str(source.relative_to(ROOT))]:
            raise ValueError("Changed original source: " + name)
        target = case / "marked.c"
        target.write_bytes(source.read_bytes())
        exported = case / "Exported.v"
        runs = [command([str(tool), "-fall", "-short-idents", "-dclight", "-stdlib", str(FRONT / "tools/runtime"),
                         "-o", str(exported), str(target)], case, case / "export.log", env)]
        if runs[-1]["returncode"]:
            cases.append({"case": name, "stage": "frontend-refused", "commands": runs})
            continue
        raw = permitted(exported).read_text()
        old = "From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs."
        new = ("From compcert.lib Require Import Coqlib Integers Floats.\n"
               "From compcert.common Require Import AST.\n"
               "From compcert.cfrontend Require Import Ctypes Cop Clight.\n"
               "From compcert.export Require Import Clightdefs.")
        if raw.count(old) != 1:
            raise ValueError("Unexpected frontend imports")
        adapted = case / "Original.v"
        adapted.write_text(raw.replace(old, new, 1))
        labels = re.findall(r"^Definition (___guardcert_scop_[0-9]+) : ident", raw, re.MULTILINE)
        if not labels:
            raise ValueError("No marked source region: " + name)
        flags = [*compiler.lowering.flags(), "-Q", str(case), "GuardTreeFixtures"]
        runs.append(command(["rocq", "compile", *flags, str(adapted)], ROOT, case / "original.log", env))
        if runs[-1]["returncode"]:
            cases.append({"case": name, "stage": "exported-ast-refused", "commands": runs})
            continue
        code = '''From Stdlib Require Import List Bool Arith ZArith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From GuardMemory Require Import GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeDecode.
From GuardTreeFixtures Require Import Original.
Import ListNotations.
Definition markers : list ident := MARKERS.
Fixpoint marked_regions source := match source with
| Slabel label body => if in_dec Pos.eq_dec label markers then [body] else marked_regions body
| Ssequence first second | Sloop first second | Sifthenelse _ first second => marked_regions first++marked_regions second
| _ => [] end.
Definition selected_regions := marked_regions (fn_body f_main).
Definition tree_summary source : list nat := match checked_double_source_tree prog source with
| None => [0]
| Some tree => [1;length (double_source_tree_instructions tree);length (double_source_tree_parameters tree);
               length (double_source_tree_writes tree);length (double_source_tree_headers tree)] end.
Goal True. idtac "SOURCE_TREE_STATS". exact I. Qed.
Eval vm_compute in map tree_summary selected_regions.
Theorem original_marked_region_count : length selected_regions=EXPECTED_COUNT%nat.
Proof. vm_compute; reflexivity. Qed.
Theorem original_whole_marked_trees_decode :
  forallb (fun source=>match checked_double_source_tree prog source with Some _=>true | None=>false end) selected_regions=true.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions original_marked_region_count.
Print Assumptions original_whole_marked_trees_decode.
'''.replace("MARKERS", "[" + ";".join(labels) + "]").replace("EXPECTED_COUNT", str(len(labels)))
        proof = case / "Probe.v"
        proof.write_text(code)
        runs.append(command(["rocq", "compile", *flags, str(proof)], ROOT, case / "probe.log", env))
        output = permitted(case / "probe.log").read_text()
        suffix = output.split("SOURCE_TREE_STATS\n", 1)[-1].split(": list", 1)[0]
        rows = re.findall(r"\[([0-9;\s]+)\]", suffix.replace("%nat", ""))
        stats = [[int(value.strip()) for value in row.split(";") if value.strip()] for row in rows]
        cases.append({"case": name, "stage": "checked-original-source-tree" if runs[-1]["returncode"] == 0 else "tree-proof-refused",
                      "marked_regions": len(labels), "summary_columns": ["accepted", "instructions", "shared_parameters", "temporary_writes", "headers"],
                      "source_tree_summaries": stats, "commands": runs,
                      "source_adaptations": "existing scop markers only; exported Rocq import namespaces adjusted",
                      "extra_source_normalization_applied": False})
        for path in [source, *case.iterdir()]:
            if path.is_file():
                bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    for directory, names in [("theories", ["ClightStructuredMemoryFrame"]),
                             ("adapters/compcert-memory", ["GuardMemoryDoubleRawEffects", "GuardMemoryDoubleSourceTreeData",
                               "GuardMemoryDoubleSourceTreeDecode", "GuardMemoryDoubleSourceTreeEffects", "GuardMemoryDoubleSourceTreeProgress"])]:
        for name in names:
            for suffix in [".v", ".vo"]:
                path = permitted(ROOT / directory / (name + suffix))
                bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "checked" if all(case["stage"] == "checked-original-source-tree" for case in cases) else "incomplete",
              "cases": cases, "source_numeric_types_and_computation_preserved": True,
              "complete_marked_regions_checked": True, "shared_parameter_registry_checked": True,
              "source_model_execution_correspondence_added_by_probe": False,
              "guard_candidate_factory_installed": False, "native_optimization_coverage_added": False,
              "full_goal_complete": False, "bindings": bindings,
              "parent_bound_inputs": len(baseline["bindings"])}
    (work / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"status": report["status"], "cases": [{key: case[key] for key in ["case", "stage", "source_tree_summaries"] if key in case}
                      for case in cases], "report": str((work / "report.json").relative_to(ROOT))}))
    if report["status"] != "checked":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
