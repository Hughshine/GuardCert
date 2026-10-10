"""Replay exact tiled inputs from the completed combined-compiler corpus.

This is a compiler diagnostic comparison, not a guard or target timing study.
"""
import argparse
import json
import os
from pathlib import Path
import re

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_combined_residual_traced_corpus import checked, run, PLUTO

ENTRY = "CombinedDoubleTreeResidualCompiler.compile_selected_combined_residual_double_program"
PARENT = ROOT / "build/benchmark-alignment/current-double-combined-residual-attempts/corpus-v1/report.json"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler-report", type=Path, required=True)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not re.fullmatch("[a-z0-9-]+", args.attempt):
        raise ValueError("Use a new simple attempt")
    bindings = {}
    build = checked(ROOT / args.compiler_report, bindings)
    parent = checked(PARENT, bindings)
    if build["whole_program_entrypoint"] != ENTRY or not build["VPL_identity_trace_inlined_by_standard_extraction"]:
        raise ValueError("Expected the unchanged compiler with the identity trace erased")
    compiler = ROOT / build["compiler"]
    work = ROOT / "build/double-tree-combined-residual/quiet-timeout-attempts" / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work / "script.py").write_bytes(Path(__file__).read_bytes())
    rows = []
    for case in ["jacobi-1d-imper", "tce"]:
        original = next(row for row in parent["results"] if row["case"] == case and row["variant"] == "original")
        old = original["configurations"]["tiled"]
        if not old["compiler"]["timeout"]:
            raise ValueError("Keep both original timed-out compiler attempts")
        directory = work / case
        directory.mkdir()
        source = directory / "program.c"
        source.write_bytes(permitted(ROOT / original["input"]).read_bytes())
        if sha(source) != old["source_sha256"]:
            raise ValueError("Use the exact previously timed-out annotated source")
        env = {key: value for key, value in os.environ.items() if not key.startswith("GUARDCERT_")}
        env.update(GUARDCERT_ORIGINAL_MODE="tile", GUARDCERT_DOUBLE_TILING_MODE="tile",
                   GUARDCERT_PHASE_KIND="tiled", GUARDCERT_TREE_LOWER="0", GUARDCERT_TREE_UPPER="4096",
                   GUARDCERT_PLUTO=str(PLUTO), GUARDCERT_ORIGINAL_OUTPUT=str(directory),
                   GUARDCERT_SCOP_DIAGNOSTICS="1")
        result, out, err = run([str(compiler), "-fall", "-stdlib", str(compiler.parent / "runtime"),
             "-dclight", "-S", "-o", str(directory / "program.s"), str(source)], directory, "compiler", env)
        row = {"case": case, "variant": "original", "mode": "requested-tiled",
               "source_sha256": sha(source), "prior_compiler": old["compiler"], "compiler": result,
               "status": "compiler_timeout" if result["timeout"] else "compiler_refusal"}
        trace = (out + err).decode(errors="replace")
        for key, pattern in [
            ("tree_installed", r"GUARDCERT_TREE_INSTALLED regions=(\d+) phase_calls=(\d+) adaptations=(\d+)"),
            ("typed_installed", r"GUARDCERT_DOUBLE_INSTALLED original=(\d+) initialized=(\d+) regions=(\d+) pipeline_calls=(\d+) reduction=(\d+)")]:
            values = re.findall(pattern, trace)
            row[key] = list(map(int, values[-1])) if values else None
        if result["returncode"] == 0:
            link, _, _ = run(["gcc", "-no-pie", str(directory / "program.s"), "-lm", "-o", str(directory / "program")], directory, "link")
            row["link"] = link
            row["status"] = "link_failure"
            if link["returncode"] == 0:
                native, actual, _ = run([str(directory / "program")], directory, "native")
                expected = permitted(ROOT / original["original_GCC_reference"]).read_bytes()
                row["native"] = native
                row["status"] = "native_match" if native["returncode"] == 0 and actual == expected else "native_mismatch_or_timeout"
        row["requested_tiling_requires_actual_candidate_analysis"] = True
        rows.append(row)
        (directory / "row.json").write_text(json.dumps(row, indent=2) + "\n")
        print(json.dumps({"case": case, "status": row["status"], "compiler_seconds": result["elapsed_seconds"],
                          "tree_installed": row["tree_installed"], "typed_installed": row["typed_installed"]}), flush=True)
    for path in [Path(__file__), PLUTO, *[p for p in work.rglob("*") if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "diagnostic_complete", "compiler_entrypoint": ENTRY,
              "whole_program_theorem": build["actual_source_Csem_to_Asm_theorem"],
              "results": rows, "native_matches": sum(row["status"] == "native_match" for row in rows),
              "same_Rocq_compiler_and_checker_definitions": True,
              "identity_trace_erased_by_standard_extraction": True,
              "prior_timeouts_retained": True, "controlled_compile_cost_comparison": False,
              "guard_runtime_cost_measured": False, "full_corpus_replayed": False,
              "full_goal_complete": False, "bindings": bindings}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    if any(row["status"] != "native_match" for row in rows):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
