"""Run the actual tiled compiler on pinned original double/I64 harnesses."""

import argparse
import json
import os
from pathlib import Path
import re

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked, run, PLUTO, PARENT


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler-report", type=Path, required=True)
    parser.add_argument("--attempt", required=True)
    parser.add_argument("--cases", nargs="+", default=["mvt", "matmul-seq"])
    parser.add_argument("--modes", nargs="+", default=["tile", "unmarked", "refuse", "wrong-witness", "malformed"])
    parser.add_argument("--tile-sizes", default="32")
    parser.add_argument("--private-count", default="16")
    args = parser.parse_args()
    if not re.fullmatch("[a-z0-9-]+", args.attempt):
        raise ValueError("Use a new simple attempt name")
    bindings = {}
    build = checked(permitted(ROOT / args.compiler_report), bindings)
    if build["status"] != "built" or not build["double_tiling_entrypoint_audited"]:
        raise ValueError("Expected the actual audited double tiling compiler")
    compiler = permitted(ROOT / build["compiler"])
    parent = checked(PARENT, bindings)
    originals = {row["case"]: row for row in parent["results"]}
    work = ROOT / "build/double-tiling/original-attempts" / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work / "script.py").write_bytes(Path(__file__).read_bytes())
    rows = []
    for case in args.cases:
        source_path = permitted(PARENT.parent / case / "marked.c")
        expected_path = permitted(PARENT.parent / case / "reference-run.stdout")
        if originals[case]["reference_execution"]["returncode"] != 0:
            raise ValueError("Missing original GCC reference")
        text = source_path.read_text()
        expected = expected_path.read_bytes()
        for path in [source_path, expected_path]:
            bindings[str(path.relative_to(ROOT))] = sha(path)
        for mode in args.modes:
            directory = work / (case + "-" + mode)
            directory.mkdir()
            source = directory / "program.c"
            source.write_text(text.replace("#pragma scop\n", "").replace("#pragma endscop\n", "")
                              if mode == "unmarked" else text)
            env = {key: value for key, value in os.environ.items() if not key.startswith("GUARDCERT_")}
            env.update(GUARDCERT_ORIGINAL_MODE="tile", GUARDCERT_DOUBLE_TILING_MODE="tile" if mode == "unmarked" else mode,
                       GUARDCERT_TILE_SIZES=args.tile_sizes, GUARDCERT_DOUBLE_PRIVATE_COUNT=args.private_count,
                       GUARDCERT_PLUTO=str(PLUTO), GUARDCERT_ORIGINAL_OUTPUT=str(directory), GUARDCERT_SCOP_DIAGNOSTICS="1")
            result, out, err = run([str(compiler), "-fall", "-stdlib", str(compiler.parent / "runtime"), "-dclight", "-S",
                                    "-o", str(directory / "program.s"), str(source)], directory, "compiler", env)
            trace = (out + err).decode(errors="replace")
            found = re.findall(r"GUARDCERT_DOUBLE_TILING_INSTALLED reduction=(\d+) phase_calls=(\d+) adaptations=(\d+) enabled=(true|false)", trace)
            installed = [int(value) for value in found[-1][:3]] if found else None
            row = {"case": case, "mode": mode, "original_source": str(source_path.relative_to(ROOT)),
                   "original_source_sha256": sha(source_path), "compiler": result,
                   "installed_phase_calls_adaptations": installed,
                   "actual_phase_directories": [str(path.relative_to(ROOT)) for path in sorted(directory.glob("tiling-pipeline-*"))],
                   "raw_generated": [str(path.relative_to(ROOT)) for path in sorted(directory.glob("tiling-pipeline-*/raw-generated.loop"))],
                   "final_generated": [str(path.relative_to(ROOT)) for path in sorted(directory.glob("tiling-pipeline-*/generated.loop"))]}
            if result["returncode"] == 0:
                link, _, _ = run(["gcc", "-no-pie", str(directory / "program.s"), "-lm", "-o", str(directory / "program")], directory, "link")
                row["link"] = link
                if link["returncode"] == 0:
                    native, output, _ = run([str(directory / "program")], directory, "native")
                    row.update(native=native, digest_matches_original_GCC=native["returncode"] == 0 and output == expected)
            row["native_match"] = row.get("digest_matches_original_GCC", False)
            expected_sites = 2 if mode == "tile" and case in {"mvt", "matmul-seq"} else 0
            row["expected_sites"] = expected_sites
            row["installation_matches_expectation"] = installed is not None and installed[0] == expected_sites
            row["passed"] = row["native_match"] and row["installation_matches_expectation"]
            rows.append(row)
            (directory / "row.json").write_text(json.dumps(row, indent=2) + "\n")
            print(json.dumps({key: row[key] for key in ["case", "mode", "passed", "native_match", "installed_phase_calls_adaptations"]}), flush=True)
    for path in [Path(__file__), PLUTO, *[path for path in work.rglob("*") if path.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "passed" if all(row["passed"] for row in rows) else "rejected", "results": rows,
              "compiler_entrypoint": build["whole_program_entrypoint"],
              "whole_program_theorem": build["actual_source_Csem_to_Asm_theorem"],
              "source_numeric_types_and_computations_preserved": True,
              "original_GCC_reference_reused": True, "controlled_cost_comparison": False,
              "runtime_guard_branch_observation": False, "full_goal_complete": False, "bindings": bindings}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    if report["status"] != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
