"""Validate selected actual affine requests through Pluto, codegen and C-to-Asm."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

import audit_selected_affine_pipeline as audit
import build_profiled_affine_compiler as builder
import build_pipeline_pluto as scheduler
import selected_affine_2d_fixtures as fixtures
from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body
from native_affine_nest_paths import closing_brace
from native_memory_layout_sequence_paths import printer_for_gcc

WORK = ROOT / "build/selected-affine-pipeline/affine-2d-native-v1"
COMPILER = builder.WORK / "ccomp"
CONFIGURATIONS = {
    "tile": (True, "tile", "pipeline", {}),
    "schedule": (True, "schedule", "pipeline", {}),
    "unannotated": (False, "tile", "pipeline", {}),
    "disabled": (True, "tile", "disabled", {}),
    "scheduler-failure": (True, "tile", "pipeline", {"GUARDCERT_PLUTO": "/usr/bin/false"}),
    "resource-refusal": (True, "tile", "pipeline", {"GUARDCERT_FM_ROWS": "0"}),
}


def check_build():
    stamp_path = COMPILER.parent / ".guard-build.json"
    stamp = json.loads(stamp_path.read_text())
    assert stamp["proved_entrypoint"] == builder.ENTRY
    assert stamp["selected_only_discovery_and_installation"]
    assert not stamp["stable_affine_source_rectangular_surrogate"]
    assert stamp["certified_builders_share_selected_installation_and_backend"]
    audit.validate()
    bindings = {COMPILER: stamp["compiler_sha256"], stamp_path: sha(stamp_path),
                builder.PROOF: stamp["proof_report_sha256"],
                ROOT / "scripts/build_profiled_affine_compiler.py": stamp["build_script_sha256"],
                COMPILER.parent / "driver/Driver.ml": stamp["driver_sha256"],
                COMPILER.parent / "cparser/Parse.ml": stamp["parser_sha256"],
                COMPILER.parent / "extract_tensor_regions.v": stamp["extraction_sha256"]}
    bindings |= {ROOT / name: digest for name, digest in
                 (stamp["proof_bindings"] | stamp["native_sources"] | stamp["build_helpers"]).items()}
    for path, digest in bindings.items():
        assert sha(path) == digest, path
    return bindings


def selections(body):
    for match in re.finditer(r"if\s*\(\s*\$[0-9]+\s*\)\s*\{", body):
        opening = match.end()-1
        end = closing_brace(body, opening)
        alternate = re.match(r"\s*else\s*\{", body[end+1:])
        if not alternate:
            continue
        fallback = end+1+alternate.end()-1
        finish = closing_brace(body, fallback)
        if re.search(r"\$i\s*<\s*\$n", body[fallback:finish]) and "for (" in body[opening:end]:
            yield opening, fallback


def compile_run(name, configuration, pluto, work):
    marked, mode, kind, extra = configuration
    directory = work / name
    directory.mkdir()
    source = directory / "regions.c"
    source.write_text(fixtures.source_text(marked))
    env = {key: value for key, value in os.environ.items() if not key.startswith("GUARDCERT_")}
    env.update(GUARDCERT_TENSOR_MODE=kind, GUARDCERT_POLYHEDRAL_MODE=mode,
               GUARDCERT_PLUTO=str(pluto), GUARDCERT_PIPELINE_DUMP=str(directory / "phases"),
               GUARDCERT_SCOP_DIAGNOSTICS="1", GUARDCERT_PIPELINE_CHECK_DIAGNOSTICS="1",
               GUARDCERT_AFFINE_FLOOR="0", GUARDCERT_AFFINE_CAP="4",
               GUARDCERT_AFFINE_BOUND_LOW="-2", GUARDCERT_AFFINE_BOUND_HIGH="4")
    env.update(extra)
    command = [str(COMPILER), "-fall", "-stdlib", str(COMPILER.parent / "runtime"),
               "-dclight", "-S", "-o", str(directory / "program.s"), str(source)]
    (directory / "compile-command.json").write_text(json.dumps({"argv": command,
        "environment": {key: value for key, value in env.items() if key.startswith("GUARDCERT_")}}, indent=2)+"\n")
    with (directory / "compile.log").open("x") as log:
        subprocess.run(command, cwd=directory, env=env, stdout=log, stderr=subprocess.STDOUT,
                       check=True, timeout=600)
    expected = fixtures.expected_output()
    subprocess.run(["gcc", "-no-pie", str(directory / "program.s"), "-o", str(directory / "program")],
                   check=True, capture_output=True)
    output = subprocess.check_output([str(directory / "program")], text=True, timeout=120)
    (directory / "output.txt").write_text(output)
    assert output == expected, (name, "assembly full outputs")
    subprocess.run(["gcc", "-O0", "-fwrapv", str(source), "-o", str(directory / "reference")],
                   check=True, capture_output=True)
    reference = subprocess.check_output([str(directory / "reference")], text=True, timeout=120)
    (directory / "reference-output.txt").write_text(reference)
    assert reference == expected, (name, "independent model/reference")
    dump = (directory / "regions.light.c").read_text()
    sites = {fn: list(selections(function_body(dump, fn))) for fn in fixtures.NAMES}
    counts = {fn: len(values) for fn, values in sites.items()}
    installed = name in ("tile", "schedule")
    if installed:
        assert counts == dict(zip(fixtures.NAMES, [1, 0, 0, 0, 0, 2])), (name, counts)
    else:
        assert not any(counts.values()), (name, counts)
    phases = sorted((directory / "phases").glob("guardcert-profiled-affine-phase-*"))
    if installed:
        assert len(phases) == 4
        assert set((phase / "source-rank.txt").read_text().strip() for phase in phases) == {"2"}
        for phase in phases:
            if (phase / "refusal.txt").exists():
                assert not (phase / "receipt.txt").exists()
                continue
            assert "rectangular-surrogate=false" in (phase / "source-origin.txt").read_text()
            assert (phase / "affine-result.txt").read_text() == "accepted\n"
            assert (phase / "tiling-result.txt").read_text() == "accepted\n"
            assert all((phase / file).exists() for file in ["before.scop", "receipt.txt", "generated.loop", "raw-generated.loop"])
            assert (phase / "whole-candidate-check-diagnostic.txt").read_text() == "valid=true\nalarm-free=true\n"
            if mode == "schedule":
                assert "--identity" not in (phase / "command.txt").read_text()
    if name in ("disabled", "unannotated"):
        assert not phases
    # Independently execute the emitted Clight, observing concrete selections.
    instrumented = printer_for_gcc(dump)
    instrumented = instrumented[:instrumented.index("\nint guard_original_main(void)")]
    for slot, fn in enumerate(fixtures.NAMES):
        body = function_body(instrumented, fn)
        edits = [(yes+1, f"guard_fast[{slot}]++;") for yes, _ in selections(body)]
        edits += [(no+1, f"guard_refused[{slot}]++;") for _, no in selections(body)]
        changed = body
        for position, code in sorted(edits, reverse=True):
            changed = changed[:position]+code+changed[position:]
        assert instrumented.count(body) == 1
        instrumented = instrumented.replace(body, changed, 1)
    calls = []
    for case in fixtures.CASES:
        slot = case[0]
        calls.append(f"guard_fast[{slot}]=0;guard_refused[{slot}]=0;run_case("+
                     ",".join(map(fixtures.literal, case))+f');printf("paths %d %d\\n",guard_fast[{slot}],guard_refused[{slot}]);')
    diagnostic = directory / "branch-diagnostic.c"
    diagnostic.write_text("int guard_fast[6],guard_refused[6];\n"+instrumented+
                          "\nint main(void){\n"+"\n".join(calls)+"\nreturn 0;}\n")
    with (directory / "branch-gcc.log").open("x") as log:
        subprocess.run(["gcc", "-O0", "-fwrapv", "-Wno-builtin-declaration-mismatch",
                        "-Wno-discarded-qualifiers", str(diagnostic), "-o", str(directory / "branch-diagnostic")],
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    observed = subprocess.check_output([str(directory / "branch-diagnostic")], text=True, timeout=120)
    (directory / "branch-output.txt").write_text(observed)
    lines = observed.splitlines()
    assert len(lines) == 2*len(fixtures.CASES)
    assert "\n".join(lines[::2])+"\n" == expected, (name, "Clight full outputs")
    paths = [tuple(map(int, line.split()[1:])) for line in lines[1::2]]
    assert all(fast+refused == counts[fixtures.NAMES[case[0]]] for case, (fast, refused) in zip(fixtures.CASES, paths))
    if installed:
        assert any(fast for fast, _ in paths) and any(refused for _, refused in paths)
        for case, (fast, refused) in zip(fixtures.CASES, paths):
            if case[1] == 1 and case[2:6] == (0, 3, 2, 2):
                assert fast == 0 and refused == counts[fixtures.NAMES[case[0]]], (name, "overlap refused", case)
    return {"assembly_calls": len(fixtures.CASES), "Clight_calls": len(fixtures.CASES),
            "installed_sites": counts, "actual_phase_count": len(phases),
            "actual_fast_selections": sum(fast for fast, _ in paths),
            "actual_refused_selections": sum(refused for _, refused in paths),
            "paths": [{"input": list(case), "fast": fast, "refused": refused}
                      for case, (fast, refused) in zip(fixtures.CASES, paths)]}


def validate(work):
    report = json.loads((work / "report.json").read_text())
    assert report["status"] == "passed" and report["proved_entrypoint"] == builder.ENTRY
    assert set(report["configurations"]) == set(CONFIGURATIONS)
    check_build()
    for path, digest in report["bindings"].items():
        assert sha(ROOT / path) == digest, path
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, default=WORK)
    parser.add_argument("--validate", action="store_true")
    parser.add_argument("--only", choices=list(CONFIGURATIONS))
    args = parser.parse_args()
    work = args.work.resolve()
    assert work.is_relative_to(ROOT / "build/selected-affine-pipeline")
    if args.validate or (work / "report.json").exists():
        report = validate(work)
        print(json.dumps({"status": "validated", "report_sha256": sha(work / "report.json")}))
        return
    bindings = check_build()
    pluto = scheduler.validate()
    work.mkdir(parents=True, exist_ok=False)
    results = {}
    for name, configuration in CONFIGURATIONS.items():
        if args.only and name != args.only:
            continue
        results[name] = compile_run(name, configuration, ROOT / pluto["binary"], work)
        print(json.dumps({"configuration": name, **{key: value for key, value in results[name].items() if key != "paths"}}), flush=True)
    if args.only:
        (work / "smoke.json").write_text(json.dumps(results, indent=2)+"\n")
        return
    helpers = [Path(__file__), ROOT / "scripts/selected_affine_2d_fixtures.py",
               ROOT / "scripts/native_zero_trip.py", ROOT / "scripts/native_affine_nest_paths.py",
               ROOT / "scripts/native_memory_layout_sequence_paths.py", ROOT / "scripts/build_pipeline_pluto.py"]
    bindings |= {path: sha(path) for path in helpers}
    bindings |= {scheduler.REPORT: sha(scheduler.REPORT), ROOT / pluto["binary"]: sha(ROOT / pluto["binary"])}
    bindings |= {path: sha(path) for path in work.rglob("*") if path.is_file()}
    report = {"status": "passed", "proved_entrypoint": builder.ENTRY,
              "configurations": results,
              "assembly_calls": sum(row["assembly_calls"] for row in results.values()),
              "Clight_calls": sum(row["Clight_calls"] for row in results.values()),
              "actual_checked_nonrectangular_source_passed_to_scheduler": True,
              "annotated_only_selected_installation": True,
              "two_regions_independently_checked_in_one_function": True,
              "all_array_cells_public_controls_and_continuation_checked": True,
              "loaded_word_and_general_affine_combined_semantic_domain": False,
              "source_grammar_extended": False, "new_installed_affine_rank": 2,
              "three_dimensional_profiled_codegen_not_completed_in_this_tier": True, "profitability_measured": False,
              "full_goal_complete": False,
              "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()}}
    (work / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    validate(work)
    print(json.dumps({"status": "passed", "assembly_calls": report["assembly_calls"],
                      "Clight_calls": report["Clight_calls"], "report_sha256": sha(work / "report.json")}))


if __name__ == "__main__":
    main()
