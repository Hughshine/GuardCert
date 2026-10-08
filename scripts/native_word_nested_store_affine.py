"""Run real marked loaded-bound C, ranked Pluto/codegen, and independent path probes."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

import build_word_nested_store_native_compiler as builder
import build_pipeline_pluto as scheduler
import word_nested_store_affine_fixtures as fixtures
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/multi-word-nested-native/native-v1"
COMPILER = builder.WORK / "ccomp"
CONFIGURATIONS = {
    "row-nonunit": (False, True, False, "tile", "normal", [2, 3]),
    "row-partial-unit": (False, True, False, "tile", "normal", [1, 3]),
    "row-all-unit": (False, True, False, "tile", "normal", [1, 1]),
    "column-nonunit": (True, True, False, "tile", "normal", [2, 3]),
    "row-variable-stride": (False, True, True, "tile", "normal", [2, 3]),
    "column-variable-stride": (True, True, True, "tile", "normal", [2, 3]),
    "row-schedule": (False, True, False, "schedule", "normal", [2, 3]),
    "unannotated": (False, False, False, "tile", "normal", [2, 3]),
    "disabled": (False, True, False, "tile", "disabled", [2, 3]),
    "scheduler-failure": (False, True, False, "tile", "failure", [2, 3]),
}
HELPERS = ["scripts/native_word_nested_store_affine.py",
           "scripts/word_nested_store_affine_fixtures.py",
           "scripts/build_word_nested_store_native_compiler.py",
           "scripts/build_pipeline_pluto.py", "scripts/audit_interface_clight.py",
           "scripts/native_selected_regions.py", "scripts/native_zero_trip.py",
           "scripts/native_affine_nest_paths.py", "scripts/native_memory_layout_sequence_paths.py"]


def check_build():
    stamp_path = COMPILER.parent / ".guard-build.json"
    stamp = json.loads(stamp_path.read_text())
    assert stamp["proved_entrypoint"] == builder.ENTRY
    assert stamp["selected_only_discovery_and_installation"]
    assert stamp["external_scheduler_callback_connected"] and stamp["prepared_codegen_candidate_producer"]
    assert stamp["actual_source_rank"] == 2 and not stamp["synthetic_axis_added"]
    assert stamp["private_count"] == 100
    bindings = {COMPILER: stamp["compiler_sha256"], stamp_path: sha(stamp_path),
                builder.PROOF: stamp["proof_report_sha256"],
                COMPILER.parent / "driver/Driver.ml": stamp["driver_sha256"],
                COMPILER.parent / "cparser/Parse.ml": stamp["parser_sha256"],
                COMPILER.parent / "extract_tensor_regions.v": stamp["extraction_sha256"],
                ROOT / "scripts/build_word_nested_store_native_compiler.py": stamp["build_script_sha256"]}
    bindings |= {ROOT / path: digest for path, digest in
                 (stamp["proof_bindings"] | stamp["native_sources"] | stamp["build_helpers"]).items()}
    for path, digest in bindings.items():
        assert sha(path) == digest, path
    return bindings


def dispatch_sites(body):
    """Classify emitted decisions by their actual fallback and public restoration."""
    for match in re.finditer(r"if\s*\(\s*\$[0-9]+\s*\)\s*\{", body):
        yes = match.end() - 1
        finish = fixtures.closing_brace(body, yes)
        no = re.match(r"\s*else\s*\{", body[finish + 1:])
        if no is None:
            continue
        fallback = finish + 1 + no.end() - 1
        end = fixtures.closing_brace(body, fallback)
        alternative = body[fallback:end]
        if re.search(r"\$i\s*<\s*\*\s*\$h", alternative):
            yield "header", yes, fallback
        elif (re.search(r"\$i\s*<\s*\$[0-9]+", alternative)
              and re.search(r"\$i\s*=\s*\$[0-9]+\s*;", body[yes:finish])):
            yield "candidate", yes, fallback


def compile_run(name, configuration, pluto):
    column, marked, variable, mode, kind, sizes = configuration
    directory = WORK / name
    directory.mkdir()
    source = directory / "regions.c"
    source.write_text(fixtures.source_text(column, marked, variable))
    env = {key: value for key, value in os.environ.items() if not key.startswith("GUARDCERT_")}
    env.update(GUARDCERT_TENSOR_MODE="disabled" if kind == "disabled" else "pipeline",
               GUARDCERT_POLYHEDRAL_MODE=mode,
               GUARDCERT_PLUTO="/usr/bin/false" if kind == "failure" else str(pluto),
               GUARDCERT_TILE_SIZES=",".join(map(str, sizes)),
               GUARDCERT_PIPELINE_DUMP=str(directory / "phases"),
               GUARDCERT_SCOP_DIAGNOSTICS="1", GUARDCERT_TENSOR_DIAGNOSTICS="1")
    command = [str(COMPILER), "-fall", "-stdlib", str(COMPILER.parent / "runtime"),
               "-dclight", "-S", "-o", str(directory / "program.s"), str(source)]
    (directory / "compile-command.json").write_text(json.dumps({"argv": command,
        "environment": {key: value for key, value in env.items() if key.startswith("GUARDCERT_")}}, indent=2) + "\n")
    with (directory / "compile.log").open("x") as log:
        subprocess.run(command, cwd=directory, env=env, stdout=log, stderr=subprocess.STDOUT,
                       check=True, timeout=600)
    subprocess.run(["gcc", "-no-pie", str(directory / "program.s"), "-o", str(directory / "program")],
                   check=True, capture_output=True)
    output = subprocess.check_output([str(directory / "program")], text=True, timeout=90)
    (directory / "output.txt").write_text(output)
    expected_output = fixtures.expected_output(column, variable)
    assert output == expected_output, (name, "assembly-output")
    subprocess.run(["gcc", "-O0", "-fwrapv", str(source), "-o", str(directory / "reference")],
                   check=True, capture_output=True)
    reference = subprocess.check_output([str(directory / "reference")], text=True, timeout=90)
    (directory / "reference-output.txt").write_text(reference)
    assert reference == expected_output, (name, "reference-output")
    installed = marked and kind == "normal"
    dump = (directory / "regions.light.c").read_text()
    sites = {function: sum(site[0] == "header" for site in dispatch_sites(fixtures.function_body(dump, function)))
             for function in fixtures.NAMES}
    candidates = {function: sum(site[0] == "candidate" for site in dispatch_sites(fixtures.function_body(dump, function)))
                  for function in fixtures.NAMES}
    expected = dict(zip(fixtures.NAMES, fixtures.INSTALLED if installed else [0] * len(fixtures.NAMES)))
    assert sites == candidates == expected, (name, "installed-sites", sites, candidates, expected)
    phases = sorted((directory / "phases").glob("guardcert-phase-*"))
    assert len(phases) == (4 if marked and kind != "disabled" else 0), (name, "phase-count", len(phases))
    for phase in phases:
        assert (phase / "source.loop").exists() and (phase / "before.scop").exists()
        assert (phase / "source-rank.txt").read_text() == "2\n"
        if installed:
            assert (phase / "receipt.txt").exists()
            assert (phase / "affine-result.txt").read_text() == "accepted\n"
            assert (phase / "tiling-result.txt").read_text() == "accepted\n"
            assert all((phase / filename).exists() for filename in
                       ["generated.loop", "raw-statement-0.loop", "raw-statement-1.loop"])
            if mode == "schedule":
                assert "--identity" not in (phase / "command.txt").read_text()
            else:
                assert "point-dim=2" in (phase / "witness.txt").read_text()
        else:
            assert (phase / "scheduler-refusal.txt").exists() and not (phase / "receipt.txt").exists()
    return {"calls": len(fixtures.CASES), "installed_sites": sites, "phase_calls": len(phases),
            "automatic_loaded_source_and_cached_model_description": True,
            "handwritten_metadata_or_semantic_callback": False, "actual_source_rank": 2,
            "complete_memory_and_public_outputs_checked": True, "assembly_path_claim": False}


def branch_probe(name, configuration):
    column, marked, variable, _mode, kind, _sizes = configuration
    directory = WORK / name
    source = fixtures.printer_for_gcc((directory / "regions.light.c").read_text())
    root_loop = r"for\s*\(\s*;\s*1\s*;\s*\$i\s*=\s*\$i\s*\+\s*1U?\s*\)\s*\{"
    root_test = r"\s*if\s*\(\s*!\s*\(\s*\$i\s*<\s*(\*\s*\$h|\$[0-9]+)"
    for function in fixtures.NAMES:
        body = fixtures.function_body(source, function)
        additions = [(yes + 1, "probe_header++;" if layer == "header" else "probe_fast++;")
                     for layer, yes, _no in dispatch_sites(body)]
        for loop in re.finditer(root_loop, body):
            test = re.match(root_test, body[loop.end():])
            assert test is not None, (name, function, "root-loop-test")
            bound = test.group(1)
            counter = ("probe_loaded++;" if "*" in bound else
                       f"if({bound}==0)probe_empty++;else probe_cached++;")
            additions.append((loop.start(), counter))
        changed = body
        for position, text in sorted(additions, reverse=True):
            changed = changed[:position] + text + changed[position:]
        source = source.replace(body, changed, 1)
    counters = "probe_header,probe_fast,probe_cached,probe_loaded,probe_empty"
    source = "int " + counters + ";\n" + source
    source += "int main(void){" + "".join(
        "probe_header=probe_fast=probe_cached=probe_loaded=probe_empty=0;loaded_case(" +
        ",".join(map(str, case)) + ');printf("PATH %d %d %d %d %d\\n",' + counters + ");"
        for case in fixtures.CASES) + "return 0;}\n"
    (directory / "branches.c").write_text(source)
    command = ["gcc", "-O0", "-fwrapv", "-Wno-builtin-declaration-mismatch", "-Wno-discarded-qualifiers",
               str(directory / "branches.c"), "-o", str(directory / "branches")]
    diagnostic = subprocess.run(command, capture_output=True, text=True)
    (directory / "branches-compile.log").write_text(diagnostic.stdout + diagnostic.stderr)
    assert diagnostic.returncode == 0, (name, "branch-probe-compile")
    output = subprocess.check_output([str(directory / "branches")], text=True, timeout=90)
    (directory / "branch-output.txt").write_text(output)
    actual = [list(map(int, line.split()[1:])) for line in output.splitlines() if line.startswith("PATH ")]
    expected = [fixtures.model(case, column, variable, marked and kind == "normal")[1]
                for case in fixtures.CASES]
    assert actual == expected, (name, "paths", [(case, a, b) for case, a, b in
                                               zip(fixtures.CASES, actual, expected) if a != b])
    assert "\n".join(line for line in output.splitlines() if not line.startswith("PATH ")) + "\n" == fixtures.expected_output(column, variable)
    return {"calls": len(fixtures.CASES), "actual_paths": actual, "assembly_path_claim": False,
            "path_columns": counters.split(","), "totals": [sum(row[i] for row in actual) for i in range(5)]}


def validate():
    check_build()
    report = json.loads((WORK / "report.json").read_text())
    assert report["status"] == "passed" and report["proved_entrypoint"] == builder.ENTRY
    assert set(report["configurations"]) == set(CONFIGURATIONS)
    for path, digest in report["bindings"].items():
        assert sha(ROOT / path) == digest, path
    for name, (column, marked, variable, _mode, kind, _sizes) in CONFIGURATIONS.items():
        assert (WORK / name / "regions.c").read_text() == fixtures.source_text(column, marked, variable)
        assert (WORK / name / "output.txt").read_text() == fixtures.expected_output(column, variable)
        assert (WORK / name / "reference-output.txt").read_text() == fixtures.expected_output(column, variable)
        assert report["clight_paths"][name]["actual_paths"] == [
            fixtures.model(case, column, variable, marked and kind == "normal")[1] for case in fixtures.CASES]
    return report


def main():
    global WORK
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, default=WORK)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    WORK = args.work.resolve()
    assert WORK.is_relative_to(ROOT / "build/multi-word-nested-native")
    if args.validate or (WORK / "report.json").exists():
        report = validate()
        print(json.dumps({"status": "validated", "assembly_calls": report["assembly_calls"],
                          "report_sha256": sha(WORK / "report.json")}))
        return
    assert not WORK.exists(), "Refusing to overwrite a native checkpoint"
    bindings = check_build()
    pluto = scheduler.validate()
    WORK.mkdir()
    configurations, paths = {}, {}
    try:
        for name, configuration in CONFIGURATIONS.items():
            configurations[name] = compile_run(name, configuration, (ROOT / pluto["binary"]).resolve())
            paths[name] = branch_probe(name, configuration)
            print(json.dumps({"configuration": name, "status": "passed", "calls": len(fixtures.CASES),
                              "paths": paths[name]["totals"]}), flush=True)
    except Exception as error:
        (WORK / "failure.json").write_text(json.dumps({"status": "failed", "error": repr(error),
            "completed": list(configurations), "completed_paths": list(paths)}, indent=2) + "\n")
        raise
    bindings |= {ROOT / path: sha(ROOT / path) for path in HELPERS}
    bindings |= {scheduler.REPORT: sha(scheduler.REPORT)}
    bindings |= {path: sha(path) for path in WORK.rglob("*") if path.is_file()}
    report = {"status": "passed", "proved_entrypoint": builder.ENTRY, "compiler_sha256": sha(COMPILER),
              "configurations": configurations, "clight_paths": paths,
              "assembly_calls": sum(case["calls"] for case in configurations.values()),
              "independent_Clight_calls": sum(case["calls"] for case in paths.values()),
              "full_memory_and_public_exits_checked": True, "real_scheduler_and_prepared_codegen": True,
              "loaded_source_header_supported": True, "general_affine_domains_supported": False,
              "measured_cost_added": False, "full_goal_complete": False,
              "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()}}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "passed", "assembly_calls": report["assembly_calls"],
                      "Clight_calls": report["independent_Clight_calls"],
                      "report_sha256": sha(WORK / "report.json")}), flush=True)


if __name__ == "__main__":
    main()
