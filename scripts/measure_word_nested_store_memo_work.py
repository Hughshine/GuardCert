"""Pair actual readonly setup test counts and linked sizes; no timing claim.

The diagnostic counts every if-expression inside the emitted setup decision
tree. It retains complete region execution and the existing path counters. A
GCC build of printed Clight is diagnostic evidence, separate from unmodified
CompCert assembly. Historical native checkpoints are read and hash-checked.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess

from audit_interface_clight import ROOT, sha
import measure_word_nested_store_shared_size as size
import native_word_nested_store_shared as shared
import word_nested_store_affine_fixtures as fixtures

BASE = ROOT / "build/multi-word-nested-shared/native-v1"
MEMO = ROOT / "build/multi-word-nested-memo/native-v1"
WORK = ROOT / "build/multi-word-nested-memo/work-v1"
HELPERS = ["scripts/measure_word_nested_store_memo_work.py",
           "scripts/measure_word_nested_store_shared_size.py",
           "scripts/native_word_nested_store_shared.py", "scripts/native_word_nested_store_affine.py",
           "scripts/word_nested_store_affine_fixtures.py", "scripts/audit_interface_clight.py",
           "scripts/native_zero_trip.py", "scripts/native_selected_regions.py"]


def parenthesis_end(text, opening):
    assert text[opening] == "("
    depth, end = 1, opening + 1
    while depth:
        depth += (text[end] == "(") - (text[end] == ")")
        end += 1
    return end


def setup_spans(body):
    for layer, yes, _no in shared.dispatch_sites(body):
        if layer != "header":
            continue
        finish = fixtures.closing_brace(body, yes)
        roots = list(re.finditer(r"\bif\s*\(\s*\$i\s*==\s*0U?\s*\)\s*\{", body[yes:finish]))
        assert len(roots) == 1, ("setup-root-count", len(roots))
        root = roots[0]
        start, opening = yes + root.start(), yes + root.end() - 1
        end = fixtures.closing_brace(body, opening)
        alternative = re.match(r"\s*else\s*\{", body[end + 1:])
        assert alternative is not None, "Setup refusal must remain a decision leaf"
        end = fixtures.closing_brace(body, end + 1 + alternative.end() - 1)
        assert not re.search(r"\b(for|while)\s*\(", body[start:end]), "Setup contains a scan"
        yield start, end + 1


def counted_setup(body):
    additions, trees, nodes = [], 0, 0
    for start, end in setup_spans(body):
        trees += 1
        for test in re.finditer(r"\bif\s*\(", body[start:end]):
            opening = start + test.end() - 1
            closing = parenthesis_end(body, opening)
            assert closing <= end
            additions += [(opening + 1, "++setup_tests, ("), (closing - 1, ")")]
            nodes += 1
    for position, text in sorted(additions, reverse=True):
        body = body[:position] + text + body[position:]
    return body, trees, nodes


def diagnostic(directory, name, configuration, stage):
    column, marked, variable, _mode, kind, _sizes = configuration
    destination = WORK / name / stage
    destination.mkdir(parents=True)
    branch = (directory / name / "branches.c").read_text()
    main = branch.rfind("int main(void){")
    assert main >= 0
    source = branch[:main]
    tree_count, nodes = 0, {}
    for function in fixtures.NAMES:
        body = fixtures.function_body(source, function)
        changed, trees, count = counted_setup(body)
        source = source.replace(body, changed, 1)
        tree_count += trees
        nodes[function] = count
    assert tree_count == (sum(fixtures.INSTALLED) if marked and kind == "normal" else 0)
    counters = "probe_header,probe_fast,probe_cached,probe_loaded,probe_empty"
    source = "unsigned int setup_tests;\n" + source
    source += "int main(void){" + "".join(
        "setup_tests=probe_header=probe_fast=probe_cached=probe_loaded=probe_empty=0;loaded_case(" +
        ",".join(map(str, case)) + ');printf("WORK %u %d %d %d %d %d\\n",setup_tests,' + counters + ");"
        for case in fixtures.CASES) + "return 0;}\n"
    path = destination / "setup-work.c"
    path.write_text(source)
    command = ["gcc", "-O0", "-fwrapv", "-Wno-builtin-declaration-mismatch", "-Wno-discarded-qualifiers",
               str(path), "-o", str(destination / "setup-work")]
    run = subprocess.run(command, capture_output=True, text=True)
    (destination / "compile.log").write_text(run.stdout + run.stderr)
    assert run.returncode == 0, (name, stage, "work-probe-compile")
    output = subprocess.check_output([str(destination / "setup-work")], text=True, timeout=90)
    (destination / "output.txt").write_text(output)
    rows = [list(map(int, line.split()[1:])) for line in output.splitlines() if line.startswith("WORK ")]
    assert len(rows) == len(fixtures.CASES) and all(len(row) == 6 for row in rows)
    assert [row[1:] for row in rows] == [fixtures.model(case, column, variable,
            marked and kind == "normal")[1] for case in fixtures.CASES], (name, stage, "observed-paths")
    assert "\n".join(line for line in output.splitlines() if not line.startswith("WORK ")) + "\n" == \
        fixtures.expected_output(column, variable), (name, stage, "full-memory-public-outputs")
    return {"calls": len(rows), "setup_trees": tree_count, "static_test_nodes": nodes,
            "tests_per_call": [row[0] for row in rows], "total_tests": sum(row[0] for row in rows),
            "full_memory_public_and_paths_preserved": True, "assembly_work_claim": False}


def validate():
    base_path, base = size.inputs(BASE)
    memo_path, memo = size.inputs(MEMO)
    report = json.loads((WORK / "report.json").read_text())
    assert report["status"] == "measured" and not report["runtime_or_profitability_claim"]
    assert report["native_report_sha256"] == {"base": sha(base_path), "memo": sha(memo_path)}
    assert set(report["configurations"]) == set(base["configurations"]) == set(memo["configurations"])
    for path, digest in report["bindings"].items():
        assert sha(ROOT / path) == digest, path
    for pair in report["configurations"].values():
        assert all(new <= old for old, new in zip(pair["base"]["tests_per_call"], pair["memo"]["tests_per_call"]))
    return report


def main():
    global WORK
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, default=WORK)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    WORK = args.work.resolve()
    assert WORK.is_relative_to(ROOT / "build/multi-word-nested-memo")
    if args.validate or (WORK / "report.json").exists():
        report = validate()
        print(json.dumps({"status": "validated", "report_sha256": sha(WORK / "report.json")}))
        return
    assert not WORK.exists(), "Refusing to overwrite a work checkpoint"
    base_path, base = size.inputs(BASE)
    memo_path, memo = size.inputs(MEMO)
    assert set(base["configurations"]) == set(memo["configurations"])
    WORK.mkdir()
    pairs = {}
    try:
        for name, configuration in shared.CONFIGURATIONS.items():
            assert (BASE / name / "regions.c").read_bytes() == (MEMO / name / "regions.c").read_bytes()
            assert (BASE / name / "output.txt").read_bytes() == (MEMO / name / "output.txt").read_bytes()
            assert base["clight_paths"][name]["actual_paths"] == memo["clight_paths"][name]["actual_paths"]
            old = diagnostic(BASE, name, configuration, "base")
            new = diagnostic(MEMO, name, configuration, "memo")
            assert all(n <= o for o, n in zip(old["tests_per_call"], new["tests_per_call"])), name
            first = size.metrics(BASE, name, WORK / (name + "-base-nm.txt"))
            second = size.metrics(MEMO, name, WORK / (name + "-memo-nm.txt"))
            for function in size.NAMES:
                assert first[function]["Clight_root_source_loop_copies"] == second[function]["Clight_root_source_loop_copies"]
            for function in ["loaded_unmarked", "loaded_unsupported", "loaded_case", "main"]:
                assert first[function] == second[function], (name, function, "outside-size-changed")
            pairs[name] = {"base": old, "memo": new,
                           "sizes": {function: {"base": first[function], "memo": second[function]} for function in size.NAMES}}
            print(json.dumps({"configuration": name, "setup_tests": [old["total_tests"], new["total_tests"]]}), flush=True)
    except Exception as error:
        (WORK / "failure.json").write_text(json.dumps({"status": "failed", "error": repr(error),
                    "completed": list(pairs)}, indent=2) + "\n")
        raise
    bindings = {base_path: sha(base_path), memo_path: sha(memo_path)}
    bindings |= {ROOT / path: sha(ROOT / path) for path in HELPERS}
    bindings |= {path: sha(path) for path in WORK.rglob("*") if path.is_file()}
    report = {"status": "measured", "configurations": pairs,
              "native_report_sha256": {"base": sha(base_path), "memo": sha(memo_path)},
              "diagnostic_calls": 2 * sum(pair["memo"]["calls"] for pair in pairs.values()),
              "metric": "GCC diagnostic of every if-expression in the actual Clight readonly setup tree; nm -S linked CompCert function bytes",
              "no_runtime_cache_or_hoisted_reads": True, "identical_sources_outputs_and_observed_paths": True,
              "runtime_or_profitability_claim": False, "header_and_alias_scan_asymptotics_changed": False,
              "full_goal_complete": False,
              "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()}}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "measured", "row_nonunit": pairs["row-nonunit"]["sizes"]["loaded_pair"],
                      "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
