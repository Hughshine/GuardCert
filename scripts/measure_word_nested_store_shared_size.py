"""Measure paired linked function sizes and source-loop copies; no timing claim."""
import argparse
import json
from pathlib import Path
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

BASE = ROOT / "build/multi-word-nested-native/native-v1"
SHARED = ROOT / "build/multi-word-nested-shared/native-v1"
WORK = ROOT / "build/multi-word-nested-shared/size-v1"
NAMES = ["loaded_pair", "loaded_unmarked", "loaded_twice", "loaded_context", "loaded_unsupported", "loaded_case", "main"]
SOURCE_LOOPS = r"for\s*\(\s*;\s*1\s*;\s*\$i\s*=\s*\$i\s*\+\s*1U?\s*\)\s*\{"


def inputs(directory):
    path = directory / "report.json"
    report = json.loads(path.read_text())
    assert report["status"] == "passed" and report["assembly_calls"] == report["independent_Clight_calls"] == 1000
    for file, digest in report["bindings"].items():
        assert sha(ROOT / file) == digest, file
    return path, report


def metrics(directory, name, log):
    output = subprocess.check_output(["nm", "-S", "--defined-only", str(directory / name / "program")], text=True)
    log.write_text(output)
    sizes = {match.group(2): int(match.group(1), 16) for match in re.finditer(
        r"^[0-9a-fA-F]+\s+([0-9a-fA-F]+)\s+[Tt]\s+(\w+)$", output, re.M)}
    assert set(NAMES) <= set(sizes), name
    dump = (directory / name / "regions.light.c").read_text()
    return {function: {"linked_function_bytes": sizes[function],
                       "Clight_root_source_loop_copies": len(re.findall(SOURCE_LOOPS, function_body(dump, function)))}
            for function in NAMES}


def validate():
    base_path, base = inputs(BASE)
    shared_path, shared = inputs(SHARED)
    report = json.loads((WORK / "report.json").read_text())
    assert report["status"] == "measured" and not report["runtime_or_profitability_claim"]
    assert set(report["configurations"]) == set(base["configurations"]) == set(shared["configurations"])
    assert report["native_report_sha256"] == {"base": sha(base_path), "shared": sha(shared_path)}
    for path, digest in report["bindings"].items():
        assert sha(ROOT / path) == digest, path
    return report


def main():
    global WORK
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, default=WORK)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    WORK = args.work.resolve()
    assert WORK.is_relative_to(ROOT / "build/multi-word-nested-shared")
    if args.validate or (WORK / "report.json").exists():
        report = validate()
        print(json.dumps({"status": "validated", "report_sha256": sha(WORK / "report.json")}))
        return
    assert not WORK.exists(), "Refusing to overwrite a size checkpoint"
    base_path, base = inputs(BASE)
    shared_path, shared = inputs(SHARED)
    assert set(base["configurations"]) == set(shared["configurations"])
    WORK.mkdir()
    pairs = {}
    for name in base["configurations"]:
        assert (BASE / name / "regions.c").read_bytes() == (SHARED / name / "regions.c").read_bytes()
        assert (BASE / name / "output.txt").read_bytes() == (SHARED / name / "output.txt").read_bytes()
        assert base["clight_paths"][name]["actual_paths"] == shared["clight_paths"][name]["actual_paths"]
        first = metrics(BASE, name, WORK / (name + "-base-nm.txt"))
        second = metrics(SHARED, name, WORK / (name + "-shared-nm.txt"))
        for function in ["loaded_unmarked", "loaded_unsupported", "loaded_case", "main"]:
            assert first[function] == second[function], (name, function, "outside-size-changed")
        if any(base["configurations"][name]["installed_sites"].values()):
            for function, copies in [("loaded_pair", 4), ("loaded_twice", 8), ("loaded_context", 4)]:
                assert second[function]["Clight_root_source_loop_copies"] == copies, (name, function)
                assert second[function]["linked_function_bytes"] < first[function]["linked_function_bytes"], (name, function)
        else:
            assert first == second, name
        pairs[name] = {function: {"base": first[function], "shared": second[function]} for function in NAMES}
    bindings = {base_path: sha(base_path), shared_path: sha(shared_path),
                Path(__file__): sha(Path(__file__)), ROOT / "scripts/audit_interface_clight.py": sha(ROOT / "scripts/audit_interface_clight.py"),
                ROOT / "scripts/native_zero_trip.py": sha(ROOT / "scripts/native_zero_trip.py")}
    bindings |= {path: sha(path) for path in WORK.rglob("*") if path.is_file()}
    report = {"status": "measured", "configurations": pairs,
              "native_report_sha256": {"base": sha(base_path), "shared": sha(shared_path)},
              "identical_sources_outputs_and_observed_paths": True,
              "metric": "nm -S linked CompCert function bytes; emitted Clight root-source loop copies",
              "runtime_or_profitability_claim": False, "guard_scan_asymptotics_changed": False,
              "full_goal_complete": False,
              "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()}}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "measured", "row_nonunit": pairs["row-nonunit"]["loaded_pair"],
                      "report_sha256": sha(WORK / "report.json")}, indent=2))


if __name__ == "__main__":
    main()
