"""Compare both frozen compilers on exactly the same actual RMW sources and inputs."""
import json
from pathlib import Path

import native_affine_observation as current
import native_zero_width_snapshot as before
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/affine-observation/comparison-v1"


def main():
    bindings = current.check_build() | before.check_build()
    after = current.validate(current.WORK)
    bindings[current.WORK / "report.json"] = sha(current.WORK / "report.json")
    if (WORK / "report.json").exists():
        report = json.loads((WORK / "report.json").read_text())
        assert report["status"] == "passed"
        for path, digest in report["bindings"].items():
            assert sha(ROOT / path) == digest, path
        print(json.dumps({"status": "validated", "report_sha256": sha(WORK / "report.json")}))
        return
    WORK.mkdir(parents=True, exist_ok=False)
    pluto = current.scheduler.validate()
    old_binary = before.COMPILER
    new_binary = current.COMPILER
    results, comparisons = {}, {}
    try:
        current.COMPILER = old_binary
        for name in ("tile", "schedule"):
            results[name] = current.compile_run(name, current.CONFIGURATIONS[name],
                ROOT / pluto["binary"], WORK, value_preserving=False)
            previous = {tuple(row["input"]): row for row in results[name]["paths"]}
            next_rows = {tuple(row["input"]): row for row in after["configurations"][name]["paths"]}
            assert set(previous) == set(next_rows)
            gains = [list(case) for case in previous
                     if previous[case]["fast"] == 0 and next_rows[case]["fast"] == 1]
            losses = [list(case) for case in previous
                      if previous[case]["fast"] == 1 and next_rows[case]["fast"] == 0]
            assert gains and not losses, (name, gains, losses)
            assert all(case[0] < 2 and case[1] in (2, 3) and case[5] == 0 for case in gains)
            comparisons[name] = {"same_inputs": len(previous),
                "before_fast": results[name]["actual_fast_selections"],
                "after_fast": after["configurations"][name]["actual_fast_selections"],
                "gains": gains, "losses": losses}
            print(json.dumps({"mode": name, **comparisons[name]}), flush=True)
    finally:
        current.COMPILER = new_binary
    helpers = [Path(__file__), ROOT / "scripts/native_affine_observation.py",
               ROOT / "scripts/affine_observation_fixtures.py",
               ROOT / "scripts/native_zero_width_snapshot.py"]
    bindings |= {path: sha(path) for path in helpers}
    bindings |= {current.scheduler.REPORT: sha(current.scheduler.REPORT),
                 ROOT / pluto["binary"]: sha(ROOT / pluto["binary"])}
    bindings |= {path: sha(path) for path in WORK.rglob("*") if path.is_file()}
    report = {"status": "passed", "before_entrypoint": before.builder.ENTRY,
        "after_entrypoint": current.builder.ENTRY,
        "before_binary_sha256": sha(old_binary), "after_binary_sha256": sha(new_binary),
        "same_C_sources_and_inputs": True, "baseline_configurations": results,
        "comparisons": comparisons, "profitability_measured": False,
        "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()}}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "passed", "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
