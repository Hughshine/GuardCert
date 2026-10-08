"""Bind retained compatibility and native-harness failures without rerunning them."""
import json

from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/selected-loaded-affine/attempts-v1"
INPUTS = ["build/selected-loaded-affine/compat-v1",
          "build/selected-loaded-affine/native-v1",
          "build/selected-loaded-affine/native-v2"]


def main():
    if (WORK / "report.json").exists():
        report = json.loads((WORK / "report.json").read_text())
        for path, digest in report["bindings"].items():
            assert sha(ROOT / path) == digest, path
        print("Validated retained loaded-affine attempts")
        return
    bindings = {"scripts/record_selected_loaded_affine_attempts.py": sha(ROOT / "scripts/record_selected_loaded_affine_attempts.py")}
    for directory in INPUTS:
        assert (ROOT / directory).is_dir(), directory
        for path in sorted((ROOT / directory).rglob("*")):
            if path.is_file():
                bindings[str(path.relative_to(ROOT))] = sha(path)
    attempts = [json.loads((ROOT / directory / "attempt-result.json").read_text()) for directory in INPUTS[1:]]
    assert all(not row["observed_native_miscompilation"] for row in attempts)
    log = ROOT / INPUTS[0] / "ClightAffinePrivateLoadedCandidates.log"
    assert "matches several files" in log.read_text()
    initial = ROOT / "build/selected-loaded-affine/source-build/ClightLoadedAffineRegionBuilders-initial.log"
    assert "inconsistent assumptions" in initial.read_text()
    for path in [initial, initial.with_suffix(".v")]:
        bindings[str(path.relative_to(ROOT))] = sha(path)
    WORK.mkdir(parents=True, exist_ok=False)
    report = {"status": "archived", "native_attempts": attempts,
        "initial_legacy_object_mismatch_retained": True,
        "compat_v1_duplicate_logical_loadpath_failure_retained": True,
        "successful_compatibility_successor": "build/selected-loaded-affine/compat-v2/report.json",
        "successful_native_successor": "build/selected-loaded-affine/native-v3/report.json",
        "reran_historical_attempts": False, "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Archived loaded-affine attempts:", sha(WORK / "report.json"))


if __name__ == "__main__":
    main()
