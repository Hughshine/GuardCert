"""Bind incomplete pipeline attempts separately from successful native tiers."""
import json
from pathlib import Path

from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/selected-affine-pipeline/attempts-v1"
ATTEMPTS = {
    "unprofiled-tile": "smoke-initial/tile",
    "unprofiled-schedule": "smoke-schedule/schedule",
    "negative-profile-two-dimensional": "smoke-profiled-2d/tile",
    "three-dimensional-profiled-codegen": "smoke-profiled/tile",
}


def main():
    if (WORK / "report.json").exists():
        report = json.loads((WORK / "report.json").read_text())
        for path, digest in report["bindings"].items():
            assert sha(ROOT / path) == digest, path
        print(json.dumps({"status": "validated", "report_sha256": sha(WORK / "report.json")}))
        return
    WORK.mkdir(parents=True, exist_ok=False)
    bindings = {Path(__file__): sha(Path(__file__))}
    results = {}
    for name, relative in ATTEMPTS.items():
        directory = ROOT / "build/selected-affine-pipeline" / relative
        command = json.loads((directory / "compile-command.json").read_text())
        compiler = Path(command["argv"][0])
        assert compiler.is_relative_to(ROOT)
        bindings[compiler] = sha(compiler)
        bindings[compiler.parent / ".guard-build.json"] = sha(compiler.parent / ".guard-build.json")
        facts = {"compile_command": str((directory / "compile-command.json").relative_to(ROOT)),
                 "compiler_sha256": sha(compiler), "successful_native_tier": False}
        phases = sorted((directory / "phases").glob("guardcert-*-phase-*"))
        if name.startswith("unprofiled"):
            assert phases and all((phase / "refusal.txt").exists() for phase in phases)
            facts["result"] = "all generated proposals refused; original program output checked by incomplete smoke"
            facts["reasons"] = sorted(set((phase / "refusal.txt").read_text().strip() for phase in phases))
        elif name == "negative-profile-two-dimensional":
            diagnostics = [phase / "whole-candidate-check-diagnostic.txt" for phase in phases
                           if (phase / "whole-candidate-check-diagnostic.txt").exists()]
            assert diagnostics and all(path.read_text() == "valid=false\nalarm-free=true\n" for path in diagnostics)
            facts["result"] = "phase-validated proposals refused by original whole-candidate checker"
            facts["negative_coordinate_enclosure_gap"] = True
        else:
            phase = next(phase for phase in phases if (phase / "source-rank.txt").read_text() == "3\n")
            assert (phase / "affine-result.txt").read_text() == "accepted\n"
            assert (phase / "tiling-result.txt").read_text() == "accepted\n"
            assert not (phase / "raw-statement-0.loop").exists()
            assert not (directory / "program.s").exists()
            facts |= {"result": "observed subprocess.TimeoutExpired after the 600-second compiler deadline",
                      "observed_outcome_not_inferred_from_absent_output": True,
                      "compiler_timeout_seconds": 600,
                      "last_completed_stage": "affine and tiling transition validation",
                      "pending_call": "first per-statement prepared_codegen",
                      "other_functional_checks_ran_concurrently": True,
                      "independent_compile_cost_measurement": False}
        results[name] = facts
        bindings |= {path: sha(path) for path in directory.rglob("*") if path.is_file()}
    bindings |= {ROOT / path: sha(ROOT / path) for path in
                 ["scripts/native_selected_affine_pipeline.py", "scripts/selected_affine_pipeline_fixtures.py",
                  "scripts/native_profiled_affine_2d_pipeline.py", "scripts/selected_affine_2d_fixtures.py"]}
    report = {"status": "recorded-incomplete-attempts", "attempts": results,
              "semantic_compiler_theorem_invalidated": False,
              "new_accepted_three_dimensional_native_case": False,
              "goal_complete": False,
              "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()}}
    (WORK / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"status": report["status"], "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
