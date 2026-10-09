"""Bind initialized double tiling and composition with the existing actual Csem-to-Asm compiler."""

import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_double_reindexed_tiled_installation as parent
import compile_matmul_installation as compiler
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/initialized-double-tiling/installation-proof-v1"
MODULES = []
MODULES += [ROOT / "adapters/compcert-memory" / (name + ".v") for name in
            ["GuardMemoryDoubleInitializedTiledLowering"]]
MODULES += [ROOT / "prototype/interface" / (name + ".v") for name in
            ["InitializedDoubleTiledRegionFactory", "InitializedDoubleTiledChoicesCompiler"]]
ENTRY = "InitializedDoubleTiledChoicesCompiler.compile_selected_initialized_tiled_choices_program"


def endpoints():
    result = ["GuardMemoryDoubleExtractedTiling.double_tiling_state_eq_exact"]
    for source in MODULES:
        content = permitted(source).read_text()
        if re.search(r"\b(?:Admitted|Abort|Axiom|Parameter)\b", content):
            raise ValueError(f"Unproved source: {source}")
        prefix = ("GuardMemoryDoubleExtractedTiling.DoubleTiling" if source.stem == "PolCertTilingProgress"
                  else source.stem)
        result += [prefix + "." + name for name in
                   re.findall(r"^Print Assumptions ([\w.]+)\.", content, re.MULTILINE)]
    return result


def validate():
    report = json.loads((WORK / "report.json").read_text())
    if (report["status"] != "compiled" or report["additional_global_axioms"]
            or report["endpoints"] != endpoints()
            or report["whole_program_entrypoint"] != ENTRY):
        raise ValueError("Invalid double tiling installation checkpoint")
    for name, digest in report["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError(f"Changed proof input: {name}")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate:
        report = validate()
        print(json.dumps({"status": "validated", "bindings": len(report["bindings"]),
                          "report_sha256": sha(WORK / "report.json")}))
        return
    baseline = parent.validate()
    allowed = set(baseline["allowed_parent_globals"])
    if len(allowed) != 42:
        raise ValueError("Wrong inherited compiler baseline")
    WORK.mkdir(parents=True, exist_ok=False)
    bindings = dict(baseline["bindings"])
    bindings[str((parent.WORK / "report.json").relative_to(ROOT))] = sha(parent.WORK / "report.json")
    flags = compiler.lowering.flags()
    queried = endpoints()
    frontier, seen, level = MODULES, set(), 0
    while frontier:
        current = sorted(set(frontier) - seen)
        if not current:
            break
        seen.update(current)
        for source in current:
            source = permitted(source)
            obj = permitted(source.with_suffix(".vo"))
            if not obj.exists() or obj.stat().st_mtime < source.stat().st_mtime:
                raise ValueError(f"Uncompiled source: {source}")
            for path in [source, obj]:
                bindings[str(path.relative_to(ROOT))] = sha(path)
        run = subprocess.run(["rocq", "dep", *flags, *map(str, current)], cwd=ROOT,
                             capture_output=True, text=True, check=True)
        (WORK / f"dependencies-{level}.log").write_text(run.stdout + run.stderr)
        frontier = []
        for line in run.stdout.splitlines():
            if ": " not in line:
                continue
            for token in line.split(": ", 1)[1].split():
                if token.endswith(".vo"):
                    obj = permitted(ROOT / token)
                    bindings[str(obj.relative_to(ROOT))] = sha(obj)
                    source = permitted(obj.with_suffix(".v"))
                    if source.exists() and source not in seen:
                        frontier.append(source)
        level += 1
    markers = [f"DOUBLE_TILING_ENDPOINT_{i}" for i in range(len(queried) + 1)]
    code = ["From GuardInterface Require Import InitializedDoubleTiledChoicesCompiler.",
            "From GuardMemory Require Import GuardMemoryDoubleInitializedTiledLowering."]
    for marker, endpoint in zip(markers, queried):
        code += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {endpoint}."]
    code += [f'Goal True. idtac "{markers[-1]}". exact I. Qed.']
    (WORK / "Audit.v").write_text("\n".join(code) + "\n")
    run = subprocess.run(["rocq", "compile", *flags, str(WORK / "Audit.v")],
                         cwd=ROOT, capture_output=True, text=True)
    (WORK / "assumptions.log").write_text(run.stdout + run.stderr)
    if run.returncode:
        raise ValueError(run.stderr)
    actual = {endpoint: sorted(names(run.stdout.split(markers[i] + "\n", 1)[1]
                                   .split(markers[i + 1] + "\n", 1)[0]))
              for i, endpoint in enumerate(queried)}
    added = sorted(set().union(*map(set, actual.values())) - allowed)
    if added:
        raise ValueError(f"New globals: {added}")
    attempts = []
    for metadata in sorted(compiler.WORK.glob("*.json")):
        item = json.loads(metadata.read_text())
        if Path(item["source"]) not in {path.relative_to(ROOT) for path in MODULES}:
            continue
        snapshot, log = metadata.with_suffix(".v"), metadata.with_suffix(".log")
        if sha(snapshot) != item["source_sha256"]:
            raise ValueError(f"Changed attempt: {metadata}")
        attempts.append({"source": str(snapshot.relative_to(ROOT)),
                         "log": str(log.relative_to(ROOT)),
                         "metadata": str(metadata.relative_to(ROOT)),
                         "compiled": item["returncode"] == 0})
        for path in [snapshot, log, metadata]:
            bindings[str(path.relative_to(ROOT))] = sha(path)
    for path in [Path(__file__), Path(compiler.__file__), ROOT / "toolchain.lock.json", *WORK.iterdir()]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "compiled", "kind": "actual-initialized-double-tiled-loop-factory-scoped-csem-to-asm",
              "new_modules": [str(path.relative_to(ROOT)) for path in MODULES],
              "new_source_lines": sum(len(path.read_text().splitlines()) for path in MODULES),
              "endpoints": queried, "endpoint_assumptions": actual,
              "additional_global_axioms": added, "allowed_parent_globals": sorted(allowed),
              "closed_endpoints": sum(not values for values in actual.values()),
              "maximum_endpoint_globals": max(map(len, actual.values())),
              "reachable_source_count": len(seen), "attempts": attempts,
              "whole_program_entrypoint": ENTRY, "whole_program_theorem": ENTRY + "_correct",
              "source_family": "common-bound signed-I64 initialized nests with two checked IEEE-double assignments; retain preceding reduction and affine routes",
              "constructive_tiling_progress_parameterized_by_existing_POLIRS": True,
              "concrete_state_equality_law_proved": True,
              "phase_schedule_and_tiling_validation_then_prepared_codegen": True,
              "raw_to_adapted_equivalence_assumed": False,
              "final_actual_candidate_checked_at_captured_parameters": True,
              "finite_untrusted_coordinate_choices_checked": True,
              "actual_candidate_execution_transported_by_proved_coordinate_isomorphism": True,
              "actual_Clight_candidate_lowering_and_public_exit_restore": True,
              "source_model_guard_frame_and_scope_obligations_internal_to_factory": True,
              "fallback_is_original_source": True,
              "source_user_supplies_semantic_callbacks": False,
              "subsequent_affine_pass_consumes_current_intermediate_program": True,
              "generic_kernel_changed": False, "new_host_contract": False,
              "new_native_or_cost_evidence": False,
              "installed_original_benchmark_coverage_increased": False,
              "full_goal_complete": False,
              "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
              "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "compiled", "source_lines": report["new_source_lines"],
                      "endpoints": len(queried), "closed_endpoints": report["closed_endpoints"],
                      "maximum_endpoint_globals": report["maximum_endpoint_globals"],
                      "reachable_sources": len(seen), "bindings": len(bindings),
                      "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
