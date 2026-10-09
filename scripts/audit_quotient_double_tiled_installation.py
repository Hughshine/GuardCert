"""Audit actual quotient capture, model extension, candidate lowering and Csem-to-Asm installation."""

import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_floor_membership_service as parent
import compile_matmul_installation as compiler
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/quotient-double-tiling/installation-proof-v1"
MODULES = [ROOT / "theories" / (name+".v") for name in
           ["PolCertParameterExtension","PolCertQuotientParameter","PolCertQuotientCapture"]]
MODULES += [ROOT / "adapters/compcert-memory" / (name+".v") for name in
            ["GuardMemoryDoubleQuotientPrepared","GuardMemoryDoubleQuotientLowering",
             "GuardMemoryDoubleReductionQuotientLowering"]]
MODULES += [ROOT / "prototype/interface" / (name+".v") for name in
            ["ReductionDoubleQuotientFactory","DoubleQuotientTiledCompiler","QuotientDoubleTiledStableCompiler"]]
ENTRY = "QuotientDoubleTiledStableCompiler.compile_selected_quotient_tiled_stable_program"
KIND = "actual-quotient-capture-affine-parameter-and-scoped-Csem-to-Asm"


def endpoints():
    queried = []
    for source in MODULES:
        content = permitted(source).read_text()
        if re.search(r"\b(?:Admitted|Abort|Axiom|Parameter)\b", content):
            raise ValueError("Unproved service source: " + str(source))
        queried += [source.stem + "." + name for name in
                    re.findall(r"^Print Assumptions ([\w.]+)\.", content, re.MULTILINE)]
    return queried


def validate():
    report = json.loads(permitted(WORK / "report.json").read_text())
    if (report["status"] != "compiled" or report["kind"] != KIND
            or report["additional_global_axioms"]
            or report["endpoints"] != endpoints()
            or report["whole_program_entrypoint"] != ENTRY):
        raise ValueError("Invalid quotient installation checkpoint")
    for path, digest in report["bindings"].items():
        if sha(permitted(ROOT / path)) != digest:
            raise ValueError("Changed service input: " + path)
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
                raise ValueError("Uncompiled source: " + str(source))
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
    queried = endpoints()
    markers = [f"QUOTIENT_INSTALLATION_ENDPOINT_{i}" for i in range(len(queried) + 1)]
    code = ["From Guard Require Import PolCertQuotientParameter.",
            "From GuardMemory Require Import GuardMemoryDoubleQuotientPrepared GuardMemoryDoubleQuotientLowering GuardMemoryDoubleReductionQuotientLowering.",
            "From GuardInterface Require Import ReductionDoubleQuotientFactory DoubleQuotientTiledCompiler QuotientDoubleTiledStableCompiler."]
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
        raise ValueError("New globals: " + str(added))
    attempts = []
    for metadata in sorted(compiler.WORK.glob("*.json")):
        item = json.loads(permitted(metadata).read_text())
        if Path(item["source"]) not in {path.relative_to(ROOT) for path in MODULES}:
            continue
        snapshot, log = metadata.with_suffix(".v"), metadata.with_suffix(".log")
        if sha(permitted(snapshot)) != item["source_sha256"]:
            raise ValueError("Changed attempt: " + str(metadata))
        attempts.append({"source": str(snapshot.relative_to(ROOT)),
                         "log": str(log.relative_to(ROOT)),
                         "metadata": str(metadata.relative_to(ROOT)),
                         "compiled": item["returncode"] == 0})
        for path in [snapshot, log, metadata]:
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    for path in [Path(__file__), Path(compiler.__file__), ROOT / "toolchain.lock.json", *WORK.iterdir()]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "compiled", "kind": KIND,
              "new_modules": [str(path.relative_to(ROOT)) for path in MODULES],
              "new_source_lines": sum(len(path.read_text().splitlines()) for path in MODULES),
              "endpoints": queried, "endpoint_assumptions": actual,
              "additional_global_axioms": added, "allowed_parent_globals": sorted(allowed),
              "closed_endpoints": sum(not values for values in actual.values()),
              "maximum_endpoint_globals": max(map(len, actual.values())),
              "reachable_source_count": len(seen), "attempts": attempts,
              "whole_program_entrypoint": ENTRY, "whole_program_theorem": ENTRY + "_correct",
              "semantic_compiler_proof_unchanged": False,
              "kernel_changed": False, "new_host_contract": False,
              "parameter_extension_preserves_actual_Loop_execution": True,
              "actual_safe_private_quotient_capture_produces_typed_environment": True,
              "quotient_relation_consumed_by_final_actual_candidate_validation": True,
              "interval_instance_transport_proved": True,
              "source_user_supplies_semantic_callbacks": False,
              "actual_quotient_candidate_lowering_public_exits_and_original_fallback": True,
              "new_quotient_pass_preserves_program_when_no_installation": True,
              "prior_compiler_consumes_current_intermediate_program": True,
              "nonnegative_division_and_all_intermediate_ranges_checked": True,
              "native_or_cost_evidence_added_by_audit": False,
              "full_goal_complete": False,
              "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
              "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "compiled", "source_lines": report["new_source_lines"],
                      "endpoints": len(queried), "closed_endpoints": report["closed_endpoints"],
                      "maximum_endpoint_globals": report["maximum_endpoint_globals"],
                      "reachable_sources": len(seen), "bindings": len(bindings)}))


if __name__ == "__main__":
    main()
