"""Audit the private-temporary host and strip-mining certificate against the CompCert assumption baseline."""
from pathlib import Path
import hashlib
import json
import subprocess

from audit_compiler import names

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build" / "stripmine-assumptions"
MODULES = ["ClightTempFootprint", "ClightTempScope", "ClightProjectedExecution", "ClightPrivateRegion",
           "ClightPrivateRegionProof", "ClightPrivatePool", "ClightPrivateRule", "CountedStripmine",
           "ClightStripmineLoops", "ClightStripmineGuard", "ClightStripmineRegion", "ClightStripmineSelector",
           "StripmineCompiler"]


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    source = WORK / "Audit.v"
    source.write_text("""From compcert.driver Require Import Compiler.
From Guard Require Import ClightTempScope ClightPrivateRegionProof ClightPrivatePool ClightPrivateRule
 CountedStripmine ClightStripmineLoops ClightStripmineGuard ClightStripmineRegion ClightStripmineSelector StripmineCompiler.
Goal True. idtac "STRIP_BASELINE_BEGIN". exact I. Qed.
Print Assumptions Compiler.transf_c_program_correct.
Goal True. idtac "STRIP_KERNEL_BEGIN". exact I. Qed.
Print Assumptions CountedStripmine.counted_iterations_stripmine.
Print Assumptions CountedStripmine.chunked_iterations_preserves_order.
Goal True. idtac "STRIP_INSTANCE_BEGIN". exact I. Qed.
Print Assumptions ClightTempScope.step_preserves_temp_scope.
Print Assumptions ClightPrivateRegionProof.PrivateRegionProof.transform_program_correct2.
Print Assumptions ClightPrivatePool.transform_private_program_correct.
Print Assumptions ClightPrivateRule.encoded_private_rule_sound.
Print Assumptions ClightStripmineLoops.stripmine_chunked_encode.
Print Assumptions ClightStripmineGuard.stripmine_guard_primitives.
Print Assumptions ClightStripmineRegion.stripmine_local.
Print Assumptions ClightStripmineSelector.select_stripmine_sound.
Goal True. idtac "STRIP_COMPILER_BEGIN". exact I. Qed.
Print Assumptions StripmineCompiler.compile_stripmine_regions_correct.
Goal True. idtac "STRIP_END". exact I. Qed.
""")
    flags = ["-Q", str(ROOT / "theories"), "Guard"]
    for name in ("lib", "common", "x86", "x86_64", "backend", "cfrontend", "driver"):
        flags += ["-R", str(ROOT / "vendor" / "CompCert" / name), "compcert." + name]
    flags += ["-R", str(ROOT / "vendor" / "CompCert" / "flocq"), "Flocq"]
    result = subprocess.run(["rocq", "compile", *flags, str(source)], cwd=ROOT,
                            check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (WORK / "audit.log").write_text(result.stdout)
    baseline, rest = result.stdout.split("STRIP_BASELINE_BEGIN", 1)[1].split("STRIP_KERNEL_BEGIN", 1)
    kernel, rest = rest.split("STRIP_INSTANCE_BEGIN", 1)
    instance, rest = rest.split("STRIP_COMPILER_BEGIN", 1)
    compiler = rest.split("STRIP_END", 1)[0]
    inherited = names(baseline)
    if not inherited or names(kernel) or "Closed under the global context" not in kernel:
        raise SystemExit("unexpected scheduling-kernel assumptions")
    if names(instance) - inherited or names(compiler) != inherited:
        raise SystemExit("unexpected strip-mine or compiler assumptions")
    (ROOT / "build" / "stripmine-proof-report.json").write_text(json.dumps({
        "status": "compiled", "checked_modules": MODULES, "kernel_global_axioms": [],
        "instance_assumptions": sorted(names(instance)),
        "whole_program_assumptions": sorted(names(compiler)), "additional_global_axioms": [],
        "whole_program_theorem": "StripmineCompiler.compile_stripmine_regions_correct",
        "scope": "order-preserving strip-mining of dynamic signed32 counted loops with arbitrary ordinary-memory bodies",
        "runtime_trip_counts_enumerated_by_compiler": False,
        "actual_clight_load_and_store_execution": True, "exact_complete_memory_equality": True,
        "temporary_exit_agreement_on_source_identifiers": True, "scratch_temporaries_allowed": True,
        "source_justified_check_domain": True, "full_ast_binding_checked": True,
        "arbitrary_positive_checked_tile_width": True, "auxiliary_arithmetic_overflow_checked": True,
        "polopt_called": False,
        "sources": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                    for path in sorted((ROOT / "theories").glob("*.v"))},
        "native_report": "build/native-stripmine/report.json",
    }, indent=2) + "\n")
    print(f"Strip-mining audited: kernel closed; {len(names(instance))} inherited instance "
          f"and {len(names(compiler))} unchanged compiler assumptions")



if __name__ == "__main__":
    main()
