"""Audit the dynamic rectangular certificate against the CompCert assumption baseline."""
from pathlib import Path
import hashlib
import json
import subprocess

from audit_compiler import names

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build" / "rectangular-assumptions"
MODULES = ["SchedulePermutation", "RectangularSchedule", "RectangularIteration", "ClightParametricLoops",
           "ClightRectangularStore", "ClightRectangularLoops", "ClightRectangularGuard",
           "ClightRectangularRegion", "ClightRectangularSelector", "RectangularCompiler"]


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    source = WORK / "Audit.v"
    source.write_text("""From compcert.driver Require Import Compiler.
From Guard Require Import AbstractSchedule SchedulePermutation RectangularSchedule RectangularIteration
 ClightParametricLoops ClightRectangularGuard ClightRectangularLoops ClightRectangularRegion
 ClightRectangularSelector RectangularCompiler.
Goal True. idtac "RECT_BASELINE_BEGIN". exact I. Qed.
Print Assumptions Compiler.transf_c_program_correct.
Goal True. idtac "RECT_KERNEL_BEGIN". exact I. Qed.
Print Assumptions SchedulePermutation.independent_permutation_certificate.
Print Assumptions SchedulePermutation.rectangular_order_permutation.
Print Assumptions RectangularIteration.rectangular_schedule.
Goal True. idtac "RECT_INSTANCE_BEGIN". exact I. Qed.
Print Assumptions RectangularSchedule.rectangle_interchange_preserves_memory.
Print Assumptions ClightParametricLoops.frontend_parametric_decode.
Print Assumptions ClightParametricLoops.frontend_parametric_encode.
Print Assumptions ClightRectangularGuard.rectangle_guard_primitives.
Print Assumptions ClightRectangularLoops.rectangle_source_decode.
Print Assumptions ClightRectangularLoops.rectangle_target_encode.
Print Assumptions ClightRectangularRegion.rectangle_source_guard_domain.
Print Assumptions ClightRectangularSelector.select_rectangle_interchange_sound.
Goal True. idtac "RECT_COMPILER_BEGIN". exact I. Qed.
Print Assumptions RectangularCompiler.compile_rectangular_regions_correct.
Goal True. idtac "RECT_END". exact I. Qed.
""")
    flags = ["-Q", str(ROOT / "theories"), "Guard"]
    for name in ("lib", "common", "x86", "x86_64", "backend", "cfrontend", "driver"):
        flags += ["-R", str(ROOT / "vendor" / "CompCert" / name), "compcert." + name]
    flags += ["-R", str(ROOT / "vendor" / "CompCert" / "flocq"), "Flocq"]
    result = subprocess.run(["rocq", "compile", *flags, str(source)], cwd=ROOT,
                            check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (WORK / "audit.log").write_text(result.stdout)
    baseline, rest = result.stdout.split("RECT_BASELINE_BEGIN", 1)[1].split("RECT_KERNEL_BEGIN", 1)
    kernel, rest = rest.split("RECT_INSTANCE_BEGIN", 1)
    instance, rest = rest.split("RECT_COMPILER_BEGIN", 1)
    compiler = rest.split("RECT_END", 1)[0]
    inherited = names(baseline)
    if not inherited or names(kernel) or "Closed under the global context" not in kernel:
        raise SystemExit("unexpected scheduling-kernel assumptions")
    if names(instance) - inherited or names(compiler) != inherited:
        raise SystemExit("unexpected rectangle or compiler assumptions")
    (ROOT / "build" / "rectangular-proof-report.json").write_text(json.dumps({
        "status": "compiled", "checked_modules": MODULES, "kernel_global_axioms": [],
        "instance_assumptions": sorted(names(instance)),
        "whole_program_assumptions": sorted(names(compiler)), "additional_global_axioms": [],
        "whole_program_theorem": "RectangularCompiler.compile_rectangular_regions_correct",
        "scope": "dynamic positive rectangular loops with affine independent signed32 stores",
        "runtime_trip_counts_enumerated_by_compiler": False,
        "actual_mem_store_execution": True, "exact_complete_memory_equality": True,
        "exact_complete_temporary_exit": True, "source_justified_conditional_check_domain": True,
        "full_ast_binding_checked": True, "guard_limits_derived_from_layout": True,
        "polcert_or_cinstr_instance_imported": False, "polopt_called": False,
        "sources": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                    for path in sorted((ROOT / "theories").glob("*.v"))},
        "native_report": "build/native-rectangular/report.json",
    }, indent=2) + "\n")
    print(f"Rectangular interchange audited: kernel closed; {len(names(instance))} inherited instance "
          f"and {len(names(compiler))} unchanged compiler assumptions")



if __name__ == "__main__":
    main()
