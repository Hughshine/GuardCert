"""Audit the abstract transport kernel and its concrete Clight instance."""
from pathlib import Path
import hashlib
import json
import subprocess

from audit_compiler import names

ROOT = Path(__file__).resolve().parents[1]
UPSTREAM = ROOT / "vendor" / "CompCert"
WORK = ROOT / "build" / "memory-transport-assumptions"


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    source = WORK / "Audit.v"
    source.write_text("""From compcert.driver Require Import Compiler.
From Guard Require Import BilateralTransport ClightMemorySteps.
Goal True. idtac "TRANSPORT_BASELINE_BEGIN". exact I. Qed.
Print Assumptions Compiler.transf_c_program_correct.
Goal True. idtac "TRANSPORT_KERNEL_BEGIN". exact I. Qed.
Print Assumptions BilateralTransport.action_mutual_transport.
Print Assumptions BilateralTransport.observation_mutual_transport.
Goal True. idtac "TRANSPORT_CLIGHT_BEGIN". exact I. Qed.
Print Assumptions ClightMemorySteps.step_memory_transport.
Print Assumptions ClightMemorySteps.star_memory_transport.
Goal True. idtac "TRANSPORT_ASSUMPTIONS_END". exact I. Qed.
""")
    flags = ["-Q", str(ROOT / "theories"), "Guard"]
    for name in ("lib", "common", "x86", "x86_64", "backend", "cfrontend", "driver"):
        flags += ["-R", str(UPSTREAM / name), "compcert." + name]
    flags += ["-R", str(UPSTREAM / "flocq"), "Flocq"]
    result = subprocess.run(["rocq", "compile", *flags, str(source)], cwd=ROOT,
                            check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (WORK / "audit.log").write_text(result.stdout)
    baseline, rest = result.stdout.split("TRANSPORT_BASELINE_BEGIN", 1)[1].split("TRANSPORT_KERNEL_BEGIN", 1)
    kernel, rest = rest.split("TRANSPORT_CLIGHT_BEGIN", 1)
    adapted = rest.split("TRANSPORT_ASSUMPTIONS_END", 1)[0]
    if names(kernel) or kernel.count("Closed under the global context") != 2:
        raise SystemExit("unexpected transport-kernel global assumptions")
    baseline_names, adapted_names = names(baseline), names(adapted)
    if not baseline_names or not adapted_names or adapted_names - baseline_names:
        raise SystemExit(f"unexpected Clight transport assumptions: {sorted(adapted_names - baseline_names)}")
    sources = ["BilateralTransport", "CompCertMemoryEquivalence", "CompCertOperatorEquivalence",
               "ClightMemoryEquivalence", "ClightMemorySteps"]
    (ROOT / "build" / "memory-transport-report.json").write_text(json.dumps({
        "status": "compiled", "kernel_global_axioms": [],
        "upstream_theorem": "Compiler.transf_c_program_correct",
        "adapted_theorems": ["ClightMemorySteps.step_memory_transport", "ClightMemorySteps.star_memory_transport"],
        "upstream_assumptions": sorted(baseline_names), "adapted_assumptions": sorted(adapted_names),
        "additional_global_axioms": [],
        "sources": {"theories/" + name + ".v": hashlib.sha256(
            (ROOT / "theories" / (name + ".v")).read_bytes()).hexdigest() for name in sources},
        "region_replacement_exit_relation_upgraded": False,
        "private_temporary_frame_supported": False,
    }, indent=2) + "\n")
    print(f"memory transport audited: kernel closed; {len(adapted_names)} inherited Clight assumptions")


if __name__ == "__main__":
    main()
