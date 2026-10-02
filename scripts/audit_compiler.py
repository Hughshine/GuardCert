"""Compare the actual extracted driver's theorem assumptions with CompCert."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
UPSTREAM = ROOT / "vendor" / "CompCert"
WORK = ROOT / "build" / "compiler-assumptions"


def names(text):
    return set(re.findall(r"^([\w.]+)\s*:", text, re.MULTILINE)) - {"Axioms", "Warning"}


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    source = WORK / "Audit.v"
    source.write_text("""From compcert.driver Require Import Compiler.
From Guard Require Import RegionCompiler.
Goal True. idtac "GUARD_BASELINE_BEGIN". exact I. Qed.
Print Assumptions Compiler.transf_c_program_correct.
Goal True. idtac "GUARD_DRIVER_BEGIN". exact I. Qed.
Print Assumptions RegionCompiler.compile_property_regions_correct.
Goal True. idtac "GUARD_ASSUMPTIONS_END". exact I. Qed.
""")
    flags = ["-Q", str(ROOT / "theories"), "Guard"]
    for name in ("lib", "common", "x86", "x86_64", "backend", "cfrontend", "driver"):
        flags += ["-R", str(UPSTREAM / name), "compcert." + name]
    flags += ["-R", str(UPSTREAM / "flocq"), "Flocq"]
    result = subprocess.run(["rocq", "compile", *flags, str(source)], cwd=ROOT,
                            check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (WORK / "audit.log").write_text(result.stdout)
    baseline, adapted = result.stdout.split("GUARD_BASELINE_BEGIN", 1)[1].split("GUARD_DRIVER_BEGIN", 1)
    adapted = adapted.split("GUARD_ASSUMPTIONS_END", 1)[0]
    upstream_names, driver_names = names(baseline), names(adapted)
    if not upstream_names or not driver_names or driver_names - upstream_names:
        raise SystemExit(f"unexpected compiler assumptions: {sorted(driver_names - upstream_names)}")
    (ROOT / "build" / "compiler-assumptions-report.json").write_text(json.dumps({
        "upstream_theorem": "Compiler.transf_c_program_correct",
        "adapted_theorem": "RegionCompiler.compile_property_regions_correct",
        "upstream_assumptions": sorted(upstream_names), "adapted_assumptions": sorted(driver_names),
        "additional_global_axioms": [],
        "theorem_source_sha256": hashlib.sha256((ROOT / "theories" / "RegionCompiler.v").read_bytes()).hexdigest(),
    }, indent=2) + "\n")
    print(f"compiler assumptions audited: {len(driver_names)} inherited, no additional global axioms")


if __name__ == "__main__":
    main()
