"""Archive and compile typed original-matmul bridge successors."""

import argparse
from pathlib import Path
import subprocess

import polcert_core

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build/original-matmul/attempts"
MODULES = {"GuardMemoryObservationDeterminism", "GuardMemoryDoubleSource",
           "GuardMemoryDoubleLocations", "GuardMemoryDoubleAssignment", "GuardMemoryLongControl",
           "GuardMemoryDoubleMatmul", "GuardMemoryDoubleMatmulInstr", "GuardMemoryDoublePolyhedral"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module", choices=sorted(MODULES))
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    source = ROOT / f"adapters/compcert-memory/{args.module}.v"
    if source.with_suffix(".vo").exists():
        raise ValueError("Successful source and proof objects are frozen")
    WORK.mkdir(parents=True, exist_ok=True)
    with (WORK / f"{args.module}-{args.attempt}.v").open("xb") as output:
        output.write(source.read_bytes())
    polcert_core.select_profile("optimizer")
    flags = [*polcert_core.load_flags(), "-Q", str(ROOT / "adapters/compcert-memory"), "GuardMemory"]
    log = WORK / f"{args.module}-{args.attempt}.log"
    with log.open("x") as output:
        result = subprocess.run(["rocq", "compile", *flags, str(source)], stdout=output, stderr=subprocess.STDOUT)
    print(f"{args.module}: returncode={result.returncode}; log={log.relative_to(ROOT)}", flush=True)
    if result.returncode:
        print(log.read_text()[-3500:])
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
