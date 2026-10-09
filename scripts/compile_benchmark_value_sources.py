"""Archive and compile new value adapters without overwriting successful proofs."""

import argparse
from pathlib import Path
import subprocess

import polcert_core

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build/benchmark-alignment/floating-proof-attempts"
MODULES = {"GuardMemoryValueInstr", "GuardMemoryDoubleValue"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module", choices=sorted(MODULES))
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(char not in "abcdefghijklmnopqrstuvwxyz0123456789-" for char in args.attempt):
        raise ValueError("Use a simple attempt name")
    source = ROOT / f"adapters/compcert-memory/{args.module}.v"
    if source.with_suffix(".vo").exists():
        raise ValueError("Successful proof objects are frozen")
    WORK.mkdir(parents=True, exist_ok=True)
    with (WORK / f"{args.module}-{args.attempt}.v").open("xb") as out:
        out.write(source.read_bytes())
    polcert_core.select_profile("optimizer")
    flags = [*polcert_core.load_flags(), "-Q", str(ROOT / "adapters/compcert-memory"), "GuardMemory"]
    log = WORK / f"{args.module}-{args.attempt}.log"
    with log.open("x") as out:
        result = subprocess.run(["rocq", "compile", *flags, str(source)], stdout=out, stderr=subprocess.STDOUT)
    print(f"{args.module}: returncode={result.returncode}; log={log.relative_to(ROOT)}", flush=True)
    if result.returncode:
        print(log.read_text()[-2500:])
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
