"""Compile fixed-parameter prepared-codegen successors, preserving every attempt."""

import argparse
from pathlib import Path
import subprocess

import polcert_core

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build/original-matmul/prepared-parameter-attempts"
MODULES = {"PolCertPreparedParameters", "GuardMemoryDoublePreparedAt"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module", choices=sorted(MODULES))
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    directory = "theories" if args.module == "PolCertPreparedParameters" else "adapters/compcert-memory"
    source = ROOT / f"{directory}/{args.module}.v"
    if source.with_suffix(".vo").exists():
        raise ValueError("Successful proof source and object are frozen")
    WORK.mkdir(parents=True, exist_ok=True)
    with (WORK / f"{args.module}-{args.attempt}.v").open("xb") as snapshot:
        snapshot.write(source.read_bytes())
    polcert_core.select_profile("optimizer")
    flags = [*polcert_core.load_flags(), "-Q", str(ROOT / "adapters/compcert-memory"), "GuardMemory",
             "-Q", str(ROOT / "prototype/interface"), "GuardInterface"]
    log = WORK / f"{args.module}-{args.attempt}.log"
    with log.open("x") as output:
        run = subprocess.run(["rocq", "compile", *flags, str(source)], stdout=output, stderr=subprocess.STDOUT)
    print(f"{args.module}: returncode={run.returncode}; log={log.relative_to(ROOT)}", flush=True)
    if run.returncode:
        print(log.read_text()[-5000:])
    raise SystemExit(run.returncode)


if __name__ == "__main__":
    main()
