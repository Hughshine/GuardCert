"""Compile installation successors, preserving each attempt and freezing successful sources."""

import argparse
import json
from pathlib import Path
import subprocess

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
import prove_original_matmul_double_lowering as lowering

WORK = ROOT / "build/original-matmul/installation-attempts-v1"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", help="New proof source relative to the repository")
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    source = permitted(ROOT / args.source)
    if source.suffix != ".v" or source.parent not in {ROOT / "theories", ROOT / "adapters/compcert-memory", ROOT / "prototype/interface"}:
        raise ValueError("Expected a proof source in an existing module directory")
    if source.with_suffix(".vo").exists():
        raise ValueError("Successful proof source and object are frozen")
    WORK.mkdir(parents=True, exist_ok=True)
    base = WORK / f"{source.stem}-{args.attempt}"
    snapshot = base.with_suffix(".v")
    with snapshot.open("xb") as archive:
        archive.write(source.read_bytes())
    argv = ["rocq", "compile", "-time", *lowering.flags(), str(source)]
    with base.with_suffix(".log").open("x") as log:
        run = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    base.with_suffix(".json").write_text(json.dumps({"source": str(source.relative_to(ROOT)),
        "source_sha256": sha(snapshot), "returncode": run.returncode, "command": argv}, indent=2)+"\n")
    print(json.dumps({"module": source.stem, "returncode": run.returncode,
                      "log": str(base.with_suffix(".log").relative_to(ROOT))}), flush=True)
    if run.returncode:
        print(base.with_suffix(".log").read_text()[-5000:])
    raise SystemExit(run.returncode)


if __name__ == "__main__":
    main()
