"""Compile only missing canonical alias modules, preserving successful objects."""
import argparse
from pathlib import Path
import subprocess

import audit_canonical_alias as audit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", default="initial")
    args = parser.parse_args()
    assert args.attempt.replace("-", "").replace("_", "").isalnum()
    parent = audit.parent_inputs()
    work = audit.ROOT / "build/canonical-difference/source-build"
    work.mkdir(parents=True, exist_ok=True)
    for file in audit.MODULES:
        source = audit.permitted(audit.ROOT / file)
        obj = source.with_suffix(".vo")
        if obj.exists():
            assert obj.stat().st_mtime >= source.stat().st_mtime, "Use a successor module: " + file
            print("Preserved", file, flush=True)
            continue
        snapshot = work / (Path(file).stem + "-" + args.attempt + ".v")
        with snapshot.open("xb") as output:
            output.write(source.read_bytes())
        log = work / (Path(file).stem + "-" + args.attempt + ".log")
        with log.open("x") as output:
            subprocess.run(["rocq", "compile", *audit.language.flags(), file], cwd=audit.ROOT,
                           stdout=output, stderr=subprocess.STDOUT, check=True)
        print("Compiled", file, flush=True)
    assert parent == audit.parent_inputs(), "A historical proof input changed"


if __name__ == "__main__":
    main()
