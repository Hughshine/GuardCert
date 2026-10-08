"""Compile missing store-sequence modules while preserving successful objects."""
import argparse
from pathlib import Path
import subprocess

import audit_word_store_sequence as audit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", default="initial")
    args = parser.parse_args()
    assert args.attempt.replace("-", "").replace("_", "").isalnum()
    baseline = audit.baseline_inputs()
    flags = audit.language.flags()
    work = audit.ROOT / "build/multi-word-sequence/source-build"
    work.mkdir(parents=True, exist_ok=True)
    for file in audit.MODULES:
        source = audit.permitted(audit.ROOT / file)
        obj = source.with_suffix(".vo")
        if obj.exists():
            assert obj.stat().st_mtime >= source.stat().st_mtime, "Use a successor module: " + file
            print("Preserved", file, flush=True)
            continue
        log = work / (Path(file).stem + "-" + args.attempt + ".log")
        with log.open("x") as output:
            subprocess.run(["rocq", "compile", *flags, file], cwd=audit.ROOT,
                           stdout=output, stderr=subprocess.STDOUT, check=True)
        print("Compiled", file, flush=True)
    assert baseline == audit.baseline_inputs(), "A historical proof input changed"


if __name__ == "__main__":
    main()
