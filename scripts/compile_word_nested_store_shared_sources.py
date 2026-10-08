"""Compile missing loaded store-list candidate and selected compiler modules while preserving successful objects."""
import argparse
from pathlib import Path
import subprocess

import audit_word_nested_store_shared as audit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", default="initial")
    args = parser.parse_args()
    assert args.attempt.replace("-", "").replace("_", "").isalnum()
    parent = audit.parent_inputs()
    work = audit.ROOT / "build/multi-word-nested-shared/source-build"
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
            subprocess.run(["rocq", "compile", *audit.language.flags(), file], cwd=audit.ROOT,
                           stdout=output, stderr=subprocess.STDOUT, check=True)
        print("Compiled", file, flush=True)
    assert parent == audit.parent_inputs(), "A historical proof input changed"


if __name__ == "__main__":
    main()
