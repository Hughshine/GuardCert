"""Compile affine observation successors, archiving every source and log."""
import argparse
from pathlib import Path
import subprocess

import audit_zero_width_stability as parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module")
    parser.add_argument("--attempt", default="initial")
    args = parser.parse_args()
    assert args.attempt.replace("-", "").replace("_", "").isalnum()
    source = parent.permitted(parent.ROOT / args.module)
    assert source.parent == parent.ROOT / "prototype/interface"
    assert source.name.startswith("ClightAffine") or source.name.startswith("ClightSelected")
    assert source.suffix == ".v"
    assert not source.with_suffix(".vo").exists(), "Preserve successful objects; use a successor"
    work = parent.ROOT / "build/affine-observation/source-build"
    work.mkdir(parents=True, exist_ok=True)
    with (work / (source.stem + "-" + args.attempt + ".v")).open("xb") as snapshot:
        snapshot.write(source.read_bytes())
    with (work / (source.stem + "-" + args.attempt + ".log")).open("x") as output:
        result = subprocess.run(["rocq", "compile", *parent.language.flags(), str(source)],
                                cwd=parent.ROOT, stdout=output, stderr=subprocess.STDOUT)
    print("Compiled" if result.returncode == 0 else "Rejected", args.module, flush=True)
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
