"""Compile missing multi-tensor modules while preserving existing proof objects.

The validated loaded-word compiler closure is a prerequisite. Once a module
has compiled successfully, use the independent audit; this helper never
overwrites its object.
"""
from pathlib import Path
import subprocess

import audit_multi_tensor as audit


def main():
    frozen = audit.inputs()
    flags = audit.language.flags()
    work = audit.ROOT / "build/multi-tensor/source-build"
    work.mkdir(parents=True, exist_ok=True)
    for file in audit.MODULES:
        source = audit.ROOT / file
        obj = source.with_suffix(".vo")
        if obj.exists():
            assert obj.stat().st_mtime >= source.stat().st_mtime, "Use a successor module: " + file
            print("Preserved", file, flush=True)
            continue
        log = work / (Path(file).stem + ".log")
        assert not log.exists(), "Preserve this attempt and choose a fresh build directory"
        with log.open("w") as output:
            subprocess.run(["rocq", "compile", *flags, file], cwd=audit.ROOT,
                           stdout=output, stderr=subprocess.STDOUT, check=True)
        print("Compiled", file, flush=True)
    assert frozen == audit.inputs(), "A historical proof input changed"


if __name__ == "__main__":
    main()
