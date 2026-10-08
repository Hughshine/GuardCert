"""Compile only missing affine-access scan modules; preserve frozen inputs."""
from pathlib import Path
import subprocess

import audit_multi_tensor_affine_scan as audit


def main():
    frozen = audit.inputs()
    flags = audit.language.flags()
    work = audit.ROOT / "build/multi-tensor-affine-scan/source-build"
    work.mkdir(parents=True, exist_ok=True)
    for file in audit.MODULES:
        source = audit.ROOT / file
        obj = source.with_suffix(".vo")
        if obj.exists():
            assert obj.stat().st_mtime >= source.stat().st_mtime, "Use a successor module: " + file
            print("Preserved", file, flush=True)
            continue
        log = work / (Path(file).stem + ".log")
        with log.open("x") as output:
            subprocess.run(["rocq", "compile", *flags, file], cwd=audit.ROOT,
                           stdout=output, stderr=subprocess.STDOUT, check=True)
        print("Compiled", file, flush=True)
    assert frozen == audit.inputs(), "A historical proof input changed"


if __name__ == "__main__":
    main()
