"""Export the original pinned matmul Clight AST without changing its computation."""

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / "build/affine-empty-runtime/compiler-v1"
SOURCE = ROOT / "build/benchmark-alignment/probe-v1/matmul/marked.c"
WORK = ROOT / "build/original-matmul/frontend-v1"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(argv, cwd, label, env):
    with (WORK / f"{label}.log").open("x") as log:
        result = subprocess.run(argv, cwd=cwd, env=env, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        raise ValueError(f"{label} failed: {(WORK / f'{label}.log').read_text()[-4000:]}")
    return argv


def main():
    if WORK.exists():
        raise ValueError("AST checkpoint already exists")
    compiler = json.loads((PARENT / ".guard-build.json").read_text())
    if sha(PARENT / "ccomp") != compiler["compiler_sha256"]:
        raise ValueError("Changed parent compiler")
    probe = json.loads((ROOT / "build/benchmark-alignment/probe-v1/report.json").read_text())
    if probe["bindings"][str(SOURCE.relative_to(ROOT))] != sha(SOURCE):
        raise ValueError("Changed original benchmark source")
    WORK.mkdir(parents=True)
    target = WORK / "tools"
    shutil.copytree(PARENT, target)
    bindings = {str(path.relative_to(ROOT)): sha(path) for path in PARENT.rglob("*") if path.is_file()}
    source = WORK / "marked.c"
    shutil.copy2(SOURCE, source)
    env = {key: value for key, value in os.environ.items() if not key.startswith("GUARDCERT_")}
    commands = [run(["make", "-j4", "-f", "Makefile.extr", "clightgen"], target, "build", env)]
    commands.append(run([str(target / "clightgen"), "-fall", "-short-idents", "-dclight",
                         "-stdlib", str(target / "runtime"), "-o", str(WORK / "OriginalMatmul.v"), str(source)],
                        WORK, "export", env))
    for path in [SOURCE, Path(__file__), ROOT / "toolchain.lock.json", WORK / "marked.c",
                 WORK / "marked.light.c", WORK / "OriginalMatmul.v", target / "clightgen",
                 WORK / "build.log", WORK / "export.log"]:
        bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "exported", "source": str(SOURCE.relative_to(ROOT)), "commands": commands,
              "source_adaptations": "none beyond the existing scop markers",
              "Clight_normalize_extra_pass": False, "original_float_and_long_types_retained": True,
              "frontend_is_trusted_boundary": True, "optimization_installed": False,
              "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items() if key != "bindings"}))


if __name__ == "__main__":
    main()
