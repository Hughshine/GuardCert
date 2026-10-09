"""Resolve two pinned harness constant initializers while preserving their types."""

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build/benchmark-alignment/harness-compat-v1"
PARENT = ROOT / "build/benchmark-alignment/probe-v1/report.json"
COMPILER = ROOT / "build/affine-empty-runtime/compiler-v1/ccomp"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(argv, directory, name, env=None):
    result = subprocess.run(argv, cwd=directory, env=env, capture_output=True, timeout=90)
    (directory / f"{name}.stdout").write_bytes(result.stdout)
    (directory / f"{name}.stderr").write_bytes(result.stderr)
    return result


def main():
    if WORK.exists():
        raise ValueError("Compatibility checkpoint already exists")
    parent = json.loads(PARENT.read_text())
    for path, digest in parent["bindings"].items():
        if sha(ROOT / path) != digest:
            raise ValueError(f"Changed parent binding: {path}")
    WORK.mkdir()
    rows = []
    for case in ["corcol3", "pca"]:
        original = PARENT.parent / case
        source = (original / "marked.c").read_text()
        parameters = {name: int(value) for name, value in re.findall(r"^static const long long (\w+) = (-?\d+);$", source, re.M)}
        changes = []
        def replace(match):
            scalar, parameter = match.groups()
            if parameter not in parameters:
                raise ValueError("Initializer does not refer to a fixed harness parameter")
            initializer = f"(double){parameter}"
            if f"  {scalar} = {initializer};" not in source:
                raise ValueError("Original init_data does not restore this scalar")
            replacement = f"static double {scalar} = (double){parameters[parameter]};"
            changes.append({"old": match.group(), "new": replacement,
                            "reason": "fixed const long long initializer folded to its same typed literal"})
            return replacement
        adapted = re.sub(r"^static double (\w+) = \(double\)(\w+);$", replace, source, flags=re.M)
        if not changes:
            raise ValueError("Expected initializer incompatibility was not found")
        directory = WORK / case
        directory.mkdir()
        (directory / "adapted.c").write_text(adapted)
        (directory / "source-adaptations.json").write_text(json.dumps(changes, indent=2) + "\n")
        expected = (original / "reference-run.stdout").read_bytes()
        gcc = run(["gcc", "-O0", "-ffp-contract=off", str(directory / "adapted.c"), "-lm", "-o", str(directory / "reference")], directory, "reference-build")
        if gcc.returncode:
            raise ValueError(gcc.stderr.decode())
        reference = run([str(directory / "reference")], directory, "reference-run")
        if reference.returncode or reference.stdout != expected:
            raise ValueError("The adaptation changed the original GCC modeled-state observation")
        row = {"case": case, "changes": changes, "original_GCC_digest_retained": True, "configurations": {}}
        for mode, old in next(row for row in parent["results"] if row["case"] == case)["configurations"].items():
            target = directory / mode
            target.mkdir()
            env = {key: value for key, value in os.environ.items() if not key.startswith("GUARDCERT_")}
            env.update(old["environment"])
            env["GUARDCERT_PIPELINE_DUMP"] = str(target / "phases")
            argv = [str(COMPILER), "-fall", "-stdlib", str(COMPILER.parent / "runtime"), "-dclight", "-S",
                    "-o", str(target / "program.s"), str(directory / "adapted.c")]
            compile_result = run(argv, target, "compiler", env)
            if compile_result.returncode:
                raise ValueError(compile_result.stderr.decode())
            link = run(["gcc", "-no-pie", str(target / "program.s"), "-lm", "-o", str(target / "program")], target, "link")
            if link.returncode:
                raise ValueError(link.stderr.decode())
            output = run([str(target / "program")], target, "native")
            if output.returncode or output.stdout != expected:
                raise ValueError("Adapted CompCert program differs from original GCC observation")
            row["configurations"][mode] = {"argv": argv, "environment": old["environment"],
                                           "native_original_reference_match": True,
                                           "pipeline_files": [str(path.relative_to(target)) for path in (target / "phases").rglob("*") if path.is_file()]}
        baseline = directory / "disabled/adapted.light.c"
        for mode, result in row["configurations"].items():
            result["emitted_clight_equals_disabled"] = (directory / mode / "adapted.light.c").read_bytes() == baseline.read_bytes()
        rows.append(row)
        print(case, "same original modeled state; all three compilations/run modes pass", flush=True)
    bindings = {str(PARENT.relative_to(ROOT)): sha(PARENT), str(Path(__file__).relative_to(ROOT)): sha(Path(__file__))}
    for path in WORK.rglob("*"):
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "passed", "kind": "explicit-harness-constant-initializer-compatibility",
              "cases": rows, "native_configuration_comparisons": 6,
              "original_GCC_reference_unchanged": True, "source_types_and_loop_computation_preserved": True,
              "parser_boundary_adaptation_not_verified_Clight_optimization": True,
              "new_optimized_corpus_cases": 0, "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
