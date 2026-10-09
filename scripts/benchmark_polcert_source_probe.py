"""Compile the pinned PolCert C harnesses without changing data or control types."""

import argparse
import dataclasses
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
PINNED = ROOT / "build/benchmark-alignment/polcert-pinned"
COMPILER = ROOT / "build/affine-empty-runtime/compiler-v1/ccomp"
ENTRY = "ClightSelectedEmptyRuntimeCompiler.compile_selected_empty_runtime_regions"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command, directory, label, env=None, timeout=90):
    start = time.monotonic()
    try:
        proc = subprocess.run(command, cwd=directory, env=env, capture_output=True, timeout=timeout)
        status = {"returncode": proc.returncode, "timeout": False}
        output, errors = proc.stdout, proc.stderr
    except subprocess.TimeoutExpired as failure:
        status = {"returncode": None, "timeout": True}
        output, errors = failure.stdout or b"", failure.stderr or b""
    for suffix, data in [("stdout", output), ("stderr", errors)]:
        with (directory / f"{label}.{suffix}").open("xb") as out:
            out.write(data)
    status.update(argv=command, elapsed_seconds=time.monotonic() - start)
    return status, output, errors


def source_bindings():
    tree = json.loads((ROOT / "build/benchmark-alignment/source-pins/polcert-tree.json").read_text())
    if tree["sha"] != "ca1ae3199c816594bab9d51eb77309a0d17527aa" or tree.get("truncated"):
        raise ValueError("Wrong or incomplete upstream source tree")
    blobs = {item["path"]: item["sha"] for item in tree["tree"] if item["type"] == "blob"}
    bindings = {}
    for path in PINNED.rglob("*"):
        if not path.is_file() or "__pycache__" in path.parts:
            continue
        relative = path.relative_to(PINNED).as_posix()
        data = path.read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if blobs.get(relative) != blob:
            raise ValueError(f"Changed pinned source: {relative}")
        bindings[str(path.relative_to(ROOT))] = sha(path)
    build = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if sha(COMPILER) != build["compiler_sha256"] or build["proved_entrypoint"] != ENTRY:
        raise ValueError("Compiler differs from its frozen extracted checkpoint")
    proof = ROOT / "build/affine-empty-runtime/proof-v1/report.json"
    if sha(proof) != build["proof_report_sha256"]:
        raise ValueError("Compiler proof checkpoint differs")
    for path in [COMPILER, COMPILER.parent / ".guard-build.json", proof,
                 ROOT / "toolchain.lock.json", Path(__file__),
                 ROOT / "docs/benchmark-alignment-inventory.json"]:
        bindings[str(path.relative_to(ROOT))] = sha(path)
    return bindings


def probe_case(case, modes, work, generator, tiers, pluto):
    directory = work / case
    directory.mkdir()
    loop = (PINNED / f"tests/polopt-generated/inputs/{case}.loop").read_text()
    info = generator.build_harness(case, loop, loop, tier="smoke", tier_overrides=tiers)
    original = generator.render_program_source(info, optimized=False, state_digest_output=True)
    kernel = info.baseline_kernel.rstrip()
    if original.count(kernel) != 1:
        raise ValueError(f"Cannot identify original kernel occurrence: {case}")
    marked = original.replace(kernel, "#pragma scop\n" + kernel + "\n#pragma endscop", 1)
    (directory / "original.c").write_text(original)
    (directory / "marked.c").write_text(marked)
    result = {
        "case": case, "harness_parameters": info.params, "harness_tier": "smoke",
        "array_shapes": {name: [dataclasses.asdict(dim) for dim in shape] for name, shape in info.arrays.items()},
        "scalar_names": list(info.scalars), "helper_functions": list(info.functions),
        "kernel_long_long_loop_variables": re.findall(r"for \(long long (\w+)", kernel),
        "source_adaptation": "paired scop annotations only; upstream baseline harness and numeric types retained",
        "data_declarations": "upstream double arrays/scalars",
        "native_observation": "upstream digest of every modeled scalar and array cell; not a universal equivalence proof",
        "configurations": {},
    }
    gcc, _, _ = run(["gcc", "-O0", "-ffp-contract=off", str(directory / "original.c"),
                     "-lm", "-o", str(directory / "reference")], directory, "reference-build")
    result["reference_build"] = gcc
    reference = None
    if gcc["returncode"] == 0:
        execute, reference, _ = run([str(directory / "reference")], directory, "reference-run", timeout=90)
        result["reference_execution"] = execute
        if execute["returncode"] != 0:
            reference = None
    for mode in modes:
        target = directory / mode
        target.mkdir()
        env = {key: value for key, value in os.environ.items() if not key.startswith("GUARDCERT_")}
        env.update(GUARDCERT_TENSOR_MODE="disabled" if mode == "disabled" else "pipeline",
                   GUARDCERT_POLYHEDRAL_MODE="schedule" if mode == "disabled" else mode,
                   GUARDCERT_PLUTO=str(pluto), GUARDCERT_PIPELINE_DUMP=str(target / "phases"),
                   GUARDCERT_SCOP_DIAGNOSTICS="1", GUARDCERT_PIPELINE_CHECK_DIAGNOSTICS="1",
                   GUARDCERT_TENSOR_DIAGNOSTICS="1")
        command = [str(COMPILER), "-fall", "-stdlib", str(COMPILER.parent / "runtime"),
                   "-dparse", "-dclight", "-S", "-o", str(target / "program.s"), str(directory / "marked.c")]
        compile_result, stdout, stderr = run(command, target, "compiler", env=env)
        row = {"compile": compile_result,
               "environment": {key: value for key, value in env.items() if key.startswith("GUARDCERT_")},
               "source_selection_trace": re.findall(r"^GUARDCERT_SCOP .*", (stdout + stderr).decode(errors="replace"), re.M)}
        result["configurations"][mode] = row
        # CompCert writes dumps beside the source, so archive them per mode before the next invocation.
        for suffix in ["light.c", "parsed.c"]:
            source_dump = directory / f"marked.{suffix}"
            if source_dump.exists():
                source_dump.rename(target / f"program.{suffix}")
        row["phase_artifacts"] = [str(path.relative_to(target)) for path in sorted((target / "phases").rglob("*")) if path.is_file()]
        if compile_result["returncode"] != 0:
            row["status"] = "compile_failed"
            continue
        link, _, _ = run(["gcc", "-no-pie", str(target / "program.s"), "-lm", "-o", str(target / "program")], target, "link")
        row["link"] = link
        if link["returncode"] != 0:
            row["status"] = "link_failed"
            continue
        execute, output, _ = run([str(target / "program")], target, "native", timeout=90)
        row["execution"] = execute
        row["modeled_state_digest_matches_reference"] = reference is not None and execute["returncode"] == 0 and output == reference
        row["status"] = "native_match" if row["modeled_state_digest_matches_reference"] else "native_failed_or_mismatch"
    baseline = directory / "disabled/program.light.c"
    for mode, row in result["configurations"].items():
        dump = directory / mode / "program.light.c"
        row["emitted_clight_equals_disabled"] = dump.exists() and baseline.exists() and dump.read_bytes() == baseline.read_bytes()
        row["requested_optimization_demonstrated"] = False
        if mode != "disabled" and row["emitted_clight_equals_disabled"] and not row["phase_artifacts"]:
            row["optimization_status"] = "unchanged_clight_no_pipeline_call"
        elif mode != "disabled":
            row["optimization_status"] = "requires_phase_and_installation_analysis"
        else:
            row["optimization_status"] = "disabled_control"
    (directory / "case-report.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, default=ROOT / "build/benchmark-alignment/probe-v1")
    parser.add_argument("--cases", nargs="+")
    parser.add_argument("--modes", nargs="+", choices=["disabled", "schedule", "tile"], default=["disabled", "schedule", "tile"])
    args = parser.parse_args()
    work = args.work.resolve()
    if not work.is_relative_to(ROOT / "build/benchmark-alignment") or work.exists():
        raise ValueError("Use a new benchmark-alignment checkpoint directory")
    bindings = source_bindings()
    inventory = json.loads((ROOT / "docs/benchmark-alignment-inventory.json").read_text())
    names = {row["case"] for row in inventory["polcert"]["cases"]}
    cases = args.cases or sorted(names)
    if len(cases) != len(set(cases)) or not set(cases) <= names:
        raise ValueError("Case selection does not match the fixed corpus")
    pluto_report = ROOT / "build/polyhedral-pipeline/pluto-build.json"
    scheduler = json.loads(pluto_report.read_text())
    pluto = ROOT / scheduler["binary"]
    if sha(pluto) != scheduler["bindings"][scheduler["binary"]]:
        raise ValueError("Scheduler checkpoint changed")
    bindings[str(pluto.relative_to(ROOT))] = sha(pluto)
    bindings[str(pluto_report.relative_to(ROOT))] = sha(pluto_report)
    sys.path.insert(0, str(PINNED / "tools/end_to_end_c"))
    import generated_harness as generator
    tiers = generator.load_param_tiers(PINNED / "tests/end-to-end-generated/param_tiers.json")
    work.mkdir()
    results = []
    for case in cases:
        result = probe_case(case, args.modes, work, generator, tiers, pluto)
        results.append(result)
        print(json.dumps({"case": case, "modes": {mode: row["status"] for mode, row in result["configurations"].items()},
                          "optimization": {mode: row["optimization_status"] for mode, row in result["configurations"].items()}}), flush=True)
    summary = {
        "status": "diagnostic_complete", "proved_compiler_entrypoint": ENTRY,
        "source_revision": inventory["polcert"]["revision"], "corpus_cases": len(names),
        "attempted_cases": len(results), "complete_case_list_attempted": set(cases) == names,
        "modes": args.modes, "results": results,
        "successful_native_configuration_comparisons": sum(row["status"] == "native_match" for result in results for row in result["configurations"].values()),
        "demonstrated_requested_optimizations": 0,
        "global_theorem_reused": "frozen selected compiler; safe refusal is not optimized case support",
        "performance_acceptance_measured": False,
        "single_run_durations_are_diagnostics_not_benchmark_cost_results": True,
        "bindings": bindings,
    }
    for path in work.rglob("*"):
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    (work / "report.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({key: value for key, value in summary.items() if key not in ["results", "bindings"]}), flush=True)


if __name__ == "__main__":
    main()
