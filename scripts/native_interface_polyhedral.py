"""Run real affine/tiling proposals through both readonly guard realizations."""
import json
import os
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_memory_multiarray import SOURCE, ACCEPTED, REFUSED, expected_output
from native_zero_trip import function_body

WORK = ROOT / "build/interface-polyhedral-native"
COMPILER = ROOT / "build/compcert-readonly-polyhedral/ccomp"
ENTRY = "ClightPolyhedralCompiler.compile_preserving_polyhedral"
MODEL_SOURCE = ROOT / "scripts/native_memory_multiarray.py"


def run(*args, cwd=WORK, environment=None, timeout=300):
    return subprocess.run([str(arg) for arg in args], cwd=cwd, check=True, text=True,
                          capture_output=True, timeout=timeout, env=environment)


def compile_run(mode, name, path, extra, expected, reference):
    work = WORK / mode / name
    work.mkdir(parents=True, exist_ok=True)
    environment = os.environ.copy()
    # Each run has a controlled proposal and oracle configuration.
    for variable in ["GUARDCERT_LOOP_CANDIDATE", "GUARDCERT_GUARD_LOWERING",
                     "GUARDCERT_FM_ROWS", "GUARDCERT_ORACLE_FAULT"]:
        environment.pop(variable, None)
    environment.update({"GUARDCERT_GUARD_LOWERING": mode, "GUARDCERT_LOOP_CANDIDATE": str(path), **extra})
    assembly = work / "multiarray.s"
    compiled = run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib",
                   COMPILER.parent / "runtime", "-dclight", "-S", "-o", assembly,
                   SOURCE, cwd=work, environment=environment)
    (work / "compiler-output.txt").write_text(compiled.stdout + compiled.stderr)
    run("gcc", assembly, "-o", work / "multiarray", cwd=work)
    actual = run(work / "multiarray", cwd=work).stdout
    (work / "output.txt").write_text(actual)
    if actual != reference or actual != expected_output():
        raise SystemExit(f"candidate/fallback differs from GCC or source model: {mode}/{name}")
    dumps = list(work.glob("*.light.c"))
    if len(dumps) != 1:
        raise SystemExit(f"unexpected Clight dumps: {mode}/{name}: {dumps}")
    dump = dumps[0].read_text()
    branch_counts = {}
    for function in ACCEPTED | REFUSED:
        body = function_body(dump, function)
        chosen = "$i = $n;" in body and "$j = $m;" in body
        if chosen != (function in expected):
            raise SystemExit(f"wrong actual candidate selection: {mode}/{name}/{function}\n{body}")
        if not chosen:
            continue
        if not re.search(r"if \([^\n]* != [^\n]*\)", body):
            raise SystemExit(f"actual safe array-base comparison missing: {mode}/{name}/{function}")
        if "switch (0)" in body:
            raise SystemExit("the legacy switch-based lowering was used instead of the common realization")
        exits = body.count("$i = $n;")
        boolean_writes = re.findall(r"(\$[\w]+) = ([01]);", body)
        if mode == "shared":
            result_variables = {identifier for identifier, _ in boolean_writes if identifier not in ["$i", "$j", "$k", "$r"]}
            if not any(re.search(r"if \(" + re.escape(identifier) + r"\)", body) for identifier in result_variables):
                raise SystemExit(f"shared private Boolean dispatch missing: {name}/{function}")
            if exits != 1:
                raise SystemExit(f"shared realization duplicates its candidate: {name}/{function}")
        branch_counts[function] = {"candidate_exit_copies": exits, "clight_body_bytes": len(body.encode())}
    return {
        "guarded_functions": sorted(expected), "full_output_lines": len(actual.splitlines()),
        "assembly_sha256": sha(assembly), "clight_sha256": sha(dumps[0]),
        "proposal_sha256": sha(path) if path.exists() else None,
        "extra_configuration": extra, "branch_counts": branch_counts,
        "output_sha256": sha(work / "output.txt"), "gcc_and_independent_model_match": True,
    }


def main():
    stamp_path = COMPILER.parent / ".guard-build.json"
    stamp = json.loads(stamp_path.read_text())
    if stamp["proved_entrypoint"] != ENTRY or sha(COMPILER) != stamp["compiler_sha256"]:
        raise SystemExit("unexpected or changed extracted compiler")
    report_path = ROOT / "build/interface-polyhedral/report.json"
    if sha(report_path) != stamp["proof_report_sha256"]:
        raise SystemExit("compiler is bound to an earlier proof audit")
    for path, digest in (stamp["proof_sources"] | stamp["native_sources"]).items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"compiler input changed: {path}")
    WORK.mkdir(parents=True, exist_ok=True)
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    reference = run(WORK / "gcc-reference").stdout
    if reference != expected_output():
        raise SystemExit("source model differs from GCC")
    (WORK / "gcc-output.txt").write_text(reference)
    templates = ROOT / "examples/loop-candidates"
    cases = [(name, templates / (name + ".sexp"), {},
              ACCEPTED - {"multi_three"} if name in ["fission", "reverse-inner"] else ACCEPTED)
             for name in ["identity", "interchange", "fission", "shift", "skew-inner", "shift-interchange", "reverse-inner"]]
    for rows, columns in [(1, 1), (2, 3), (17, 13)]:
        name = f"tile-{rows}-{columns}"
        path = WORK / (name + ".sexp")
        path.write_text(f"(tile {rows} {columns})\n")
        cases.append((name, path, {}, ACCEPTED))
    cases.extend((name, templates / (name + ".sexp"), {}, set())
                 for name in ["wrong-arguments", "changed-domain", "drop-all-statements",
                              "reverse-dependent", "wrong-shift", "shift-overflow", "missing-proposal"])
    malformed = WORK / "malformed.sexp"
    malformed.write_text("(map-index ((swap 0)) unclosed\n")
    cases.append(("malformed", malformed, {}, set()))
    for name, extra in [("resource-limit", {"GUARDCERT_FM_ROWS": "0"}),
                        ("invalid-certificate", {"GUARDCERT_ORACLE_FAULT": "top-certificate"})]:
        cases.append((name, templates / "fission.sexp", extra, set()))
    configurations = {}
    for mode in ["direct", "shared"]:
        for name, path, extra, expected in cases:
            configurations[mode + "/" + name] = compile_run(mode, name, path, extra, expected, reference)
            print(f"Passed {mode}/{name}: {len(expected)} guarded functions", flush=True)
    report = {
        "status": "passed", "proved_entrypoint": ENTRY, "compiler_sha256": stamp["compiler_sha256"],
        "compiler_stamp_sha256": sha(stamp_path), "proof_report_sha256": sha(report_path),
        "source_sha256": sha(SOURCE), "independent_model_source_sha256": sha(MODEL_SOURCE),
        "configurations": configurations, "guard_realizations": ["direct", "shared"],
        "actual_multiple_arrays_and_array_reads": True, "actual_candidate_checker_consumed": True,
        "real_affine_shift_skew_composition_and_tiling": True,
        "unsafe_domain_argument_dependence_machine_overflow_refused": True,
        "zero_negative_bounds_and_nonzero_start_source_fallback_executed": True,
        "global_and_enclosing_contexts_checked": True, "all_arrays_and_public_counters_checked": True,
        "shared_one_candidate_and_one_source_fallback": True,
        "legacy_switch_lowering_used": False, "performance_measured": False,
        "general_pointer_alias_source_migrated": False, "general_affine_source_migrated": False,
    }
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Readonly polyhedral user passed: {len(configurations)} configurations, "
          f"{len(reference.splitlines())} output lines each")


if __name__ == "__main__":
    main()
