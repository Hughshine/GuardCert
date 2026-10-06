"""Run source-observed pointer envelopes through the proved full compiler."""
import argparse
import json
import os
import re
import subprocess
from pathlib import Path

import native_memory_affine_alias as common
import native_memory_address_parameters as proposals
from native_zero_trip import function_body
from native_interface_private_scan import sha

ROOT = common.ROOT
WORK = ROOT / "build/native-interface-observed-pointer"
COMPILER = ROOT / "build/compcert-observed-pointer/ccomp"
PROOF = ROOT / "build/interface-observed-pointer/report.json"
SOURCE = ROOT / "examples/native_interface_observed_pointer.c"
NAMES = ["observed_flat2", "observed_group2", "observed_conditional2", "observed_three3",
         "observed_missing2", "observed_clobber2", "observed_linear1"]
DIMENSIONS = [2, 2, 2, 3, 2, 2, 1]


def compile_run(source, directory, syntax, extra, reference, timeout):
    """Give this larger direct-tree compiler an explicit diagnostic budget."""
    directory.mkdir(parents=True, exist_ok=True)
    candidate = directory / "candidate.sexp"
    candidate.write_text(syntax+"\n")
    command = [str(COMPILER), "-conf", str(COMPILER.parent / "compcert.ini"),
               "-stdlib", str(COMPILER.parent / "runtime"), "-dclight", "-S",
               "-o", str(directory / "affine.s"), str(source)]
    try:
        result = subprocess.run(command, cwd=directory,
                                env=os.environ | {"GUARDCERT_LOOP_CANDIDATE": str(candidate)} | extra,
                                text=True, capture_output=True, check=True, timeout=timeout)
    except subprocess.TimeoutExpired as failure:
        (directory / "compile-timeout.json").write_text(json.dumps(
            {"status": "timeout", "command": command, "compile_timeout_seconds": timeout,
             "compiler_sha256": sha(COMPILER), "source_sha256": sha(source)}, indent=2)+"\n")
        raise failure
    (directory / "compiler-output.txt").write_text(result.stdout+result.stderr)
    subprocess.run(["gcc", str(directory / "affine.s"), "-o", str(directory / "affine")], check=True)
    actual = subprocess.check_output([str(directory / "affine")], text=True, timeout=120)
    assert actual == reference, directory
    (directory / "output.txt").write_text(actual)
    dump = directory / (source.stem+".light.c")
    return dump.read_text(), dump.stat().st_size, (directory / "affine.s").stat().st_size


def reuse_passed(report, stamp, name, syntax, extra, reference):
    """Re-execute bound binaries; a partial run never counts as a full suite."""
    assert report["compiler_sha256"] == stamp["compiler_sha256"]
    assert report["proof_report_sha256"] == sha(PROOF) and report["source_sha256"] == sha(SOURCE)
    assert sha(ROOT / report["verification_script_archive"]) == report["verification_script_sha256"]
    assert report["proposal_inputs"][name] == {"syntax": syntax, "environment": extra}
    evidence = report["configurations"][name]
    directory = WORK / name
    for filename, key in [("candidate.sexp", "proposal_sha256"), (SOURCE.stem+".light.c", "clight_sha256"),
                          ("affine.s", "assembly_sha256"), ("affine", "binary_sha256"), ("output.txt", "output_sha256")]:
        assert sha(directory / filename) == evidence[key], (name, filename)
    assert (directory / "candidate.sexp").read_text() == syntax+"\n"
    actual = subprocess.check_output([str(directory / "affine")], text=True, timeout=120)
    assert actual == reference == (directory / "output.txt").read_text(), name
    dump = directory / (SOURCE.stem+".light.c")
    return dump.read_text(), dump.stat().st_size, (directory / "affine.s").stat().st_size


def check_build():
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    proof = json.loads(PROOF.read_text())
    assert stamp["proved_entrypoint"] == "ClightObservedPointerCompiler.compile_preserving_observed_pointer"
    assert stamp["compiler_sha256"] == sha(COMPILER)
    assert stamp["proof_report_sha256"] == sha(PROOF)
    assert proof["status"] == "compiled" and proof["readonly_envelope_shortcut_installed_here"]
    assert proof["additional_global_axioms"] == []
    for filename, digest in (stamp["proof_sources"] | stamp["native_sources"]).items():
        assert sha(ROOT / filename) == digest, filename
    return stamp


def full_inputs():
    inputs = []
    for which, dimensions in enumerate(DIMENSIONS):
        counts = ([[0, 1, 1], [1, 1, 1], [2, 1, 1], [8, 1, 1], [32, 1, 1], [278, 1, 1], [279, 1, 1]]
                  if dimensions == 1 else
                  [[0, 2, 1], [2, 0, 1], [1, 1, 1], [2, 2, 1], [2, 3, 1], [7, 2, 1], [7, 3, 1], [65, 17, 1]]
                  if dimensions == 2 else
                  [[0, 2, 2], [2, 0, 2], [2, 2, 0], [1, 1, 1], [2, 2, 2], [5, 3, 2], [15, 9, 9]])
        for kind in range(6):
            inputs += [[which, kind, 0, n, m, s, 0] for n, m, s in counts]
        inputs += [[which, 0, 1, 3, 2, 2, 3]]
        inputs += [[which, 0, 0, 3, 2, 2, t] for t in [-17, 3, 63, 64, 65]]
        inputs += [[which, 0, 0, 0, 2, 2, -2147483648]]
    inputs += [[2, 6, 0, 0, 2, 1, -2147483648], [2, 6, 0, -2147483648, 2, 1, 2147483647],
               [2, 6, 0, 2, 0, 1, 2147483647]]
    return inputs


def calls_text():
    def literal(value):
        return "(-2147483647-1)" if value == -2147483648 else str(value)
    return "\n".join("  observed_run(" + ",".join(map(literal, args)) + ");" for args in full_inputs())


def model(args, interchange=False):
    which, kind, start, n, m, s, t = args
    arrays = [[3*x+1 for x in range(4096)], [5*x+7 for x in range(4096)]]
    p = (0, 256)
    q = (1, 256) if kind == 1 else (0, {0: 256, 2: 162, 3: 2056, 4: 257, 5: 160}.get(kind, 256))
    active = which != 2 or (n > 0 and m > 0)

    def read(pointer, offset):
        block, base = pointer
        assert 0 <= base+offset < 4096, (args, pointer, offset)
        return arrays[block][base+offset]

    def write(pointer, offset, value):
        block, base = pointer
        assert 0 <= base+offset < 4096, (args, pointer, offset)
        arrays[block][base+offset] = common.word(value)

    rp = read(p, 0) if active else 0
    rq = read(q, 0) if active and which != 4 else 0
    if which == 5:
        q = (q[0], q[1]+1)
    points = ([(i, j, k) for i in range(start, n) for j in (range(m) if DIMENSIONS[which] >= 2 else [0])
               for k in (range(s) if which == 3 else [0])] if active else [])
    if interchange:
        points.sort(key=lambda point: (point[1], point[0], point[2]))
    for i, j, k in points:
        address = 64*i+8*j+k+t if which == 3 else 16*i+j+t
        left = 32+2*i+t if which == 6 else 32+address
        right = 127+3*i+t if which == 6 else (256 if which == 3 else 127)+address
        write(p, left, read(q, right)+i+j+k+1)
    exits = [max(start, n) if active else start, 77, 91]
    if active and start < n and DIMENSIONS[which] >= 2:
        exits[1] = max(0, m)
        if which == 3 and m > 0:
            exits[2] = max(0, s)
    if active:
        write(p, 0, rp+17)
        write(q, 0, rq+19)
    context = common.word(31+sum(exits))
    values = args+exits+[rp, rq, context]+[value for pair in zip(*arrays) for value in pair]
    return " ".join(map(str, values))+"\n", arrays


def observed_functions(dump):
    found = {}
    for function in NAMES:
        body = function_body(dump, function)
        equality = re.search(r"\bif\s*\(\$p\s*==\s*\$q\)", body)
        scans = re.findall(r"\$(\d+) = 0;\s*for \(; 1; \(\{ break; \}\)\)", body)
        if not equality and not scans:
            continue
        if equality:
            before = body[:equality.start()]
            assert "$rp = *$p;" in before and "$rq = *$q;" in before, function
            assert re.search(r"\bif\s*\(0\s*<\s*\$n\)", before), function
            assert "$t" in before and "$p +" in body and "$q +" in body, function
        found[function] = {"readonly_envelope_shortcut": bool(equality), "original_scan_present": bool(scans),
                           "body_bytes": len(body.encode()), "scan_ast_copies": len(scans)}
    return found


def configurations():
    choices = [(name, syntax, {}) for name, syntax in proposals.templates().items()]
    choices += [("resource-limit", proposals.templates()["schedule-interchange-2"], {"GUARDCERT_FM_ROWS": "0"}),
                ("invalid-certificate", proposals.templates()["schedule-interchange-2"], {"GUARDCERT_ORACLE_FAULT": "top-certificate"}),
                ("missing-proposal", "", {"GUARDCERT_LOOP_CANDIDATE": str(WORK / "absent.sexp")}),
                ("malformed-proposal", "(", {})]
    priority = ["direct-interchange-2", "schedule-interchange-2"]
    return sorted(choices, key=lambda item: priority.index(item[0]) if item[0] in priority else len(priority))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cases")
    parser.add_argument("--compile-timeout", type=int, default=1800)
    parser.add_argument("--reuse-passed-report", type=Path,
                        help="re-execute bound passed artifacts from an explicitly archived earlier run")
    args = parser.parse_args()
    assert args.compile_timeout > 0
    stamp = check_build()
    reused = json.loads(args.reuse_passed_report.read_text()) if args.reuse_passed_report else None
    assert calls_text() in SOURCE.read_text(), "source calls do not match the model"
    expected = "".join(model(arguments)[0] for arguments in full_inputs())
    reference = common.checked_reference(SOURCE, WORK, expected)
    # This overlapping source really has a candidate order counterexample.
    counterexample = [0, 0, 0, 7, 3, 1, 0]
    assert model(counterexample)[0] != model(counterexample, interchange=True)[0]
    common.COMPILER = COMPILER
    choices = configurations()
    selected = set(args.cases.split(",")) if args.cases else {name for name, _, _ in choices}
    assert selected <= {name for name, _, _ in choices}
    results = {}
    for name, syntax, extra in choices:
        if name not in selected:
            continue
        directory = WORK / name
        reuse = reused is not None and name in reused["configurations"]
        if reuse:
            dump, clight_bytes, assembly_bytes = reuse_passed(reused, stamp, name, syntax, extra, reference)
        else:
            dump, clight_bytes, assembly_bytes = compile_run(SOURCE, directory, syntax, extra, reference, args.compile_timeout)
        found = observed_functions(dump)
        refused = bool(extra) or name in {"invalid-coordinate", "malformed-proposal"}
        if refused:
            assert not found, (name, found)
        else:
            dimensions = int(name[-1]) if name.startswith("direct") else 2
            expected_functions = {function for which, (function, dim) in enumerate(zip(NAMES, DIMENSIONS))
                                  if which not in [4, 5] and (dim >= 2 if name.startswith("tile") else dim == dimensions)}
            assert expected_functions <= set(found), (name, expected_functions, found)
            assert all(found[function]["readonly_envelope_shortcut"] and found[function]["original_scan_present"]
                       for function in expected_functions), (name, found)
            assert not any(found.get(function, {}).get("readonly_envelope_shortcut") for function in NAMES[4:6]), found
        results[name] = {"functions": found, "actual_calls": len(full_inputs()),
                         "compilation_origin": "bound-earlier-run-reexecuted" if reuse else "compiled-in-this-run",
                         "compilation_driver_sha256": reused["verification_script_sha256"] if reuse else sha(Path(__file__)),
                         "compile_timeout_seconds": None if reuse else args.compile_timeout,
                         "full_buffers_public_exits_prefix_values_and_context_match_model_and_gcc": True,
                         "clight_bytes": clight_bytes, "assembly_bytes": assembly_bytes,
                         "proposal_sha256": sha(directory / "candidate.sexp"),
                         "clight_sha256": sha(directory / (SOURCE.stem+".light.c")),
                         "assembly_sha256": sha(directory / "affine.s"), "binary_sha256": sha(directory / "affine"),
                         "output_sha256": sha(directory / "output.txt")}
        (WORK / "partial-report.json").write_text(json.dumps(results, indent=2)+"\n")
        print(name, {function: facts["readonly_envelope_shortcut"] for function, facts in found.items()}, flush=True)
    report = {"status": "passed", "compiler_sha256": stamp["compiler_sha256"], "proof_report_sha256": sha(PROOF),
              "source_sha256": sha(SOURCE), "verification_script_sha256": sha(Path(__file__)),
              "configurations": results, "full_configuration_suite": not bool(args.cases),
              "proposal_inputs": {name: {"syntax": syntax, "environment": extra}
                                  for name, syntax, extra in choices if name in selected},
              "reuse_report_sha256": sha(args.reuse_passed_report) if reused else None,
              "reuse_report_path": str(args.reuse_passed_report.relative_to(ROOT)) if reused else None,
              "unique_source_calls": len(full_inputs()), "calls_across_configurations": len(full_inputs())*len(results),
              "overlapping_candidate_counterexample_confirmed": counterexample, "performance_measured": False,
              "scope": "complete assembly outputs with original source reads, same-base separation, overlap, different bases, "
                       "uncovered or clobbered observations, empty/null branch, machine bounds and retained suffix effects"}
    (WORK / ("smoke-report.json" if args.cases else "report.json")).write_text(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
