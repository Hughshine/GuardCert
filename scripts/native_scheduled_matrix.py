"""Run every finite matrix order through the extracted, proposal-checking compiler."""
from pathlib import Path
import hashlib
import itertools
import json
import os
import re
import subprocess

from native_zero_trip import function_body

ROOT = Path(__file__).resolve().parents[1]
COMPILER = ROOT / "build" / "compcert-scheduled" / "ccomp"
SOURCE = ROOT / "examples" / "native_matrix_interchange.c"
WORK = ROOT / "build" / "native-scheduled-matrix"
VALUES = {0: 1, 1: 2, 2: 11, 3: 12}
SELECTED = ["matrix_dynamic", "matrix_goto", "matrix_global", "matrix_context", "matrix_unread_bound"]
REFUSED_BODIES = ["matrix_different_value", "matrix_dependent_value", "matrix_volatile"]


def run(*args, env=None, check=True):
    return subprocess.run([str(x) for x in args], cwd=WORK, env=env, check=check,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def direct_points(body):
    # Initializers write zero. Candidate stores use the distinct positive
    # payloads of the source points; source-loop fallbacks use variable indices.
    return [(int(index), int(value)) for index, value in
            re.findall(r"\*\((?:a|global_matrix) \+ (\d+)\) = (\d+);", body)
            if int(index) in VALUES and int(value) == VALUES[int(index)]]


def expected_output():
    inputs = [(0, 2, 2), (0, 1, 2), (0, 2, 1), (0, 0, 2), (1, 2, 2),
              (3, 2, 2), (0, 2, 0), (2**31-1, 2**31-1, -2**31),
              (-2**31, -2**31, 2**31-1)]
    result = ""
    for start, n, m in inputs:
        cells, j = [0, 0, 0, 0], 99
        for i in range(start, n):
            j = 0
            for inner in range(m):
                cells[i * 2 + inner] = i * 10 + inner + 1
                j = inner + 1
        result += f"matrix {sum(cells)} {max(start, n)} {j}\n"
    return result + "contexts 228 26 228\nfallbacks 105 12 105\nunread 99 99 99\nrefused 396 29 26\n"


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if (stamp["proved_entrypoint"] != "ScheduledRegionCompiler.compile_scheduled_regions"
            or stamp["schedule_proposal_input"] != "GUARDCERT_POINT_ORDER"
            or stamp["compiler_sha256"] != hashlib.sha256(COMPILER.read_bytes()).hexdigest()):
        raise SystemExit("unexpected or stale scheduling compiler")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    reference = run(WORK / "gcc-reference").stdout
    if reference != expected_output():
        raise SystemExit("GCC reference differs from independent matrix expectations")
    orders = list(itertools.permutations(range(4)))
    invalid = [[], [0, 1, 2], [0, 1, 1, 3], [0, 1, 2, 4],
               [0, 1, 2, 3, 4], [0, 0, 1, 2, 3], [9, 8, 7, 6]]
    results = []
    common = [COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib",
              COMPILER.parent / "runtime", "-dclight", "-S"]
    for case, (order, accepted) in enumerate([(o, True) for o in orders] + [(o, False) for o in invalid]):
        env = dict(os.environ, GUARDCERT_POINT_ORDER=",".join(map(str, order)))
        assembly = WORK / f"schedule-{case:02d}.s"
        executable = WORK / f"schedule-{case:02d}"
        run(*common, "-o", assembly, SOURCE, env=env)
        run("gcc", assembly, "-o", executable)
        output = run(executable).stdout
        if output != reference:
            raise SystemExit(f"schedule {order} behavior differs from reference\n{output}")
        dump = (WORK / (SOURCE.stem + ".light.c")).read_text()
        assembly.with_suffix(".light.c").write_text(dump)
        for name in SELECTED:
            body = function_body(dump, name)
            points = direct_points(body)
            expected = [(index, VALUES[index]) for index in order] if accepted else []
            if points != expected:
                raise SystemExit(f"proposal {order} did not produce its certified points in {name}: {points}")
            if accepted:
                checks = all(re.search(rf"if \(\${id} == {value}(?:U)?\)", body)
                             for id, value in [("i", 0), ("n", 2), ("m", 2)])
                if not checks or not re.search(r"\$j = 2;\s*\$i = 2;", body):
                    raise SystemExit(f"missing dynamic guard or exact exit restoration in {name}")
            if not re.search(r"for \(; 1; \$i = \$i \+ 1\).*?for \(; 1; \$j = \$j \+ 1\)", body, re.S):
                raise SystemExit(f"missing original-loop fallback in {name}")
            if accepted and len(re.findall(r"for \(; 1; \$i = \$i \+ 1\)", body)) != 1:
                raise SystemExit(f"fallback was duplicated in {name}")
        for name in REFUSED_BODIES:
            if direct_points(function_body(dump, name)):
                raise SystemExit(f"unsupported body accepted by schedule {order}: {name}")
        symbols = run("nm", "-S", "--defined-only", executable).stdout
        sizes = {name: int(size, 16) for _, size, _, name in
                 re.findall(r"^([0-9a-fA-F]+) ([0-9a-fA-F]+) (\w) (\w+)$", symbols, re.M)
                 if name in SELECTED}
        if set(sizes) != set(SELECTED):
            raise SystemExit(f"cannot record actual matrix function sizes: {sizes}")
        results.append({"order": list(order), "accepted": accepted,
                        "assembly_sha256": hashlib.sha256(assembly.read_bytes()).hexdigest(),
                        "function_bytes": sizes,
                        "output_sha256": hashlib.sha256(output.encode()).hexdigest()})
    for proposal in ["-1,0,1,2", "1025,0,1,2", "garbage", ",".join(["0"] * 65)]:
        env = dict(os.environ, GUARDCERT_POINT_ORDER=proposal)
        if run(*common, "-o", WORK / "bad-parser.s", SOURCE, env=env, check=False).returncode == 0:
            raise SystemExit(f"invalid proposal parser input accepted: {proposal}")
    (WORK / "output.txt").write_text(reference)
    (WORK / "report.json").write_text(json.dumps({
        "proved_entrypoint": stamp["proved_entrypoint"], "compiler_sha256": stamp["compiler_sha256"],
        "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        "valid_orders_checked": len(orders), "invalid_orders_checked": len(invalid), "cases": results,
        "actual_clight_proposed_store_order_checked": SELECTED,
        "exact_loop_exit_restoration_checked": True, "runtime_acceptance_and_fallback_checked": True,
        "single_original_loop_fallback_checked": True,
        "gcc_and_independent_behavior_matches": True, "proposal_parser_refusals_checked": 4,
        "unread_inner_bound_goto_enclosing_loop_and_global_array_checked": True,
        "unsupported_bodies_refused": REFUSED_BODIES,
        "scope": "exact 2x2 source; finite scheduling and full unrolling; dimension guard",
        "function_size_comparison_baseline": "refused proposals retain zero-trip rewriting; not a stock compiler",
        "polopt_called": False, "performance_measured": False,
    }, indent=2) + "\n")
    print(f"Native proposed schedules passed: {len(orders)} permutations, {len(invalid)} refused proposals, "
          f"{len(SELECTED)} program contexts and exact exits")


if __name__ == "__main__":
    main()
