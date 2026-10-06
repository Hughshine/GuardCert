"""Exercise private-scan installation in real enclosing Clight control flow."""
import itertools
import json
from pathlib import Path

import native_memory_affine_alias as common
from native_interface_private_scan import ROOT, WORK, COMPILER, PROOF, check_build, sha
from native_zero_trip import function_body

SOURCE = ROOT / "examples/native_interface_private_scan_context.c"
CONTEXT_WORK = WORK / "context"
NAMES = ["pointer_control", "pointer_two_regions", "pointer_outer_control", "pointer_empty_control"]


def inputs():
    cases = [[which, kind, route, 0 if counts == 0 else 2, 0 if counts == 1 else 3,
              0 if parameters else 3, 0 if parameters else 7]
             for which, kind, route, counts, parameters in
             itertools.product(range(4), range(3), range(3), range(3), range(2))]
    return cases + [[which, 3, 0, 0, 2, -2147483648, 2147483647] for which in range(4)] + [
        [0, 0, 0, 2, 3, -1, 0], [1, 0, 0, 2, 3, 64, 1]]


def output_model(arguments):
    which, kind, route, n, m, u, v = arguments
    a, b = [3*i+1 for i in range(1280)], [5*i+7 for i in range(1280)]
    source = b if kind == 0 else a
    source_base = 129 if kind == 2 else 128
    i, j = 0, 77
    mark = [10, 20+route, 30, 40+route][which]
    def loop(second=False):
        nonlocal i, j
        i = 0
        for row in range(n):
            i = row
            j = 0
            for column in range(m):
                assert kind != 3
                target = 128 + 16*row + column + u + (33 if second else 32)
                index = source_base + 16*row + column + v + (34 if second else 33)
                a[target] = common.word(source[index] + (-row+column if second else row-column))
                j = column+1
            i = row+1
    if which == 0:
        if route < 2:
            loop()
            mark += 1 if route == 0 else 2
        else:
            mark += 3
        if route != 1:
            mark += 4
    elif which == 1:
        loop(); mark += 5; loop(True)
    elif which == 2:
        for outer in [0, 2]:
            loop(); mark += 1
            if route:
                break
    else:
        loop()
    return " ".join(map(str, arguments+[i,j,mark]+[value for pair in zip(a,b) for value in pair]))+"\n"


def main():
    stamp = check_build()
    common.COMPILER = COMPILER
    cases = inputs()
    reference = common.checked_reference(SOURCE, CONTEXT_WORK, "".join(output_model(case) for case in cases))
    configurations = {}
    for name, syntax, extra in [
        ("interchange", "(schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0)))", {}),
        ("tile", "(tile 2 3)", {}),
        ("resource-limit", "(schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0)))", {"GUARDCERT_FM_ROWS":"0"})]:
        work = CONTEXT_WORK / name
        dump, clight_bytes, assembly_bytes = common.compile_run(SOURCE, work, syntax, extra, reference)
        # Count actual materialized dispatches, including two consecutive
        # source regions and branches beneath surrounding labels/control.
        import re
        sites = {function: len(re.findall(r"\$(\d+) = 0;\s*for \(; 1; \(\{ break; \}\)\)",
                           function_body(dump, function))) for function in NAMES}
        assert sites == ({function:0 for function in NAMES} if extra else dict(zip(NAMES,[2,2,1,1]))), (name, sites)
        configurations[name] = {"guard_sites": sites, "actual_calls": len(cases),
            "full_arrays_public_exits_and_context_effects_match_model_and_gcc": True,
            "clight_bytes": clight_bytes, "assembly_bytes": assembly_bytes,
            "proposal_sha256": sha(work/"candidate.sexp"), "clight_sha256": sha(work/(SOURCE.stem+".light.c")),
            "assembly_sha256": sha(work/"affine.s"), "output_sha256": sha(work/"output.txt")}
        print(name,sites,flush=True)
    report = {"status":"passed", "compiler_sha256":stamp["compiler_sha256"], "proof_report_sha256":sha(PROOF),
        "source_sha256":sha(SOURCE), "verification_script_sha256":sha(Path(__file__)),
        "unique_source_calls":len(cases), "calls_across_configurations":len(cases)*len(configurations),
        "configurations":configurations, "scope":"complete assembly execution; enclosing switch/goto/return, "
            "outer continue/break, consecutive regions, global effects, alias refusal and empty undefined/null inputs"}
    (CONTEXT_WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")


if __name__ == "__main__":
    main()
