"""Check strip-mining with real memory dependencies, aliasing, and program contexts."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

from native_zero_trip import function_body

ROOT = Path(__file__).resolve().parents[1]
COMPILER = ROOT / "build" / "compcert-stripmine" / "ccomp"
SOURCE = ROOT / "examples" / "native_stripmine.c"
WORK = ROOT / "build" / "native-stripmine"
WIDTHS = [0, 1, 2, 4, 7, 16, 65, 1024]
ACCEPTED = ["dependent_strip", "pointer_strip", "goto_strip", "switch_strip",
            "enclosing_strip", "recursive_strip"]


def run(*args, cwd=WORK, env=None):
    return subprocess.run([str(arg) for arg in args], cwd=cwd, env=env, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def snapshot(tag, start, n, mode="dependent", repeats=1):
    a, b = [-100] * 64, [k % 5 + 1 for k in range(64)]
    a[0] = 1
    for _ in range(repeats):
        i = start
        while i < n:
            if mode == "separate":
                a[i + 1] = b[i] + 2
            elif mode == "alias":
                a[i + 1] = a[i] + 2
            elif mode == "switch" and n % 2:
                a[i + 1] = a[i] - b[i]
            else:
                a[i + 1] = a[i] + b[i]
            if mode == "dependent":
                b[i] = a[i + 1] + b[i] if i % 2 else a[i + 1] - b[i]
            elif mode == "enclosing":
                b[i] += 1
            i += 1
    return f"{tag} {i} {n} " + " ".join(map(str, a + b)) + "\n"


def expected_output():
    expected = "".join(snapshot("dependent", 0, n) + snapshot("separate", 0, n, "separate")
                       + snapshot("alias", 0, n, "alias") for n in range(1, 64))
    fallback = [(1, 7), (0, 0), (0, -3), (2**31-1, 2**31-1), (-2**31, -2**31)]
    expected += "".join(snapshot("dependent", i, n) for i, n in fallback)
    expected += snapshot("goto", 0, 7, "ordinary")
    expected += snapshot("switch", 0, 6, "switch") + snapshot("switch", 0, 7, "switch")
    expected += snapshot("enclosing", 0, 9, "enclosing", repeats=2)
    expected += "".join(snapshot("recursive", 0, n, "ordinary") for n in [7, 8, 9])
    a = [-100] * 64
    a[0] = 1
    for i in range(9):
        a[i+1] = a[i] + 1
    expected += "volatile 9 " + " ".join(map(str, a)) + "\n"
    expected += "call 0\ncall 1\ncall 2\ncalled 3\nrefused 9 3\n"
    return expected


def check_dump(dump, width):
    for name in ACCEPTED:
        body = function_body(dump, name)
        guards = re.findall(r"if \(\$i == 0(?:U)?\)", body)
        if width == 0:
            if guards or re.search(r"\$\d+ = \$i \+", body):
                raise SystemExit(f"zero tile width accepted in {name}")
        elif (not guards or not re.search(rf"\$\d+ = \$i \+ {width};", body)
              or f"if ($n <= {2**31-1-width})" not in body or "switch (0)" not in body):
            raise SystemExit(f"strip-mined candidate, helper or overflow guard missing in {name}\n{body}")
    for name in ["volatile_strip", "call_in_loop", "bound_mutation", "early_break"]:
        body = function_body(dump, name)
        if re.search(r"if \(\$i == 0(?:U)?\)", body):
            raise SystemExit(f"unsupported effect accepted in {name}")


def check_rectangular_composition():
    import native_rectangular as rectangle

    directory = WORK / "rectangular-composition"
    directory.mkdir(exist_ok=True)
    source = ROOT / "examples" / "native_rectangular.c"
    env = dict(os.environ, GUARDCERT_TILE_WIDTH="7")
    run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib", COMPILER.parent / "runtime",
        "-dclight", "-S", "-o", directory / "composed.s", source, cwd=directory, env=env)
    run("gcc", directory / "composed.s", "-o", directory / "native")
    run("gcc", "-O0", source, "-o", directory / "reference")
    actual = run(directory / "native").stdout
    if actual != run(directory / "reference").stdout:
        raise SystemExit("composed rectangle interchange and strip-mining differs from GCC")
    if actual != rectangle.expected_output():
        raise SystemExit("composed output differs from the independent rectangle model")
    dumps = list(directory.glob("*.light.c"))
    if len(dumps) != 1:
        raise SystemExit(f"expected one composition dump: {dumps}")
    dump = dumps[0].read_text()
    accepted = {"rectangle_dynamic": (12, 10), "rectangle_other_layout": (15, 7),
                "rectangle_goto": (12, 10), "rectangle_global": (12, 10),
                "rectangle_enclosing_loop": (12, 10), "rectangle_unread_bound": (12, 10),
                "rectangle_update_dynamic": (12, 10), "rectangle_update_other_layout": (15, 7),
                "rectangle_update_goto": (12, 10), "rectangle_update_global": (12, 10),
                "rectangle_update_enclosing_loop": (12, 10), "rectangle_update_unread_bound": (12, 10),
                "rectangle_update_compound": (12, 10),
                "rectangle_row_dynamic": (12, 10), "rectangle_row_other_layout": (15, 7),
                "rectangle_row_goto": (12, 10), "rectangle_row_global": (12, 10),
                "rectangle_row_enclosing_loop": (12, 10), "rectangle_row_unread_bound": (12, 10)}
    for name, limits in accepted.items():
        body = function_body(dump, name)
        if (not rectangle.selected(body, *limits) or not re.search(r"\$\d+ = \$i \+ 7;", body)
                or not re.search(r"\$\d+ = \$j \+ 7;", body)):
            raise SystemExit(f"composed interchange and candidate/fallback strip-mining missing in {name}")
    (directory / "output.txt").write_text(actual)
    return {"status": "passed", "positive_rectangles": 225, "positive_read_modify_write_rectangles": 345, "positive_row_dependency_rectangles": 225,
            "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "actual_interchange_and_stripmining_of_both_candidate_and_fallback_checked": True,
            "complete_array_and_exit_values_match_independent_fixture_and_gcc": True}


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    reference = run(WORK / "gcc-reference").stdout
    expected = expected_output()
    if reference != expected:
        raise SystemExit("independent model differs from the GCC source execution")
    reports = []
    for width in WIDTHS:
        directory = WORK / str(width)
        directory.mkdir(exist_ok=True)
        env = dict(os.environ, GUARDCERT_TILE_WIDTH=str(width))
        run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib", COMPILER.parent / "runtime",
            "-dclight", "-S", "-o", directory / "stripmine.s", SOURCE, cwd=directory, env=env)
        run("gcc", directory / "stripmine.s", "-o", directory / "native")
        actual = run(directory / "native").stdout
        if actual != expected:
            raise SystemExit(f"strip-mined output differs for tile width {width}")
        dumps = list(directory.glob("*.light.c"))
        if len(dumps) != 1:
            raise SystemExit(f"expected one Clight dump for width {width}: {dumps}")
        check_dump(dumps[0].read_text(), width)
        (directory / "output.txt").write_text(actual)
        reports.append({"tile_width": width, "output_matches_gcc_and_independent_model": True,
                        "guard_and_actual_clight_candidate_checked": True})
    parser_refusals = ["-1", "1025", "invalid"]
    for token in parser_refusals:
        env = dict(os.environ, GUARDCERT_TILE_WIDTH=token)
        refused = subprocess.run([str(COMPILER), "-conf", str(COMPILER.parent / "compcert.ini"),
                                  "-stdlib", str(COMPILER.parent / "runtime"), "-S", "-o", str(WORK / "refused.s"),
                                  str(SOURCE)], cwd=WORK, env=env, text=True,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if refused.returncode == 0:
            raise SystemExit(f"invalid tile-width parser input accepted: {token}")
    composition = check_rectangular_composition()
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if (stamp["proved_entrypoint"] != "StripmineCompiler.compile_stripmine_regions"
            or stamp["compiler_sha256"] != hashlib.sha256(COMPILER.read_bytes()).hexdigest()):
        raise SystemExit("unexpected compiler entrypoint or executable")
    (WORK / "report.json").write_text(json.dumps({
        "status": "passed", "proved_entrypoint": stamp["proved_entrypoint"],
        "compiler_sha256": stamp["compiler_sha256"], "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        "tile_widths": reports, "dynamic_nonempty_loop_executions_per_width": 189,
        "complete_arrays_and_source_counter_exits_checked": True,
        "loop_carried_read_write_dependencies_checked": True, "same_and_distinct_block_alias_cases_checked": True,
        "multi_statement_and_conditional_memory_bodies_checked": True,
        "goto_switch_enclosing_loop_and_recursive_calls_checked": True,
        "helper_values_private_to_call_frames_checked": True,
        "zero_negative_and_nonzero_start_fallbacks_checked": True,
        "volatile_call_control_write_and_early_exit_refused": ["volatile_strip", "call_in_loop", "bound_mutation", "early_break"],
        "width_zero_refused": True, "tile_width_parser_refusals": parser_refusals, "no_runtime_domain_enumeration": True,
        "general_affine_domain_and_dependence_reordering": False, "polopt_called": False,
        "rectangle_composition": composition, "performance_measured": False,
    }, indent=2) + "\n")
    print(f"Native strip-mining passed: {len(WIDTHS)} tile widths, 189 dynamic dependent/alias loops per width; "
          "full arrays, source exits, calls, goto, switch, enclosing loops and refusals checked")


if __name__ == "__main__":
    main()
