"""Observe actual Clight branches separately from unmodified assembly runs."""
import argparse
import json
import re
import subprocess
import native_affine_nest as fixture
from native_zero_trip import function_body
from native_memory_layout_sequence_paths import printer_for_gcc


def closing_brace(source, opening):
    depth = 1
    for index in range(opening+1, len(source)):
        depth += (source[index] == "{") - (source[index] == "}")
        if depth == 0:
            return index
    raise AssertionError("unbalanced Clight block")


def marked_source(dump, names):
    source = printer_for_gcc(dump)
    main = source.index("\nint guard_original_main(void)\n{")
    source = source[:main]
    for slot, name in enumerate(names):
        body = function_body(source, name)
        conditions = list(re.finditer(r"if \(\$[0-9]+\) \{", body))
        assert len(conditions) >= 2, (name, len(conditions))
        selection = conditions[-1]
        assert sum(condition.group() == selection.group() for condition in conditions) == 2, name
        opening = selection.end()-1
        end = closing_brace(body, opening)
        fallback = re.match(r"\s*else\s*\{", body[end+1:])
        assert fallback, name
        fallback_open = end+1+fallback.end()-1
        prefix = body[:selection.start()]
        for variable, counter in [("local_p", "guard_p_reads"), ("local_alpha", "guard_alpha_reads")]:
            # Only the emitted guard prefix; declarations and the original
            # prelude are before the first copied root header.
            guard_begin = prefix.index("$n;", prefix.index("$L = 83;"))
            guard_begin = prefix.rfind("\n", 0, guard_begin)
            before, guard = prefix[:guard_begin], prefix[guard_begin:]
            guard = re.sub(r"\$" + variable + r"\b",
                           "(" + counter + "[" + str(slot) + "]++, $" + variable + ")", guard)
            prefix = before + guard
        changed = (prefix + body[selection.start():opening+1] +
                   f"guard_fast[{slot}]++;" + body[opening+1:fallback_open+1] +
                   f"guard_fallback[{slot}]++;" + body[fallback_open+1:])
        source = source.replace(body, changed, 1)
    declarations = "".join("int " + name + "[" + str(len(names)) + "];\n"
                           for name in ["guard_fast", "guard_fallback", "guard_p_reads", "guard_alpha_reads"])
    return declarations + source


def guard_accepts(args):
    which, _, start, n, m, p, _ = args
    if not start < n:
        return False
    first_upper = fixture.word(m-start if which == 4 else start+m)
    if first_upper <= 0 or (fixture.DEPTHS[which] == 3 and p <= 0):
        return False
    return (1 <= n <= 8 and -4 <= start <= 7 and -8 <= m <= 8
            and (fixture.DEPTHS[which] == 2 or -8 <= p <= 8))


def diagnostic(name, configuration):
    work = fixture.WORK / name
    names = [fn for fn, facts in configuration["functions"].items() if facts["guarded"]]
    source = marked_source((work / (fixture.SOURCE.stem + ".light.c")).read_text(), names)
    calls, expected, observations = [], [], []
    fast = fallback = negative = undefined_p = undefined_alpha = restored_empty = 0
    for slot, function in enumerate(names):
        which = fixture.NAMES.index(function)
        for args in [row for row in fixture.full_inputs() if row[0] == which]:
            hit = int(guard_accepts(args))
            fast += hit
            fallback += 1-hit
            negative += int(hit and args[2] < 0)
            points, final = fixture.source_points(args)
            last_child_empty = args[2] < args[3] and final[3] <= 0
            restored_empty += int(hit and last_child_empty and which == 4)
            checks = []
            if which == 3:
                _, _, start, n, m, p, _ = args
                p_defined = start < n and fixture.word(n-1+m) > 0
                alpha_defined = p_defined and fixture.word(n-2+m+p) > 0
                if not p_defined:
                    checks.append(f"guard_p_reads[{slot}]!=0")
                    undefined_p += 1
                if not alpha_defined:
                    checks.append(f"guard_alpha_reads[{slot}]!=0")
                    undefined_alpha += 1
            calls.append("".join(f"{counter}[{slot}]=0;" for counter in
                         ["guard_fast", "guard_fallback", "guard_p_reads", "guard_alpha_reads"]) +
                         "affine_case(" + ",".join(fixture.literal(x) for x in args) + ");" +
                         f"if(guard_fast[{slot}]!={hit} || guard_fallback[{slot}]!={1-hit}" +
                         "".join(" || " + check for check in checks) + ")return 1;")
            expected.append(fixture.output_model(args))
            observations.append({"input": list(args), "actual_fast_branch": bool(hit),
                "last_source_child_empty": last_child_empty,
                "guard_local_p_read_count_required_zero": which == 3 and not p_defined,
                "guard_local_alpha_read_count_required_zero": which == 3 and not alpha_defined})
    assert fast and fallback and negative and undefined_p and undefined_alpha and restored_empty
    diagnostic_source = work / "branch-diagnostic.c"
    diagnostic_source.write_text(source + "\nint main(void){\n" + "\n".join(calls) + "\nreturn 0;}\n")
    compiled = subprocess.run(["gcc", "-O0", "-fwrapv", "-Wno-builtin-declaration-mismatch",
        "-Wno-discarded-qualifiers", str(diagnostic_source), "-o", str(work / "branch-diagnostic")],
        capture_output=True, text=True)
    (work / "branch-gcc.log").write_text(compiled.stdout + compiled.stderr)
    assert compiled.returncode == 0, (name, compiled.stderr[-3000:])
    result = subprocess.run([str(work / "branch-diagnostic")], text=True, capture_output=True, timeout=120)
    (work / "branch-output.txt").write_text(result.stdout)
    assert result.returncode == 0, (name, len(result.stdout.splitlines()))
    assert result.stdout == "".join(expected), name
    print(name, fast, "fast calls,", fallback, "fallback calls;", undefined_p,
          "undefined bound parameters safely skipped", flush=True)
    return {"source_calls": len(calls), "actual_fast_calls": fast, "actual_fallback_calls": fallback,
            "negative_root_fast_calls": negative, "undefined_child_parameter_calls": undefined_p,
            "undefined_leaf_parameter_calls": undefined_alpha,
            "accepted_final_child_empty_calls": restored_empty,
            "complete_arrays_and_public_exits_match_model": True,
            "undefined_parameters_have_zero_guard_reads": True,
            "diagnostic_source_sha256": fixture.sha(diagnostic_source),
            "diagnostic_output_sha256": fixture.sha(work / "branch-output.txt"), "observations": observations}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cases")
    args = parser.parse_args()
    stamp = fixture.check_build()
    report = json.loads((fixture.WORK / "report.json").read_text())
    assert report["status"] == "passed" and report["all_configurations_checked"]
    assert report["compiler_sha256"] == stamp["compiler_sha256"]
    assert report["source_sha256"] == fixture.sha(fixture.SOURCE)
    selected = set(args.cases.split(",")) if args.cases else {"identity", "box", "interchange", "reverse"}
    results = {name: diagnostic(name, configuration)
               for name, configuration in report["configurations"].items() if name in selected}
    assert set(results) == selected
    (fixture.WORK / ("smoke-branch-report.json" if args.cases else "branch-report.json")).write_text(json.dumps({
        "status": "passed", "compiler_sha256": stamp["compiler_sha256"],
        "source_sha256": report["source_sha256"], "configurations": results,
        "scope": "GCC execution of instrumented actual Clight guards; accepted and fallback branches, "
                 "empty-child public exits and lazy undefined parameters; unmodified assembly checked separately"}, indent=2) + "\n")


if __name__ == "__main__":
    main()
