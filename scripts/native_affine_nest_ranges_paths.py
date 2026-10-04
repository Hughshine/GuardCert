"""Observe larger-profile checks in generated Clight, separately from assembly."""
import json
import subprocess
import native_affine_nest_ranges as large
from native_affine_nest_paths import marked_source


def accepted(args, cap):
    which, _, start, n, m, p, _ = args
    return (start < n and large.common.word(start+m) > 0
            and (large.DEPTHS[which] == 2 or p > 0)
            and 1 <= n <= cap and -4 <= start < cap and -8 <= m <= 8
            and (large.DEPTHS[which] == 2 or -8 <= p <= 8))


def main():
    stamp = large.common.check_build()
    report = json.loads((large.WORK/"report.json").read_text())
    assert report["status"] == "passed" and report["all_configurations_checked"]
    assert report["compiler_sha256"] == stamp["compiler_sha256"]
    results = {}
    for name, configuration in report["configurations"].items():
        names = [fn for fn,yes in configuration["installed_functions"].items() if yes]
        if not names:
            continue
        work = large.WORK/name
        source = marked_source((work/(large.SOURCE.stem+".light.c")).read_text(),names)
        cap = 8 if name == "builtin-interchange" else 32
        calls,expected,observations = [],[],[]
        fast = fallback = beyond_old = 0
        for slot,fn in enumerate(names):
            which = large.NAMES.index(fn)
            for args in [row for row in large.inputs() if row[0] == which]:
                hit = int(accepted(args,cap))
                fast += hit
                fallback += 1-hit
                beyond_old += int(hit and args[3]>8)
                calls.append(f"guard_fast[{slot}]=0;guard_fallback[{slot}]=0;affine_range_case("+
                    ",".join(large.common.literal(value) for value in args)+
                    f");if(guard_fast[{slot}]!={hit} || guard_fallback[{slot}]!={1-hit})return 1;")
                expected.append(large.model(args))
                observations.append({"input":list(args),"actual_fast_branch":bool(hit)})
        if name == "builtin-interchange":
            assert fast == 0 and fallback
        else:
            assert fast and fallback and beyond_old
        diagnostic = work/"branch-diagnostic.c"
        diagnostic.write_text(source+"\nint main(void){\n"+"\n".join(calls)+"\nreturn 0;}\n")
        result = subprocess.run(["gcc","-O0","-fwrapv","-Wno-builtin-declaration-mismatch",
            "-Wno-discarded-qualifiers",str(diagnostic),"-o",str(work/"branch-diagnostic")],text=True,capture_output=True)
        (work/"branch-gcc.log").write_text(result.stdout+result.stderr)
        assert result.returncode == 0,(name,result.stderr[-3000:])
        result = subprocess.run([str(work/"branch-diagnostic")],text=True,capture_output=True,timeout=120)
        (work/"branch-output.txt").write_text(result.stdout)
        assert result.returncode == 0 and result.stdout == "".join(expected),name
        print(name,fast,"fast calls,",fallback,"fallback calls;",beyond_old,"fast calls above old cap",flush=True)
        results[name] = {"source_calls":len(calls),"actual_fast_calls":fast,"actual_fallback_calls":fallback,
            "actual_fast_calls_above_old_cap":beyond_old,"all_array_cells_and_public_exits_match_model":True,
            "diagnostic_source_sha256":large.common.sha(diagnostic),
            "output_sha256":large.common.sha(work/"branch-output.txt"),"observations":observations}
    assert results
    (large.WORK/"branch-report.json").write_text(json.dumps({"status":"passed",
        "compiler_sha256":stamp["compiler_sha256"],"source_sha256":report["source_sha256"],"configurations":results,
        "scope":"GCC execution of instrumented actual Clight; larger inferred-profile acceptance and fallback; unmodified assembly checked separately"},indent=2)+"\n")


if __name__ == "__main__":
    main()
