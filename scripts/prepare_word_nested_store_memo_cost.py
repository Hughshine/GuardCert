"""Prepare frozen complete-call benchmarks and actual Clight guard diagnostics.

All timed programs are unmodified CompCert assembly. Read previous proof,
compiler and native reports; never rebuild or replace their checkpoints.
Preparation checks full outputs for repeated execution before timing begins.
"""
import argparse
from collections import Counter
import json
import os
from pathlib import Path
import re
import subprocess
import time

from audit_interface_clight import ROOT, sha
import build_pipeline_pluto as scheduler
import measure_word_nested_store_memo_work as setup_work
import native_word_nested_store_shared as shared
import native_word_nested_store_memo as memo
import word_nested_store_affine_fixtures as fixture

WORK = ROOT / "build/multi-word-nested-memo/cost-prepared-v1"
MODES = ["source", "shared", "memo"]
PROFILES = {"row": (False, False), "column": (True, False), "row-variable": (False, True)}
CASES = {
    "small-accepted": (0, 0, 2, 3, 1, 16),
    "cap-accepted": (0, 0, 8, 8, 1, 16),
    "word-wrap": (0, 0, 3, 2, 2147483647, 16),
    "alias-refusal": (1, 0, 2, 3, 1, 16),
    "header-refusal": (0, 1, 2, 3, 1, 16),
    "header-alias-refusal": (3, 0, 2, 2, -2, 16),
    "setup-refusal": (0, 0, 9, 1, 1, 16),
    "outer-empty": (6, 0, 0, 99, 7, 16),
    "child-empty": (7, 0, 2, 0, 7, 16),
}
HELPERS = ["scripts/prepare_word_nested_store_memo_cost.py",
           "scripts/measure_word_nested_store_memo_work.py",
           "scripts/measure_word_nested_store_shared_size.py",
           "scripts/native_word_nested_store_shared.py", "scripts/native_word_nested_store_memo.py",
           "scripts/native_word_nested_store_affine.py", "scripts/word_nested_store_affine_fixtures.py",
           "scripts/build_pipeline_pluto.py", "scripts/audit_interface_clight.py",
           "scripts/native_selected_regions.py", "scripts/native_zero_trip.py",
           "scripts/native_memory_layout_sequence_paths.py"]


def source_text(profile):
    column, variable = PROFILES[profile]
    selected = fixture.source_text(column, True, variable).split("\nvoid loaded_unmarked(", 1)[0]
    assert selected.count("#pragma scop") == selected.count("#pragma endscop") == 1
    rows = ",\n".join("{" + ",".join(map(str, case)) + "}" for case in CASES.values())
    return "#include <stdlib.h>\n#include <time.h>\n" + selected + """
int *bench_a,*bench_b,*bench_h,*bench_k;
int bench_alias,bench_start,bench_n,bench_m,bench_alpha,bench_ld;
int bench_inputs[][6]={
""" + rows + """};
void initialize(int which){int x;
bench_alias=bench_inputs[which][0];bench_start=bench_inputs[which][1];
bench_n=bench_inputs[which][2];bench_m=bench_inputs[which][3];
bench_alpha=bench_inputs[which][4];bench_ld=bench_inputs[which][5];
for(x=0;x<1024;x++)arena[x]=3*x+1;
bench_a=arena+64;bench_b=arena+(bench_alias==1?64:320);
bench_h=arena;bench_k=bench_alias==3?bench_b:arena+1;
*bench_h=bench_n;*bench_k=bench_m;
if(bench_alias==6){bench_a=0;bench_b=0;bench_k=0;}
if(bench_alias==7){bench_a=0;bench_b=0;}
first_i=bench_start;first_j=77;}
void reset_headers(void){*bench_h=bench_n;if(bench_k)*bench_k=bench_m;}
void show(void){int x;printf("RESULT %d %d %d %d",public_i,public_j,first_i,first_j);
for(x=0;x<1024;x++)printf(" %d",arena[x]);printf("\\n");}
int main(int argc,char **argv){int r,count,which;clock_t before,after;
if(argc!=3)return 2;which=atoi(argv[1]);count=atoi(argv[2]);
if(which<0 || which>=""" + str(len(CASES)) + """ || count<0)return 3;
initialize(which);reset_headers();
loaded_pair(bench_a,bench_b,bench_h,bench_k,bench_start,bench_alpha,bench_ld);show();
before=clock();for(r=0;r<count;r++){reset_headers();
loaded_pair(bench_a,bench_b,bench_h,bench_k,bench_start,bench_alpha,bench_ld);}
after=clock();printf("TIME %d %lu %lu\\n",count,(unsigned long)(after-before),(unsigned long)CLOCKS_PER_SEC);
show();return 0;}
"""


def one_run(memory, case, column, variable):
    alias, start, n, m, alpha, ld = case
    a, b, h, k = 64, (64 if alias == 1 else 320), 0, (320 if alias == 3 else 1)
    memory[h] = n
    if alias != 6:
        memory[k] = m
    i, j, steps = start, 77, 0
    while i < memory[h]:
        assert alias != 6, "Unavailable child"
        j = 0
        while j < memory[k]:
            assert alias != 7, "Unavailable arrays"
            index = fixture.point_index(i, j, column, variable, ld)
            assert 0 <= a + index < len(memory) and 0 <= b + index < len(memory)
            memory[a + index] = fixture.word(memory[b + index] + alpha)
            memory[b + index] = fixture.word(memory[a + index] + alpha)
            j += 1
            steps += 1
            assert steps <= 1024
        i += 1
    return i, j


def expected(profile, case_name, calls):
    assert calls >= 1
    case = CASES[case_name]
    alias, start, n, m, alpha, ld = case
    column, variable = PROFILES[profile]
    initial, a, b, h, k = fixture.initial((0, *case))
    first = list(initial)
    public = one_run(first, case, column, variable)
    if alias == 3:
        # This header-refusal input resets k=2 then the first store sets it to
        # -2. Its remaining inner tests refuse, and the complete call is
        # idempotent under the documented header reset.
        second = list(first)
        assert one_run(second, case, column, variable) == public and second == first
        after = first
    else:
        assert first[h] == initial[h] and first[k] == initial[k]
        indices = Counter(fixture.point_index(i, j, column, variable, ld)
                          for i in range(start, n) for j in range(m))
        if alias != 1:
            assert not {a + index for index in indices}.intersection(b + index for index in indices)
        after = list(initial)
        for index, multiplicity in indices.items():
            if alias == 1:
                after[a + index] = fixture.word(initial[a + index] + 2 * alpha * multiplicity * calls)
            else:
                after[a + index] = fixture.word(initial[b + index] + (2 * multiplicity * calls - 1) * alpha)
                after[b + index] = fixture.word(initial[b + index] + 2 * multiplicity * calls * alpha)
        if calls == 1:
            assert after == first
    return "RESULT " + " ".join(map(str, [*public, start, 77, *after]))


def check_oracle():
    for profile, (column, variable) in PROFILES.items():
        for name, case in CASES.items():
            memory, *_ = fixture.initial((0, *case))
            for calls in range(1, 5):
                public = one_run(memory, case, column, variable)
                literal = "RESULT " + " ".join(map(str, [*public, case[1], 77, *memory]))
                assert literal == expected(profile, name, calls), (profile, name, calls)


def parent_inputs():
    setup_work.validate()
    parents = [ROOT / "build/multi-word-nested-shared/native-v1/report.json",
               ROOT / "build/multi-word-nested-memo/native-v1/report.json",
               ROOT / "build/multi-word-nested-memo/work-v1/report.json"]
    bindings = shared.check_build() | memo.check_build()
    bindings |= {path: sha(path) for path in parents}
    return bindings


def environment(mode, directory, pluto):
    env = {key: value for key, value in os.environ.items() if not key.startswith("GUARDCERT_")}
    env.update(GUARDCERT_TENSOR_MODE="disabled" if mode == "source" else "pipeline",
               GUARDCERT_POLYHEDRAL_MODE="tile", GUARDCERT_TILE_SIZES="2,3",
               GUARDCERT_PLUTO=str(pluto), GUARDCERT_PIPELINE_DUMP=str(directory / "phases"),
               GUARDCERT_SCOP_DIAGNOSTICS="1", GUARDCERT_TENSOR_DIAGNOSTICS="1")
    return env


def compile_one(profile, mode, pluto):
    directory = WORK / profile / mode
    directory.mkdir(parents=True)
    source = WORK / profile / "cost.c"
    compiler = shared.COMPILER if mode == "shared" else memo.COMPILER
    command = [str(compiler), "-fall", "-stdlib", str(compiler.parent / "runtime"),
               "-dclight", "-S", "-o", str(directory / "program.s"), str(source)]
    env = environment(mode, directory, pluto)
    (directory / "compile-command.json").write_text(json.dumps({"argv": command,
        "environment": {key: value for key, value in env.items() if key.startswith("GUARDCERT_")}}, indent=2) + "\n")
    started = time.monotonic()
    with (directory / "compile.log").open("x") as log:
        subprocess.run(command, cwd=directory, env=env, stdout=log, stderr=subprocess.STDOUT,
                       check=True, timeout=600)
    compile_seconds = time.monotonic() - started
    subprocess.run(["gcc", "-no-pie", str(directory / "program.s"), "-o", str(directory / "program")],
                   capture_output=True, check=True)
    assembly = (directory / "program.s").read_text()
    assert len(re.findall(r"\bcall\s+loaded_pair\b", assembly)) >= 2, "Timed kernel calls missing"
    dump = (directory / "cost.light.c").read_text()
    body = fixture.function_body(dump, "loaded_pair")
    sites = list(shared.dispatch_sites(body))
    assert [layer for layer, *_ in sites] == ([] if mode == "source" else ["header", "candidate"])
    phases = list((directory / "phases").glob("guardcert-phase-*"))
    assert len(phases) == (0 if mode == "source" else 1)
    for phase in phases:
        assert (phase / "source-rank.txt").read_text() == "2\n"
        assert all((phase / name).is_file() for name in ["before.scop", "generated.loop", "receipt.txt"])
        assert (phase / "affine-result.txt").read_text() == (phase / "tiling-result.txt").read_text() == "accepted\n"
    nm = subprocess.check_output(["nm", "-S", "--defined-only", str(directory / "program")], text=True)
    (directory / "nm.txt").write_text(nm)
    match = re.search(r"^[0-9a-fA-F]+\s+([0-9a-fA-F]+)\s+T\s+loaded_pair$", nm, re.M)
    assert match
    return {"compile_wall_seconds": compile_seconds, "kernel_bytes": int(match.group(1), 16),
            "installed_sites": 0 if mode == "source" else 1, "phase_calls": len(phases)}


def sample(prepared, profile, mode, case_name, repetitions, cpu=None, output_path=None):
    case_index = list(CASES).index(case_name)
    command = [str(prepared / profile / mode / "program"), str(case_index), str(repetitions)]
    if cpu is not None:
        command = ["taskset", "-c", str(cpu), *command]
    output = subprocess.check_output(command, text=True, timeout=60)
    if output_path is not None:
        with output_path.open("x") as log:
            log.write(output)
    lines = output.splitlines()
    assert len(lines) == 3 and lines[1].startswith("TIME "), (profile, mode, case_name, "output-lines")
    assert lines[0] == expected(profile, case_name, 1), (profile, mode, case_name, "warmup-output")
    assert lines[2] == expected(profile, case_name, repetitions + 1), (profile, mode, case_name, "final-output")
    count, ticks, frequency = map(int, lines[1].split()[1:])
    assert count == repetitions and ticks >= 0 and frequency > 0
    return {"repetitions": count, "cpu_ticks": ticks, "ticks_per_second": frequency,
            "cpu_seconds": ticks / frequency, "ns_per_call": 1e9 * ticks / frequency / count if count else None,
            "warmup_and_final_outputs_checked": True}


def instrument_guard(body, installed):
    additions, excluded = [], []
    for layer, yes, _no in shared.dispatch_sites(body):
        additions.append((yes + 1, "probe_header++;" if layer == "header" else "probe_fast++;"))
        if layer == "candidate":
            excluded.append((yes + 1, fixture.closing_brace(body, yes)))
    root_loop = r"for\s*\(\s*;\s*1\s*;\s*\$i\s*=\s*\$i\s*\+\s*1U?\s*\)\s*\{"
    root_test = r"\s*if\s*\(\s*!\s*\(\s*\$i\s*<\s*(\*\s*\$h|\$[0-9]+)"
    for loop in re.finditer(root_loop, body):
        test = re.match(root_test, body[loop.end():])
        assert test is not None
        bound = test.group(1)
        additions.append((loop.start(), "probe_loaded++;" if "*" in bound else
                          f"if({bound}==0)probe_empty++;else probe_cached++;"))
        excluded.append((loop.start(), fixture.closing_brace(body, loop.end() - 1) + 1))
    tests = 0
    if installed:
        for match in re.finditer(r"\bif\s*\(", body):
            if any(start <= match.start() < end for start, end in excluded):
                continue
            opening = match.end() - 1
            closing = setup_work.parenthesis_end(body, opening)
            additions += [(opening + 1, "++guard_tests, ("), (closing - 1, ")")]
            tests += 1
    for position, text in sorted(additions, reverse=True):
        body = body[:position] + text + body[position:]
    return body, tests


def diagnostic(profile, mode):
    directory = WORK / profile / mode
    dump = (directory / "cost.light.c").read_text()
    main = re.search(r"^int main\([^;\n]*\)\n\{", dump, re.M)
    assert main is not None
    prefix = re.sub(r"^int main\([^;\n]*\);\n", "", dump[:main.start()], flags=re.M)
    source = fixture.printer_for_gcc(prefix + "int main(void)\n{\nreturn 0;\n}\n")
    body = fixture.function_body(source, "loaded_pair")
    body_with_setup, trees, nodes = setup_work.counted_setup(body)
    assert trees == (0 if mode == "source" else 1)
    changed, guard_nodes = instrument_guard(body_with_setup, mode != "source")
    source = source.replace(body, changed, 1)
    counters = "probe_header,probe_fast,probe_cached,probe_loaded,probe_empty"
    source = "unsigned long guard_tests;unsigned int setup_tests;int " + counters + ";\n" + source
    source += "int main(void){int which;for(which=0;which<" + str(len(CASES)) + ";which++){" + \
        "initialize(which);reset_headers();guard_tests=setup_tests=" + \
        "probe_header=probe_fast=probe_cached=probe_loaded=probe_empty=0;" + \
        "loaded_pair(bench_a,bench_b,bench_h,bench_k,bench_start,bench_alpha,bench_ld);show();" + \
        'printf("GUARD %lu %u %d %d %d %d %d\\n",guard_tests,setup_tests,' + counters + ");}return 0;}\n"
    path = directory / "guard-diagnostic.c"
    path.write_text(source)
    command = ["gcc", "-O0", "-fwrapv", "-Wno-builtin-declaration-mismatch", "-Wno-discarded-qualifiers",
               str(path), "-o", str(directory / "guard-diagnostic")]
    run = subprocess.run(command, capture_output=True, text=True)
    (directory / "guard-diagnostic-compile.log").write_text(run.stdout + run.stderr)
    assert run.returncode == 0, (profile, mode, "guard-diagnostic-compile")
    output = subprocess.check_output([str(directory / "guard-diagnostic")], text=True, timeout=60)
    (directory / "guard-diagnostic.txt").write_text(output)
    lines = output.splitlines()
    assert len(lines) == 2 * len(CASES)
    rows = {}
    column, variable = PROFILES[profile]
    for i, (name, case) in enumerate(CASES.items()):
        assert lines[2 * i] == expected(profile, name, 1), (profile, mode, name, "diagnostic-memory")
        assert lines[2 * i + 1].startswith("GUARD ")
        values = list(map(int, lines[2 * i + 1].split()[1:]))
        assert len(values) == 7
        memory, a, b, h, k = fixture.initial((0, *case))
        paths = fixture.expected_path((0, *case), memory, a, b, h, k, column, variable, mode != "source")
        assert values[2:] == paths, (profile, mode, name, "diagnostic-paths", values[2:], paths)
        rows[name] = {"guard_if_evaluations": values[0], "setup_if_evaluations": values[1], "paths": paths}
    return {"rows": rows, "static_guard_if_nodes": guard_nodes, "static_setup_if_nodes": nodes,
            "assembly_work_claim": False, "timed": False}


def validate(work=WORK):
    report = json.loads((work / "report.json").read_text())
    assert report["status"] == "prepared" and report["parent_bindings"] == {
        str(path.relative_to(ROOT)): digest for path, digest in parent_inputs().items()}
    assert report["profiles"] == {key: list(value) for key, value in PROFILES.items()}
    assert report["cases"] == {key: list(value) for key, value in CASES.items()}
    assert set(report["configurations"]) == {profile + "/" + mode for profile in PROFILES for mode in MODES}
    for path, digest in report["bindings"].items():
        assert sha(ROOT / path) == digest, path
    for profile in PROFILES:
        assert (work / profile / "cost.c").read_text() == source_text(profile)
        old = report["configurations"][profile + "/shared"]["diagnostic"]["rows"]
        new = report["configurations"][profile + "/memo"]["diagnostic"]["rows"]
        for name in CASES:
            assert old[name]["paths"] == new[name]["paths"]
            assert new[name]["setup_if_evaluations"] <= old[name]["setup_if_evaluations"]
            assert new[name]["guard_if_evaluations"] - new[name]["setup_if_evaluations"] == \
                old[name]["guard_if_evaluations"] - old[name]["setup_if_evaluations"]
    return report


def main():
    global WORK
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, default=WORK)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    WORK = args.work.resolve()
    assert WORK.is_relative_to(ROOT / "build/multi-word-nested-memo")
    if args.validate or (WORK / "report.json").exists():
        report = validate(WORK)
        print(json.dumps({"status": "validated", "configurations": len(report["configurations"]),
                          "report_sha256": sha(WORK / "report.json")}))
        return
    assert not WORK.exists(), "Refusing to overwrite prepared cost artifacts"
    parents = parent_inputs()
    check_oracle()
    pluto = (ROOT / scheduler.validate()["binary"]).resolve()
    WORK.mkdir()
    configurations = {}
    try:
        for profile in PROFILES:
            directory = WORK / profile
            directory.mkdir()
            source = directory / "cost.c"
            source.write_text(source_text(profile))
            subprocess.run(["gcc", "-O0", "-fwrapv", str(source), "-o", str(directory / "reference")],
                           capture_output=True, check=True)
            for name in CASES:
                for count in [0, 1, 3]:
                    # The same independent full-output oracle checks GCC C and
                    # every uninstrumented assembly benchmark at repeated exits.
                    index = list(CASES).index(name)
                    output = subprocess.check_output([str(directory / "reference"), str(index), str(count)], text=True)
                    lines = output.splitlines()
                    assert lines[0] == expected(profile, name, 1)
                    assert lines[2] == expected(profile, name, count + 1)
                    (directory / f"reference-{name}-{count}.txt").write_text(output)
            for mode in MODES:
                item = compile_one(profile, mode, pluto)
                for name in CASES:
                    for count in [0, 1, 3]:
                        sample(WORK, profile, mode, name, count,
                               output_path=directory / mode / f"checked-{name}-{count}.txt")
                item["diagnostic"] = diagnostic(profile, mode)
                configurations[profile + "/" + mode] = item
                print(json.dumps({"profile": profile, "mode": mode, "status": "prepared",
                                  "bytes": item["kernel_bytes"]}), flush=True)
    except Exception as error:
        (WORK / "failure.json").write_text(json.dumps({"status": "failed", "error": repr(error),
                    "completed": list(configurations)}, indent=2) + "\n")
        raise
    bindings = parents | {ROOT / path: sha(ROOT / path) for path in HELPERS}
    bindings[scheduler.REPORT] = sha(scheduler.REPORT)
    bindings[ROOT / "toolchain.lock.json"] = sha(ROOT / "toolchain.lock.json")
    bindings |= {path: sha(path) for path in WORK.rglob("*") if path.is_file()}
    report = {"status": "prepared", "configurations": configurations,
              "profiles": {key: list(value) for key, value in PROFILES.items()},
              "cases": {key: list(value) for key, value in CASES.items()},
              "parent_bindings": {str(path.relative_to(ROOT)): digest for path, digest in parents.items()},
              "assembly_full_output_checks": len(PROFILES) * len(MODES) * len(CASES) * 3,
              "independent_Clight_calls": len(PROFILES) * len(MODES) * len(CASES),
              "new_compiler_or_semantic_theorem": False, "source_and_candidate_proofs_reused": True,
              "full_goal_complete": False,
              "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()}}
    with (WORK / "report.json").open("x") as out:
        out.write(json.dumps(report, indent=2) + "\n")
    validate(WORK)
    print(json.dumps({"status": "prepared", "assembly_checks": report["assembly_full_output_checks"],
                      "Clight_calls": report["independent_Clight_calls"], "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
