"""Check invariant-word guards on real C, full arrays, public exits, and Clight dispatch."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

from audit_interface_clight import ROOT, sha
import native_nested_frontend as frontend
from native_zero_trip import function_body
from native_affine_nest_paths import closing_brace
from native_memory_layout_sequence_paths import printer_for_gcc

WORK = ROOT / "build/nested-invariant/native"
COMPILER = ROOT / "build/nested-invariant/compiler/ccomp"
PROOF = ROOT / "build/nested-invariant/proof/report.json"
ENTRY = "ClightGuardedNestedInvariantCompiler.compile_ncs_invariant_regions"
SOURCE = WORK / "invariant_words.c"
MODES = ["disabled", "identity", "interchange", "tile-2-3", "wrong-reindex", "invalid-domain"]
NAMES = ["invariant_fill", "changing_fill"]
SIZE, CENTER = 2048, 128
CASES = [(0, view, 0, 3, 3, 1, 1) for view in [0, 1, 2]]
CASES += [(0, view, 0, 1, 1, -2**31, -2**31) for view in [0, 1, 2]]
CASES += [(0, view, 0, 2, 3, 1, 1) for view in [0, 1, 2]]
CASES += [(0, view, 0, 1, 2, 1, 0) for view in [0, 1, 2]]
CASES += [(0, 0, 1, 3, 3, 1, 1), (0, 0, 0, -1, 99, 1, 1),
          (0, 0, 0, 3, -1, 1, 1), (0, 0, 0, 2**31-1, 99, 1, 1),
          (0, 0, 0, 3, 3, 2**31-1, 2**31-1)]
CASES += [(1, view, 0, 1, 1, 0, 0) for view in [0, 1, 2]]
HELPERS = ["scripts/native_nested_invariant.py", "scripts/native_nested_frontend.py",
           "scripts/native_zero_trip.py", "scripts/native_affine_nest_paths.py",
           "scripts/native_memory_layout_sequence_paths.py", "scripts/audit_interface_clight.py"]


def word(value):
    return (value + 2**31) % 2**32 - 2**31


def literal(value):
    return "(-2147483647-1)" if value == -2**31 else str(value)


def model(case):
    kind, view, start, u, v, alpha, beta = case
    arrays = {"A": [word(3*x+1) for x in range(SIZE)], "D": [u, v]}
    header, base = ("D", 0) if view == 0 else ("A", CENTER+(5 if view == 2 else 0))
    arrays[header][base:base+2] = [u, v]
    public = [start, 77, 91]
    count = 0
    while public[0] < word(arrays[header][base]+1):
        assert 0 <= public[0] < 32, (case, "root range")
        public[1] = 0
        while public[1] < word(arrays[header][base+1]+1):
            assert 0 <= public[1] < 32, (case, "child range")
            public[2] = 0
            while public[2] < 5:
                r, c, k = public
                index = CENTER+80*r+5*c+k
                assert 0 <= index < SIZE, (case, index)
                value = alpha+beta+1 if kind == 0 else alpha+r+c+k
                arrays["A"][index] = word(value)
                public[2] += 1
                count += 1
                assert count < 20000, (case, "runaway")
            public[1] += 1
        public[0] += 1
    return " ".join(map(str, [*case, *public, 107, 211, arrays[header][base], arrays[header][base+1], *arrays["A"]]))+"\n"


def expected_output():
    return "".join(model(case) for case in CASES)


def source_text():
    text = '#include <stdio.h>\nint nc_row,nc_column,nc_component,nc_pre,nc_post;\n'
    for kind, name in enumerate(NAMES):
        value = "(alpha+beta)+1" if kind == 0 else "alpha+row+column+component"
        text += (f"void {name}(int *a,int *shape,int start,int alpha,int beta){{"
                 "int row=start,column=77,component=91;nc_pre=nc_pre+7;"
                 "for(;row<shape[0]+1;row++)for(column=0;column<shape[1]+1;column++)"
                 f"for(component=0;component<5;component++)a[80*row+5*column+component]={value};"
                 "nc_row=row;nc_column=column;nc_component=component;nc_post=nc_post+11;}\n")
    text += '''void invariant_case(int kind,int view,int start,int u,int v,int alpha,int beta){
int A[2048],dims[2],x;int *a,*shape;for(x=0;x<2048;x++)A[x]=3*x+1;
a=A+128;dims[0]=u;dims[1]=v;shape=dims;
if(view==1){shape=a;shape[0]=u;shape[1]=v;}if(view==2){shape=a+5;shape[0]=u;shape[1]=v;}
nc_pre=100;nc_post=200;
if(kind==0)invariant_fill(a,shape,start,alpha,beta);if(kind==1)changing_fill(a,shape,start,alpha,beta);
printf("%d %d %d %d %d %d %d %d %d %d %d %d %d %d",kind,view,start,u,v,alpha,beta,nc_row,nc_column,nc_component,nc_pre,nc_post,shape[0],shape[1]);
for(x=0;x<2048;x++)printf(" %d",A[x]);printf("\\n");}
'''
    return text+'int main(void){'+"".join("invariant_case("+",".join(map(literal,case))+");" for case in CASES)+"return 0;}\n"


def expected_dispatch(mode, case):
    if mode not in ["identity", "interchange", "tile-2-3"]:
        return [0, 0]
    kind, view, start, u, v, alpha, beta = case
    numeric = start == 0 and 1 <= word(u+1) < 5 and 1 <= word(v+1) < 5
    stable = view == 0 or kind == 0 and u == v == word(alpha+beta+1)
    accepted = numeric and stable
    return [int(accepted), int(not accepted)]


def branch_probe(mode, directory):
    source = printer_for_gcc((directory/(SOURCE.stem+".light.c")).read_text())
    for name in NAMES:
        body = function_body(source, name)
        insertions = []
        for match in re.finditer(r"if \(\$[0-9]+\) \{", body):
            opening = match.end()-1
            end = closing_brace(body, opening)
            no = re.match(r"\s*else\s*\{", body[end+1:])
            if no is None:
                continue
            fallback = end+1+no.end()-1
            finish = closing_brace(body, fallback)
            if "$row < *($shape + 0) + 1" in body[fallback:finish] and "*($a" in body[opening:end]:
                insertions += [(opening+1,"invariant_fast++;"), (fallback+1,"invariant_refusal++;")]
        assert len(insertions) == 2, (mode, name, len(insertions))
        changed = body
        for offset, value in sorted(insertions, reverse=True):
            changed = changed[:offset]+value+changed[offset:]
        source = source.replace(body, changed, 1)
    source = "int invariant_fast,invariant_refusal;\n"+source
    source += "int main(void){"+"".join(
        "invariant_fast=0;invariant_refusal=0;invariant_case("+",".join(map(literal,case))+
        ');printf("PATH %d %d\\n",invariant_fast,invariant_refusal);' for case in CASES)+"return 0;}\n"
    path = directory/"branches.c"
    path.write_text(source)
    subprocess.run(["gcc", "-O0", "-fwrapv", "-Wno-builtin-declaration-mismatch", "-Wno-discarded-qualifiers",
                    str(path), "-o", str(directory/"branches")], capture_output=True, check=True)
    output = subprocess.check_output([str(directory/"branches")], text=True, timeout=90)
    (directory/"branch-output.txt").write_text(output)
    actual = [list(map(int,line.split()[1:])) for line in output.splitlines() if line.startswith("PATH ")]
    assert actual == [expected_dispatch(mode,case) for case in CASES], (mode, actual)
    assert "\n".join(line for line in output.splitlines() if not line.startswith("PATH "))+"\n" == expected_output()
    return {"calls": len(CASES), "cases_and_dispatch": [[list(case), branch] for case, branch in zip(CASES, actual)],
            "assembly_path_claim": False,
            "artifacts": {name: sha(directory/name) for name in ["branches.c", "branches", "branch-output.txt"]}}


def compile_run(mode):
    directory = WORK/mode
    directory.mkdir(parents=True, exist_ok=True)
    env = {k:v for k,v in os.environ.items() if not k.startswith("GUARDCERT_")}
    env.update(GUARDCERT_AFFINE_MODE=mode, GUARDCERT_AFFINE_CAP="4", GUARDCERT_AFFINE_BOUND_LOW="1",
               GUARDCERT_AFFINE_BOUND_HIGH="5", GUARDCERT_AFFINE_DIAGNOSTICS="1")
    with (directory/"compile.log").open("w") as log:
        subprocess.run([str(COMPILER), "-conf", str(COMPILER.parent/"compcert.ini"),
                        "-stdlib", str(COMPILER.parent/"runtime"), "-dclight", "-S", "-o",
                        str(directory/"program.s"), str(SOURCE)], cwd=directory, env=env,
                       stdout=log, stderr=subprocess.STDOUT, check=True, timeout=300)
    subprocess.run(["gcc", "-no-pie", str(directory/"program.s"), "-o", str(directory/"program")], check=True)
    output = subprocess.check_output([str(directory/"program")], text=True, timeout=90)
    (directory/"output.txt").write_text(output)
    assert output == expected_output(), mode
    dump = (directory/(SOURCE.stem+".light.c")).read_text()
    sizes = {}
    for name in NAMES:
        body = function_body(dump, name)
        installed = body.count("for (") > 3
        assert installed == (mode in ["identity", "interchange", "tile-2-3"]), (mode, name)
        sizes[name] = {"installed": installed, "machine_bytes": frontend.machine_bytes(directory/"program", name)}
    return {"calls": len(CASES), "functions": sizes,
            "artifacts": {name: sha(directory/name) for name in
                          ["compile.log", "program.s", "program", "output.txt", SOURCE.stem+".light.c"]}}


def bindings():
    return {"status": "passed", "proved_entrypoint": ENTRY, "compiler_sha256": sha(COMPILER),
            "proof_report_sha256": sha(PROOF), "stamp_sha256": sha(COMPILER.parent/".guard-build.json"),
            "source_sha256": sha(SOURCE), "cases": [list(case) for case in CASES],
            "helpers": {name: sha(ROOT/name) for name in HELPERS}}


def validate(report):
    frontend.COMPILER, frontend.PROOF, frontend.ENTRY = COMPILER, PROOF, ENTRY
    frontend.check_build()
    assert {key:report[key] for key in bindings()} == bindings()
    assert SOURCE.read_text() == source_text()
    assert (WORK/"reference-output.txt").read_text() == expected_output()
    assert sha(WORK/"reference-output.txt") == report["reference_sha256"]
    assert set(report["configurations"]) == set(MODES)
    for mode, facts in report["configurations"].items():
        directory = WORK/mode
        for name, digest in facts["artifacts"].items():
            assert sha(directory/name) == digest, (mode, name)
        assert (directory/"output.txt").read_text() == expected_output()
        assert facts["calls"] == len(CASES)
        for name, values in facts["functions"].items():
            assert values["installed"] == (mode in ["identity", "interchange", "tile-2-3"])
            assert values["machine_bytes"] == frontend.machine_bytes(directory/"program", name)
    assert set(report["clight_dispatch"]) == {"identity", "interchange", "tile-2-3"}
    for mode, facts in report["clight_dispatch"].items():
        directory = WORK/mode
        for name, digest in facts["artifacts"].items():
            assert sha(directory/name) == digest, (mode, name)
        assert facts["calls"] == len(CASES) and not facts["assembly_path_claim"]
        assert facts["cases_and_dispatch"] == [[list(case), expected_dispatch(mode,case)] for case in CASES]
        output = (directory/"branch-output.txt").read_text().splitlines()
        actual = [list(map(int,line.split()[1:])) for line in output if line.startswith("PATH ")]
        assert actual == [expected_dispatch(mode,case) for case in CASES]
        assert "\n".join(line for line in output if not line.startswith("PATH "))+"\n" == expected_output()
    assert report["assembly_calls"] == len(CASES)*len(MODES)
    assert report["clight_dispatch_calls"] == len(CASES)*3
    assert not report["new_machine_dispatch_probes"] and not report["cost_or_profitability_measured"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    frontend.COMPILER, frontend.PROOF, frontend.ENTRY = COMPILER, PROOF, ENTRY
    if args.validate:
        validate(json.loads((WORK/"report.json").read_text()))
        print(json.dumps({"status":"validated", "report_sha256":sha(WORK/"report.json")}))
        return
    frontend.check_build()
    WORK.mkdir(parents=True, exist_ok=True)
    SOURCE.write_text(source_text())
    subprocess.run(["gcc", "-O0", "-fwrapv", str(SOURCE), "-o", str(WORK/"reference")], check=True)
    reference = subprocess.check_output([str(WORK/"reference")], text=True, timeout=90)
    assert reference == expected_output()
    (WORK/"reference-output.txt").write_text(reference)
    configurations = {mode: compile_run(mode) for mode in MODES}
    dispatch = {mode: branch_probe(mode, WORK/mode) for mode in ["identity", "interchange", "tile-2-3"]}
    report = bindings() | {"configurations":configurations, "clight_dispatch":dispatch,
                          "reference_sha256":sha(WORK/"reference-output.txt"),
                          "assembly_calls":len(CASES)*len(MODES), "clight_dispatch_calls":len(CASES)*3,
                          "new_machine_dispatch_probes":False, "cost_or_profitability_measured":False}
    validate(report)
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"passed", "assembly_calls":report["assembly_calls"],
                      "clight_calls":report["clight_dispatch_calls"], "report_sha256":sha(WORK/"report.json")},indent=2))


if __name__ == "__main__":
    main()
