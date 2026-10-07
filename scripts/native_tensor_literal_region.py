"""Run literal-bound tensor regions through the proved compiler, including refusal, public exits and contexts."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_nested_frontend import machine_bytes
from native_zero_trip import function_body
from native_affine_nest_paths import closing_brace
from native_memory_layout_sequence_paths import printer_for_gcc

WORK = ROOT / "build/tensor-literal-region/native"
COMPILER = ROOT / "build/tensor-literal-region/compiler/ccomp"
PROOF = ROOT / "build/tensor-literal-region/proof/report.json"
ENTRY = "ClightTensorLiteralCompiler.compile_tensor_literal_regions"
SOURCE = WORK / "tensor_regions.c"
MODES = ["disabled", "identity", "interchange", "tile-2-3", "wrong-reindex", "zero-tile", "wrong-coordinates", "wrong-literal"]
INSTALLED = ["identity", "interchange", "tile-2-3"]
SPECIFICATIONS = [
    ("tensor_single", True, 0, 5), ("tensor_twice", True, 1, 5), ("tensor_context", True, 2, 5),
    ("tensor_row_single", False, 0, 5), ("tensor_row_twice", False, 1, 5), ("tensor_row_context", False, 2, 5),
    ("tensor_three", True, 0, 3), ("tensor_row_three", False, 0, 3),
    ("tensor_zero", True, 0, 0), ("tensor_row_zero", False, 0, 0),
    ("tensor_six", True, 0, 6), ("tensor_row_six", False, 0, 6),
]
NAMES = [spec[0] for spec in SPECIFICATIONS]
SIZE, CENTER = 6144, 128
INPUTS = [(0, 3, 31, 2, 5, 7), (0, 2, 3, 2, 5, 2**31-1),
          (0, 2, 31, 32, 5, -2), (0, 2, 31, 2, 6, 1),
          (1, 3, 31, 2, 5, 3), (0, 0, 1001, 99, 99, 2**31-1),
          (0, 3, 31, 0, 5, 7), (0, 1, 1001, 2, 5, 7),
          (0, 33, 1, 1, 1, 7), (0, 3, 31, 2, 0, 7),
          (0, 3, 31, 2, 5, -2**31), (4, 3, 31, 2, 5, 7)]
CASES = [(kind, *values) for kind in range(len(SPECIFICATIONS)) for values in INPUTS]
HELPERS = ["scripts/native_tensor_literal_region.py", "scripts/native_nested_frontend.py",
           "scripts/native_zero_trip.py", "scripts/native_affine_nest_paths.py",
           "scripts/native_memory_layout_sequence_paths.py", "scripts/audit_interface_clight.py"]


def word(value):
    return (value+2**31) % 2**32-2**31


def literal(value):
    return "(-2147483647-1)" if value == -2**31 else str(value)


def model(case):
    kind, start, n, ld, columns, components, alpha = case
    _name, column_order, kind, upper = SPECIFICATIONS[kind]
    array = [word(3*x+1) for x in range(SIZE)]
    public = [start, 77, 88]
    first = public[:]
    if kind == 2:
        array[900] = word(array[900]+7)
    if not (kind == 2 and start == 4):
        for repeat in range(2 if kind == 1 else 1):
            public = [start, 77, 88]
            value = word(alpha+repeat)
            while public[0] < n:
                public[1] = 0
                while public[1] < columns:
                    public[2] = 0
                    while public[2] < upper:
                        i, j, k = public
                        major, minor = (j, i) if column_order else (i, j)
                        index = CENTER+word(word(word(major*ld)+minor)*5+k)
                        assert 0 <= index < SIZE, (case, index)
                        array[index] = word(array[index]+value)
                        public[2] += 1
                    public[1] += 1
                public[0] += 1
            if repeat == 0:
                first = public[:]
    if kind == 2:
        array[900] = word(array[900]+11)
    return " ".join(map(str, [*case, *public, *first, 107, 211, *array]))+"\n"


def expected_output():
    return "".join(model(case) for case in CASES)


def source_text():
    text = '#include <stdio.h>\nint tensor_i,tensor_j,tensor_k,tensor_first_i,tensor_first_j,tensor_first_k,tensor_pre,tensor_post;\n'
    loop = ("for(;i<n;i++)for(j=0;j<columns;j++)for(k=0;k<UPPER;k++)"
            "a[((i*ld)+j)*5+k]=a[((i*ld)+j)*5+k]+VALUE;\n")
    for name, column_order, kind, upper in SPECIFICATIONS:
        actual_loop = loop.replace("UPPER", str(upper))
        if column_order:
            actual_loop = actual_loop.replace("((i*ld)+j)", "((j*ld)+i)")
        text += (f"void {name}(int*a,int n,int ld,int columns,int components,int alpha,int start){{"
                 "int i=start,j=77,k=88,fi=start,fj=77,fk=88,beta=alpha+1;"
                 "tensor_pre=tensor_pre+7;\n")
        if kind == 2:
            text += "a[772]=a[772]+7;if(start==4)goto finish;\n"
        text += actual_loop.replace("VALUE", "alpha")+"fi=i;fj=j;fk=k;\n"
        if kind == 1:
            text += "i=start;j=77;k=88;\n"+actual_loop.replace("VALUE", "beta")
        if kind == 2:
            text += "finish:a[772]=a[772]+11;\n"
        text += ("tensor_i=i;tensor_j=j;tensor_k=k;tensor_first_i=fi;tensor_first_j=fj;tensor_first_k=fk;"
                 "tensor_post=tensor_post+11;}\n")
    text += ('void tensor_case(int kind,int start,int n,int ld,int columns,int components,int alpha){\n'
             'int A[6144],x;for(x=0;x<6144;x++)A[x]=3*x+1;tensor_pre=100;tensor_post=200;\n')
    for selected, (name, _column, kind, upper) in enumerate(SPECIFICATIONS):
        pointer = "A+128"
        if kind == 0:
            pointer = "(n==0?0:A+128)" if upper > 0 else "0"
        text += f"if(kind=={selected}){name}({pointer},n,ld,columns,components,alpha,start);\n"
    text += ('printf("%d %d %d %d %d %d %d %d %d %d %d %d %d %d %d",kind,start,n,ld,columns,components,alpha,\n'
             'tensor_i,tensor_j,tensor_k,tensor_first_i,tensor_first_j,tensor_first_k,tensor_pre,tensor_post);\n'
             'for(x=0;x<6144;x++)printf(" %d",A[x]);printf("\\n");}\n')
    return text+"int main(void){"+"".join("tensor_case("+",".join(map(literal,case))+");" for case in CASES)+"return 0;}\n"


def expected_dispatch(mode, case):
    kind, start, n, ld, columns, components, _alpha = case
    _name, column_order, kind, upper = SPECIFICATIONS[kind]
    if mode not in INSTALLED or kind == 2 and start == 4:
        return [0, 0]
    accepted = (start == 0 and 1 <= n <= 32 and 1 <= columns <= 32 and
                1 <= upper <= 5 and 1 <= ld < 1000 and (n if column_order else columns) <= ld)
    count = 2 if kind == 1 else 1
    return [count*int(accepted), count*int(not accepted)]


def check_build():
    stamp = json.loads((COMPILER.parent/".guard-build.json").read_text())
    proof = json.loads(PROOF.read_text())
    assert stamp["proved_entrypoint"] == proof["whole_program_entrypoint"] == ENTRY
    assert proof["status"] == "compiled" and not proof["additional_global_axioms"]
    checks = {COMPILER: stamp["compiler_sha256"], PROOF: stamp["proof_report_sha256"],
              COMPILER.parent/"driver/Driver.ml": stamp["driver_sha256"],
              COMPILER.parent/"extract_tensor_regions.v": stamp["extraction_sha256"],
              ROOT/"scripts/build_tensor_literal_region_compiler.py": stamp["build_script_sha256"]}
    checks |= {ROOT/p: digest for p, digest in (stamp["proof_sources"] | stamp["native_sources"] | stamp["build_helpers"]).items()}
    checks |= {(ROOT/p).with_suffix(".vo"): digest for p, digest in proof["compiled_objects"].items()}
    checks |= {ROOT/p: digest for p, digest in proof["helpers"].items()}
    for path, digest in checks.items():
        assert sha(path) == digest, path


def compile_run(mode):
    directory = WORK/mode
    directory.mkdir(parents=True, exist_ok=True)
    env = {k: v for k, v in os.environ.items() if not k.startswith("GUARDCERT_")}
    env.update(GUARDCERT_TENSOR_MODE=mode, GUARDCERT_TENSOR_DIAGNOSTICS="1")
    with (directory/"compile.log").open("w") as out:
        subprocess.run([str(COMPILER), "-conf", str(COMPILER.parent/"compcert.ini"),
                        "-stdlib", str(COMPILER.parent/"runtime"), "-dclight", "-S", "-o",
                        str(directory/"program.s"), str(SOURCE)], cwd=directory, env=env,
                       check=True, stdout=out, stderr=subprocess.STDOUT, timeout=600)
    subprocess.run(["gcc", "-no-pie", str(directory/"program.s"), "-o", str(directory/"program")], check=True)
    output = subprocess.check_output([str(directory/"program")], text=True, timeout=90)
    (directory/"output.txt").write_text(output)
    assert output == expected_output(), mode
    dump = (directory/(SOURCE.stem+".light.c")).read_text()
    functions = {}
    for kind, name in enumerate(NAMES):
        body = function_body(dump, name)
        sites = len(list(dispatch_sites(body)))
        assert sites == ((2 if SPECIFICATIONS[kind][2] == 1 else 1) if mode in INSTALLED else 0), (mode, name, sites)
        assert_raw_literal(body, SPECIFICATIONS[kind][3], mode in INSTALLED)
        functions[name] = {"installed_sites": sites, "machine_bytes": machine_bytes(directory/"program", name),
                           "raw_literal_fallback_checked": True}
    return {"calls": len(CASES), "functions": functions,
            "artifacts": {name: sha(directory/name) for name in
                          ["compile.log", "program.s", "program", "output.txt", SOURCE.stem+".light.c"]}}


def dispatch_sites(body):
    for match in re.finditer(r"if \(\$[0-9]+\) \{", body):
        opening = match.end()-1
        end = closing_brace(body, opening)
        no = re.match(r"\s*else\s*\{", body[end+1:])
        if no is None:
            continue
        fallback = end+1+no.end()-1
        finish = closing_brace(body, fallback)
        if "$i < $n" in body[fallback:finish] and "*($a" in body[opening:end]:
            yield opening, fallback


def assert_raw_literal(body, upper, installed):
    pattern = r"\$k\s*<\s*"+str(upper)+r"\b"
    if installed:
        sites = list(dispatch_sites(body))
        assert sites
        for _yes, no in sites:
            assert re.search(pattern, body[no:closing_brace(body, no)]), (upper, body[no:no+300])
    else:
        assert re.search(pattern, body), (upper, body[:500])


def branch_probe(mode):
    directory = WORK/mode
    source = printer_for_gcc((directory/(SOURCE.stem+".light.c")).read_text())
    for kind, name in enumerate(NAMES):
        body = function_body(source, name)
        sites = list(dispatch_sites(body))
        assert len(sites) == (2 if SPECIFICATIONS[kind][2] == 1 else 1), (mode, name, sites)
        changed = body
        insertions = [(offset+1, code) for yes, no in sites for offset, code in
                      [(yes, "tensor_fast++;"), (no, "tensor_refusal++;")]]
        for offset, code in sorted(insertions, reverse=True):
            changed = changed[:offset]+code+changed[offset:]
        source = source.replace(body, changed, 1)
    source = "int tensor_fast,tensor_refusal;\n"+source
    source += "int main(void){"+"".join("tensor_fast=0;tensor_refusal=0;tensor_case("+
        ",".join(map(literal,case))+');printf("PATH %d %d\\n",tensor_fast,tensor_refusal);' for case in CASES)+"return 0;}\n"
    path = directory/"branches.c"
    path.write_text(source)
    subprocess.run(["gcc", "-O0", "-fwrapv", "-Wno-builtin-declaration-mismatch", "-Wno-discarded-qualifiers",
                    str(path), "-o", str(directory/"branches")], check=True, capture_output=True)
    output = subprocess.check_output([str(directory/"branches")], text=True, timeout=90)
    (directory/"branch-output.txt").write_text(output)
    actual = [list(map(int,line.split()[1:])) for line in output.splitlines() if line.startswith("PATH ")]
    assert actual == [expected_dispatch(mode,case) for case in CASES], (mode, actual)
    assert "\n".join(line for line in output.splitlines() if not line.startswith("PATH "))+"\n" == expected_output()
    return {"calls": len(CASES), "cases_and_dispatch": [[list(case), branch] for case, branch in zip(CASES, actual)],
            "assembly_path_claim": False,
            "artifacts": {name: sha(directory/name) for name in ["branches.c", "branches", "branch-output.txt"]}}


def bindings():
    return {"status": "passed", "proved_entrypoint": ENTRY, "compiler_sha256": sha(COMPILER),
            "proof_report_sha256": sha(PROOF), "stamp_sha256": sha(COMPILER.parent/".guard-build.json"),
            "source_sha256": sha(SOURCE), "specifications": [list(spec) for spec in SPECIFICATIONS], "words_per_call": SIZE, "cases": [list(case) for case in CASES],
            "helpers": {name: sha(ROOT/name) for name in HELPERS}}


def validate(report):
    check_build()
    assert {key: report[key] for key in bindings()} == bindings()
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
        dump = (directory/(SOURCE.stem+".light.c")).read_text()
        for kind, name in enumerate(NAMES):
            values = facts["functions"][name]
            body = function_body(dump, name)
            assert_raw_literal(body, SPECIFICATIONS[kind][3], mode in INSTALLED)
            assert values["raw_literal_fallback_checked"]
            assert values["installed_sites"] == len(list(dispatch_sites(body)))
            assert values["installed_sites"] == ((2 if SPECIFICATIONS[kind][2] == 1 else 1) if mode in INSTALLED else 0)
            assert values["machine_bytes"] == machine_bytes(directory/"program", name)
    assert set(report["clight_dispatch"]) == set(INSTALLED)
    for mode, facts in report["clight_dispatch"].items():
        directory = WORK/mode
        for name, digest in facts["artifacts"].items():
            assert sha(directory/name) == digest, (mode, name)
        assert facts["calls"] == len(CASES) and not facts["assembly_path_claim"]
        assert facts["cases_and_dispatch"] == [[list(case), expected_dispatch(mode,case)] for case in CASES]
        output = (directory/"branch-output.txt").read_text().splitlines()
        assert [list(map(int,line.split()[1:])) for line in output if line.startswith("PATH ")] == [expected_dispatch(mode,case) for case in CASES]
        assert "\n".join(line for line in output if not line.startswith("PATH "))+"\n" == expected_output()
    assert report["assembly_calls"] == len(CASES)*len(MODES)
    assert report["clight_dispatch_calls"] == len(CASES)*len(INSTALLED)
    assert not report["new_machine_dispatch_probes"] and not report["cost_or_profitability_measured"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate:
        validate(json.loads((WORK/"report.json").read_text()))
        print(json.dumps({"status": "validated", "report_sha256": sha(WORK/"report.json")}))
        return
    check_build()
    WORK.mkdir(parents=True, exist_ok=True)
    SOURCE.write_text(source_text())
    subprocess.run(["gcc", "-O0", "-fwrapv", str(SOURCE), "-o", str(WORK/"reference")], check=True)
    reference = subprocess.check_output([str(WORK/"reference")], text=True, timeout=90)
    assert reference == expected_output()
    (WORK/"reference-output.txt").write_text(reference)
    configurations = {mode: compile_run(mode) for mode in MODES}
    dispatch = {mode: branch_probe(mode) for mode in INSTALLED}
    report = bindings() | {"configurations": configurations, "clight_dispatch": dispatch,
                          "reference_sha256": sha(WORK/"reference-output.txt"),
                          "assembly_calls": len(CASES)*len(MODES), "clight_dispatch_calls": len(CASES)*len(INSTALLED),
                          "new_machine_dispatch_probes": False, "cost_or_profitability_measured": False}
    validate(report)
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status": "passed", "assembly_calls": report["assembly_calls"],
                      "clight_calls": report["clight_dispatch_calls"], "report_sha256": sha(WORK/"report.json")},indent=2))


if __name__ == "__main__":
    main()
