"""Check explicit SCoP selection, identical unmarked sites, and actual guarded C execution."""
import argparse
import json
import os
import re
import subprocess

import audit_selected_regions as proof
import native_tensor_literal_region as prior
from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body
from native_affine_nest_paths import closing_brace
from native_memory_layout_sequence_paths import printer_for_gcc
from native_nested_frontend import machine_bytes

WORK = ROOT / "build/selected-polyhedral-region/native"
COMPILER = ROOT / "build/selected-polyhedral-region/compiler/ccomp"
PROOF = proof.WORK / "report.json"
ENTRY = proof.ENTRY
SOURCE = WORK / "selected_regions.c"
MODES = prior.MODES
INSTALLED = prior.INSTALLED
NAMES = ["selected_one", "selected_mixed", "selected_two", "unmarked", "selected_context", "selected_bad"]
MARKED = [1, 1, 2, 0, 1, 1]
COUNTS = [1, 2, 2, 1, 1, 1]
CASES = [(kind, *values) for kind in range(len(NAMES)) for values in prior.INPUTS]
HELPERS = ["scripts/native_selected_regions.py", "scripts/native_tensor_literal_region.py",
           "scripts/native_nested_frontend.py", "scripts/native_zero_trip.py",
           "scripts/native_affine_nest_paths.py", "scripts/native_memory_layout_sequence_paths.py",
           "scripts/audit_interface_clight.py", "scripts/audit_selected_regions.py"]


def source_text(markers=True):
    text = '#include <stdio.h>\nint tensor_i,tensor_j,tensor_k,tensor_first_i,tensor_first_j,tensor_first_k,tensor_pre,tensor_post;\n'
    loop = ("for(;i<n;i++)for(j=0;j<columns;j++)for(k=0;k<5;k++)"
            "a[((i*ld)+j)*5+k]=a[((i*ld)+j)*5+k]+alpha;\n")
    for kind, name in enumerate(NAMES):
        text += (f"void {name}(int*a,int n,int ld,int columns,int components,int alpha,int start){{"
                 "int i=start,j=77,k=88,fi=start,fj=77,fk=88;"
                 "tensor_pre=tensor_pre+7;\n")
        if kind == 4:
            text += "a[772]=a[772]+7;if(start==4)goto finish;\n"
        if kind == 3:
            # A source label resembling a marker must neither be selected nor
            # collide with the frontend's freshly generated marker identities.
            text += "__guardcert_scop_1:\n"
        for repeat in range(COUNTS[kind]):
            if repeat:
                text += "i=start;j=77;k=88;\n"
            selected = kind != 3 and (kind != 1 or repeat == 0)
            if markers and selected:
                text += "#pragma scop\n"
            text += loop.replace("+alpha;", "+alpha+1;" if kind == 5 else "+alpha;")
            if markers and selected:
                text += "#pragma endscop\n"
            if repeat == 0:
                text += "fi=i;fj=j;fk=k;\n"
        if kind == 4:
            text += "finish:a[772]=a[772]+11;\n"
        text += ("tensor_i=i;tensor_j=j;tensor_k=k;tensor_first_i=fi;tensor_first_j=fj;tensor_first_k=fk;"
                 "tensor_post=tensor_post+11;}\n")
    text += ('void tensor_case(int kind,int start,int n,int ld,int columns,int components,int alpha){\n'
             'int A[6144],x;for(x=0;x<6144;x++)A[x]=3*x+1;tensor_pre=100;tensor_post=200;\n')
    for kind, name in enumerate(NAMES):
        pointer = "A+128" if kind == 4 else "(n==0?0:A+128)"
        text += f"if(kind=={kind}){name}({pointer},n,ld,columns,components,alpha,start);\n"
    text += ('printf("%d %d %d %d %d %d %d %d %d %d %d %d %d %d %d",kind,start,n,ld,columns,components,alpha,\n'
             'tensor_i,tensor_j,tensor_k,tensor_first_i,tensor_first_j,tensor_first_k,tensor_pre,tensor_post);\n'
             'for(x=0;x<6144;x++)printf(" %d",A[x]);printf("\\n");}\n')
    return text + "int main(void){" + "".join(
        "tensor_case(" + ",".join(map(prior.literal, case)) + ");" for case in CASES) + "return 0;}\n"


def model(case):
    kind, start, n, ld, columns, components, alpha = case
    array = [prior.word(3*x+1) for x in range(prior.SIZE)]
    public = [start, 77, 88]
    first = public[:]
    if kind == 4:
        array[900] = prior.word(array[900]+7)
    if not (kind == 4 and start == 4):
        for repeat in range(COUNTS[kind]):
            public = [start, 77, 88]
            while public[0] < n:
                public[1] = 0
                while public[1] < columns:
                    public[2] = 0
                    while public[2] < 5:
                        i, j, k = public
                        index = prior.CENTER+prior.word(prior.word(prior.word(i*ld)+j)*5+k)
                        assert 0 <= index < prior.SIZE, case
                        array[index] = prior.word(array[index]+alpha+(kind == 5))
                        public[2] += 1
                    public[1] += 1
                public[0] += 1
            if repeat == 0:
                first = public[:]
    if kind == 4:
        array[900] = prior.word(array[900]+11)
    return " ".join(map(str, [*case, *public, *first, 107, 211, *array]))+"\n"


def expected_output():
    return "".join(model(case) for case in CASES)


def expected_dispatch(mode, case):
    kind, start, n, ld, columns, _components, _alpha = case
    if mode not in INSTALLED or kind in (3, 5) or kind == 4 and start == 4:
        return [0, 0]
    accepted = (start == 0 and 1 <= n <= 32 and 1 <= columns <= 32
                and 1 <= ld < 1000 and columns <= ld)
    return [MARKED[kind]*int(accepted), MARKED[kind]*int(not accepted)]


def check_build():
    proof.validate()
    stamp = json.loads((COMPILER.parent/".guard-build.json").read_text())
    report = json.loads(PROOF.read_text())
    assert stamp["proved_entrypoint"] == report["whole_program_entrypoint"] == ENTRY
    assert stamp["selected_only_discovery_and_installation"]
    assert not stamp["external_scheduler_connected"] and not stamp["prepared_optimizer_connected"]
    checks = {COMPILER: stamp["compiler_sha256"], PROOF: stamp["proof_report_sha256"],
              COMPILER.parent/"driver/Driver.ml": stamp["driver_sha256"],
              COMPILER.parent/"cparser/Parse.ml": stamp["parser_sha256"],
              COMPILER.parent/"extract_tensor_regions.v": stamp["extraction_sha256"],
              ROOT/"scripts/build_selected_region_compiler.py": stamp["build_script_sha256"]}
    checks |= {ROOT/path: digest for path, digest in
               (stamp["proof_sources"] | stamp["native_sources"] | stamp["build_helpers"]).items()}
    for path, digest in checks.items():
        assert sha(path) == digest, path
    return stamp


def compile_run(mode, markers=True):
    name = mode if markers else "unannotated-interchange"
    directory = WORK/name
    directory.mkdir(parents=True, exist_ok=True)
    source = SOURCE if markers else WORK/"unannotated.c"
    env = {key: value for key, value in os.environ.items() if not key.startswith("GUARDCERT_")}
    env.update(GUARDCERT_TENSOR_MODE=mode, GUARDCERT_TENSOR_DIAGNOSTICS="1", GUARDCERT_SCOP_DIAGNOSTICS="1")
    with (directory/"compile.log").open("w") as output:
        subprocess.run([str(COMPILER), "-conf", str(COMPILER.parent/"compcert.ini"),
                        "-stdlib", str(COMPILER.parent/"runtime"), "-dclight", "-S", "-o",
                        str(directory/"program.s"), str(source)], cwd=directory, env=env,
                       stdout=output, stderr=subprocess.STDOUT, check=True, timeout=600)
    subprocess.run(["gcc", "-no-pie", str(directory/"program.s"), "-o", str(directory/"program")], check=True)
    output = subprocess.check_output([str(directory/"program")], text=True, timeout=90)
    (directory/"output.txt").write_text(output)
    assert output == expected_output(), name
    dump = (directory/(source.stem+".light.c")).read_text()
    manifest = re.findall(r"GUARDCERT_SCOP label=(\S+) file=(\S+) begin=(\d+) end=(\d+) statements=(\d+)",
                          (directory/"compile.log").read_text())
    assert len(manifest) == (sum(MARKED) if markers else 0), (name, manifest)
    assert len({row[0] for row in manifest}) == len(manifest)
    assert "__guardcert_scop_1" not in {row[0] for row in manifest}
    functions = {}
    for kind, function in enumerate(NAMES):
        body = function_body(dump, function)
        sites = len(list(prior.dispatch_sites(body)))
        expected = MARKED[kind] if markers and mode in INSTALLED and kind != 5 else 0
        assert sites == expected, (name, function, sites, expected)
        assert re.search(r"\$k\s*<\s*5\b", body), function
        functions[function] = {"installed_sites": sites, "machine_bytes": machine_bytes(directory/"program", function)}
    # The marked and unmarked source loops use the same variables and body in
    # this function. Exactly one dispatch proves installation is site-restricted.
    assert functions["selected_mixed"]["installed_sites"] == (int(markers and mode in INSTALLED))
    return {"calls": len(CASES), "functions": functions, "marker_manifest": manifest,
            "artifacts": {name: sha(directory/name) for name in
                          ["compile.log", "program.s", "program", "output.txt", source.stem+".light.c"]}}


def branch_probe(mode):
    directory = WORK/mode
    source = printer_for_gcc((directory/(SOURCE.stem+".light.c")).read_text())
    for kind, name in enumerate(NAMES):
        body = function_body(source, name)
        sites = list(prior.dispatch_sites(body))
        changed = body
        for offset, code in sorted([(offset+1, code) for yes, no in sites for offset, code in
                                    [(yes, "tensor_fast++;"), (no, "tensor_refusal++;")]], reverse=True):
            changed = changed[:offset]+code+changed[offset:]
        source = source.replace(body, changed, 1)
    source = "int tensor_fast,tensor_refusal;\n"+source
    source += "int main(void){"+"".join("tensor_fast=0;tensor_refusal=0;tensor_case("+
        ",".join(map(prior.literal,case))+');printf("PATH %d %d\\n",tensor_fast,tensor_refusal);' for case in CASES)+"return 0;}\n"
    (directory/"branches.c").write_text(source)
    subprocess.run(["gcc", "-O0", "-fwrapv", "-Wno-builtin-declaration-mismatch", "-Wno-discarded-qualifiers",
                    str(directory/"branches.c"), "-o", str(directory/"branches")], check=True, capture_output=True)
    output = subprocess.check_output([str(directory/"branches")], text=True, timeout=90)
    (directory/"branch-output.txt").write_text(output)
    actual = [list(map(int,line.split()[1:])) for line in output.splitlines() if line.startswith("PATH ")]
    assert actual == [expected_dispatch(mode,case) for case in CASES], (mode, actual)
    assert "\n".join(line for line in output.splitlines() if not line.startswith("PATH "))+"\n" == expected_output()
    return {"calls": len(CASES), "cases_and_dispatch": [[list(case), branch] for case, branch in zip(CASES, actual)],
            "assembly_path_claim": False,
            "artifacts": {name: sha(directory/name) for name in ["branches.c", "branches", "branch-output.txt"]}}


def validate():
    check_build()
    report = json.loads((WORK/"report.json").read_text())
    assert report["status"] == "passed" and report["proved_entrypoint"] == ENTRY
    for path, digest in report["bindings"].items():
        assert sha(ROOT/path) == digest, path
    assert SOURCE.read_text() == source_text() and (WORK/"unannotated.c").read_text() == source_text(False)
    assert not report["external_scheduler_connected"] and not report["prepared_optimizer_connected"]
    for mode, facts in report["configurations"].items():
        directory = WORK/mode
        for name, digest in facts["artifacts"].items():
            assert sha(directory/name) == digest, (mode, name)
        assert (directory/"output.txt").read_text() == expected_output()
        source = SOURCE if mode != "unannotated-interchange" else WORK/"unannotated.c"
        dump = (directory/(source.stem+".light.c")).read_text()
        for kind, name in enumerate(NAMES):
            expected = MARKED[kind] if mode in INSTALLED and kind != 5 else 0
            assert facts["functions"][name]["installed_sites"] == expected
            assert len(list(prior.dispatch_sites(function_body(dump, name)))) == expected
    for mode, facts in report["clight_dispatch"].items():
        directory = WORK/mode
        for name, digest in facts["artifacts"].items():
            assert sha(directory/name) == digest, (mode, name)
        assert facts["cases_and_dispatch"] == [[list(case), expected_dispatch(mode,case)] for case in CASES]
        output = (directory/"branch-output.txt").read_text().splitlines()
        assert [list(map(int,line.split()[1:])) for line in output if line.startswith("PATH ")] == [expected_dispatch(mode,case) for case in CASES]
        assert "\n".join(line for line in output if not line.startswith("PATH "))+"\n" == expected_output()
    assert report["assembly_calls"] == len(CASES)*(len(MODES)+1)
    assert report["clight_dispatch_calls"] == len(CASES)*len(INSTALLED)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate:
        validate()
        print(json.dumps({"status": "validated", "report_sha256": sha(WORK/"report.json")}, indent=2))
        return
    check_build()
    WORK.mkdir(parents=True, exist_ok=True)
    SOURCE.write_text(source_text())
    (WORK/"unannotated.c").write_text(source_text(False))
    subprocess.run(["gcc", "-O0", "-fwrapv", str(SOURCE), "-o", str(WORK/"reference")], check=True)
    output = subprocess.check_output([str(WORK/"reference")], text=True, timeout=90)
    assert output == expected_output()
    (WORK/"reference-output.txt").write_text(output)
    facts, branches = {}, {}
    for mode in MODES:
        print("Checking annotated", mode, flush=True)
        facts[mode] = compile_run(mode)
        if mode in INSTALLED:
            branches[mode] = branch_probe(mode)
    facts["unannotated-interchange"] = compile_run("interchange", False)
    paths = [str(p.relative_to(ROOT)) for p in [COMPILER, COMPILER.parent/".guard-build.json", PROOF,
             SOURCE, WORK/"unannotated.c", WORK/"reference", WORK/"reference-output.txt"]] + HELPERS
    report = {"status": "passed", "proved_entrypoint": ENTRY, "bindings": {path: sha(ROOT/path) for path in paths},
              "configurations": facts, "clight_dispatch": branches,
              "assembly_calls": len(CASES)*(len(MODES)+1), "clight_dispatch_calls": len(CASES)*len(INSTALLED),
              "identical_marked_unmarked_source_sites": True, "fake_label_prefix_unselected": True,
              "multiple_regions_independent": True, "external_scheduler_connected": False,
              "prepared_optimizer_connected": False, "cost_or_profitability_measured": False,
              "scope": "annotation selection and installation using the existing candidate policy; real scheduler/codegen pending"}
    (WORK/"report.json").write_text(json.dumps(report, indent=2)+"\n")
    validate()
    print(json.dumps({"status": "passed", "assembly_calls": report["assembly_calls"],
                      "clight_dispatch_calls": report["clight_dispatch_calls"],
                      "report_sha256": sha(WORK/"report.json")}, indent=2))


if __name__ == "__main__":
    main()
