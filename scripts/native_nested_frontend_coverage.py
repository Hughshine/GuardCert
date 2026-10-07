"""Exercise array bodies and program contexts at the actual nested compiler entry."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body
import native_nested_frontend as frontend

WORK = ROOT / "build/nested-frontend/coverage"
SOURCE = ROOT / "examples/native_nested_frontend_coverage.c"
NAMES = ["nested_accum", "nested_multi", "nested_chain", "nested_write",
         "nested_undefined", "nested_twice", "nested_context"]
MODES = ["disabled", "identity", "interchange", "tile-2-3", "wrong-reindex", "invalid-domain"]
SIZE, CENTER = 2048, 128
HELPERS = ["scripts/native_nested_frontend_coverage.py", *frontend.HELPERS]


def word(value):
    return (value + 2**31) % 2**32 - 2**31


def cases():
    result = []
    for kind in range(len(NAMES)):
        shapes = [(0, 2, 2, 1), (0, 2, 3, 1), (1, 2, 2, 1), (-1, 2, 2, 1),
                  (3, 2, 2, 1), (0, 0, 0, 1), (0, 2, 0, 1),
                  (0, 4, 2, 1), (0, 2, 4, 1), (0, -1, 99, 2**31-1),
                  (0, 2, 2, 2**31-1), (0, 2, 2, -2**31)]
        result += [(kind, 0, start, u, v, alpha, 1) for start, u, v, alpha in shapes]
        result += [(kind, 7, 0, -1, 99, 2**31-1, 1),
                   (kind, 7, 0, 2**31-1, 99, 2**31-1, 1),
                   (kind, 8, 0, 2, -1, 2**31-1, 1),
                   (kind, 8, 0, 2, 2**31-1, 2**31-1, 1)]
    result += [(1, view, 0, 2, 3, 1, 1) for view in [3, 4, 5]]
    result += [(3, view, 0, 2, 2, 1, 1) for view in [1, 2]]
    result += [(6, 0, 0, 2, 3, 1, take) for take in [0, 2]]
    return result


def run_model(args, *, traversal="source"):
    kind, view, start, u, v, alpha, take = args
    arrays = {"A": [word(3*x+1) for x in range(3*SIZE)],
              "B": [word(3*x+18) for x in range(SIZE)],
              "C": [word(3*x+35) for x in range(SIZE)], "D": [u, v]}
    a, b, c, shape = ("A", CENTER), ("B", CENTER), ("C", CENTER), ("D", 0)
    if view in [1, 2]:
        shape = ("A", CENTER + (0 if view == 1 else 5))
        arrays["A"][shape[1]:shape[1]+2] = [u, v]
    elif view == 3:
        b = c = a
    elif view == 4:
        b, c = ("A", CENTER+1024), ("A", CENTER+2048)
    elif view == 5:
        b, c = ("A", CENTER+1), ("A", CENTER+2)
    elif view == 7:
        arrays["D"] = [u]
    public, markers, visited = [start, 77, 91], [100, 200], []

    def header(index):
        assert index < len(arrays[shape[0]])-shape[1], (args, "unreadable header", index)
        return arrays[shape[0]][shape[1]+index]

    def read(pointer, index):
        assert view not in [7, 8], (args, "null body pointer reached")
        offset = pointer[1]+index
        assert 0 <= offset < len(arrays[pointer[0]]), (args, pointer, index)
        return arrays[pointer[0]][offset]

    def visit(point):
        row, column, component = point
        index = 80*row+5*column+component
        if kind == 3:
            value = 1
        elif kind == 1:
            value = read(b, index)+read(c, index)+alpha+row-column+component
        else:
            value = read(a, index+(75 if kind == 2 else 0))+alpha+row-column+component
        read(a, index)  # validate the actual write allocation too
        arrays[a[0]][a[1]+index] = word(value)
        visited.append(point)

    if kind == 6:
        markers[0] += 7
        if not take:
            public = [-7, -8, -9]
    if kind != 6 or take:
        for repetition in range(2 if kind == 5 else 1):
            if repetition:
                public[0] = 0
            staged = []
            while public[0] < word(header(0)+1):
                assert -2 <= public[0] < 32, (args, "model root runaway")
                public[1] = 0
                while public[1] < word(header(1)+1):
                    assert public[1] < 32, (args, "model child runaway")
                    public[2] = 0
                    while public[2] < 5:
                        point = tuple(public)
                        if traversal == "source":
                            visit(point)
                        else:
                            assert view == 0, "counterexamples use independent headers"
                            staged.append(point)
                        public[2] += 1
                    public[1] += 1
                public[0] += 1
            if traversal != "source":
                key = ((lambda q: (q[1], q[0], q[2])) if traversal == "interchange" else
                       (lambda q: (q[0]//2, q[1]//3, q[0], q[1], q[2])))
                for point in sorted(staged, key=key):
                    visit(point)
        if kind == 6:
            markers[1] += 19 if take == 2 else 11
    values = [*args, *public, *markers, header(0), 99 if view == 7 else header(1),
              *arrays["A"], *arrays["B"], *arrays["C"]]
    return " ".join(map(str, values))+"\n", visited


def expected_output():
    return "".join(run_model(row)[0] for row in cases())


def literal(value):
    return "(-2147483647-1)" if value == -2**31 else str(value)


def source_text():
    text = "/* Nested loaded-header frontend coverage; not a benchmark. */\n#include <stdio.h>\n"
    text += "int nc_row,nc_column,nc_component,nc_pre,nc_post;\n"
    for kind, name in enumerate(NAMES):
        parameter = "local_alpha" if kind == 4 else "alpha"
        prefix = ("int local_alpha;if(start<shape[0]+1 && shape[1]+1>0)local_alpha=alpha;" if kind == 4 else "")
        if kind == 6:
            prefix = "nc_pre=nc_pre+7;if(!take){nc_row=-7;nc_column=-8;nc_component=-9;return;}"
        index = "80*row+5*column+component"
        rhs = ("1" if kind == 3 else f"b[{index}]+c[{index}]+{parameter}+row-column+component" if kind == 1 else
               f"a[{index}{'+75' if kind == 2 else ''}]+{parameter}+row-column+component")
        loop = ("for(;row<shape[0]+1;row++)for(column=0;column<shape[1]+1;column++)"
                f"for(component=0;component<5;component++)a[{index}]={rhs};")
        loops = loop+("row=0;"+loop if kind == 5 else "")
        suffix = "nc_row=row;nc_column=column;nc_component=component;"
        if kind == 6:
            suffix += "if(take==2){nc_post=nc_post+19;return;}nc_post=nc_post+11;"
        text += (f"void {name}(int *a,int *b,int *c,int *shape,int start,int alpha,int take){{"
                 f"int row=start,column=77,component=91;{prefix}{loops}{suffix}}}\n")
    text += """void nested_case(int kind,int view,int start,int u,int v,int alpha,int take){
int A[6144],B[2048],C[2048],dims[2],single[1],x;int *a,*b,*c,*shape;
for(x=0;x<6144;x++)A[x]=3*x+1;for(x=0;x<2048;x++){B[x]=3*x+18;C[x]=3*x+35;}
a=A+128;b=B+128;c=C+128;dims[0]=u;dims[1]=v;single[0]=u;shape=dims;
if(view==1){shape=a;shape[0]=u;shape[1]=v;}if(view==2){shape=a+5;shape[0]=u;shape[1]=v;}
if(view==3){b=a;c=a;}if(view==4){b=a+1024;c=a+2048;}if(view==5){b=a+1;c=a+2;}
if(view==7){shape=single;a=0;b=0;c=0;}if(view==8){a=0;b=0;c=0;}
nc_pre=100;nc_post=200;
"""
    for kind, name in enumerate(NAMES):
        text += f"if(kind=={kind}){name}(a,b,c,shape,start,alpha,take);\n"
    text += """printf("%d %d %d %d %d %d %d %d %d %d %d %d %d %d",kind,view,start,u,v,alpha,take,nc_row,nc_column,nc_component,nc_pre,nc_post,shape[0],view==7?99:shape[1]);
for(x=0;x<6144;x++)printf(" %d",A[x]);for(x=0;x<2048;x++)printf(" %d",B[x]);for(x=0;x<2048;x++)printf(" %d",C[x]);printf("\\n");}
int main(void){
"""
    text += "\n".join("nested_case("+",".join(map(literal, row))+");" for row in cases())
    return text+"return 0;}\n"


def counterexamples():
    row = (2, 0, 0, 2, 3, 1, 1)
    original = run_model(row)[0]
    result = {}
    for mode in ["interchange", "tile-2-3"]:
        changed = run_model(row, traversal=mode)[0]
        assert changed != original, (mode, "missing genuine dependence witness")
        before, after = list(map(int, original.split())), list(map(int, changed.split()))
        different = [(i-14, a, b) for i, (a, b) in enumerate(zip(before, after)) if a != b]
        result[mode] = {"case": row, "different_output_words": len(different), "first_difference": different[0]}
    return result


def counterexample_source(mode):
    text = source_text().split("int main(void){", 1)[0]
    body = function_body(text, "nested_chain")
    first, last = body.index("for(;row<shape[0]+1;"), body.index("nc_row=row;")
    store = "a[80*row+5*column+component]=a[80*row+5*column+component+75]+alpha+row-column+component;"
    if mode == "interchange":
        loop = ("for(column=0;column<shape[1]+1;column++)for(row=start;row<shape[0]+1;row++)"
                "for(component=0;component<5;component++)"+store)
    else:
        assert mode == "tile-2-3"
        loop = ("int tile_row,tile_column;"
                "for(tile_row=0;tile_row<shape[0]+1;tile_row=tile_row+2)"
                "for(tile_column=0;tile_column<shape[1]+1;tile_column=tile_column+3)"
                "for(row=tile_row;row<tile_row+2 && row<shape[0]+1;row++)"
                "for(column=tile_column;column<tile_column+3 && column<shape[1]+1;column++)"
                "for(component=0;component<5;component++)"+store)
    changed = body[:first]+loop+"row=shape[0]+1;column=shape[1]+1;component=5;"+body[last:]
    assert text.count(body) == 1
    text = text.replace(body, changed, 1)
    return text+"int main(void){nested_case(2,0,0,2,3,1,1);return 0;}\n"


def run_counterexample(mode):
    directory = WORK/"counterexamples"/mode
    directory.mkdir(parents=True, exist_ok=True)
    path = directory/"forced.c"
    path.write_text(counterexample_source(mode))
    env = {key:value for key,value in os.environ.items() if not key.startswith("GUARDCERT_")}
    env.update(GUARDCERT_AFFINE_MODE="disabled")
    with (directory/"compile.log").open("w") as log:
        subprocess.run([str(frontend.COMPILER), "-conf", str(frontend.COMPILER.parent/"compcert.ini"),
                        "-stdlib", str(frontend.COMPILER.parent/"runtime"), "-S", "-o",
                        str(directory/"program.s"), str(path)], cwd=directory,env=env,stdout=log,
                       stderr=subprocess.STDOUT,check=True,timeout=300)
    subprocess.run(["gcc","-no-pie",str(directory/"program.s"),"-o",str(directory/"program")],check=True)
    output = subprocess.check_output([str(directory/"program")],text=True,timeout=90)
    (directory/"output.txt").write_text(output)
    row = (2,0,0,2,3,1,1)
    assert output == run_model(row,traversal=mode)[0] and output != run_model(row)[0], mode
    print("Unguarded assembly counterexample:",mode,counterexamples()[mode],flush=True)
    return {"calls":1,"unguarded_rewrite_changes_source_behavior":True,
            "artifacts":{name:sha(directory/name) for name in ["forced.c","compile.log","program.s","program","output.txt"]}}


def installation_expected(mode, name):
    return mode in ["identity","interchange","tile-2-3"] and not (
        name == "nested_chain" and mode in ["interchange","tile-2-3"])


def compile_run(mode, *, directory=None, bound_high=5):
    directory = Path(directory) if directory is not None else WORK / mode
    directory.mkdir(parents=True, exist_ok=True)
    env = {key: value for key, value in os.environ.items() if not key.startswith("GUARDCERT_")}
    env.update(GUARDCERT_AFFINE_MODE=mode, GUARDCERT_AFFINE_CAP="4", GUARDCERT_AFFINE_BOUND_LOW="1",
               GUARDCERT_AFFINE_BOUND_HIGH=str(bound_high), GUARDCERT_AFFINE_DIAGNOSTICS="1")
    with (directory / "compile.log").open("w") as log:
        subprocess.run([str(frontend.COMPILER), "-conf", str(frontend.COMPILER.parent/"compcert.ini"),
                        "-stdlib", str(frontend.COMPILER.parent/"runtime"), "-dclight", "-S", "-o",
                        str(directory/"program.s"), str(SOURCE)], cwd=directory, env=env, stdout=log,
                       stderr=subprocess.STDOUT, check=True, timeout=300)
    subprocess.run(["gcc", "-no-pie", str(directory/"program.s"), "-o", str(directory/"program")], check=True)
    output = subprocess.check_output([str(directory/"program")], text=True, timeout=90)
    (directory/"output.txt").write_text(output)
    assert output == expected_output(), mode
    dump = directory/(SOURCE.stem+".light.c")
    functions = {}
    for kind, name in enumerate(NAMES):
        body = function_body(dump.read_text(), name)
        loops = body.count("for (")
        baseline = 6 if kind == 5 else 3
        functions[name] = {"loops": loops, "installed": loops > baseline,
                           "machine_bytes": frontend.machine_bytes(directory/"program", name)}
    print(mode, functions, flush=True)
    return {"functions": functions, "calls": len(cases()),
            "range_policy":{"root_cap":4,"bound_lower":1,"bound_upper_exclusive":bound_high},
            "artifacts": {path: sha(directory/path) for path in ["compile.log", "program.s", "program", dump.name, "output.txt"]}}


def validate():
    frontend.check_build()
    report = json.loads((WORK/"report.json").read_text())
    assert report["status"] == "passed" and report["source_sha256"] == sha(SOURCE)
    assert SOURCE.read_text() == source_text()
    assert report["compiler_sha256"] == sha(frontend.COMPILER)
    assert report["proved_entrypoint"] == frontend.ENTRY
    assert report["stamp_sha256"] == sha(frontend.COMPILER.parent/".guard-build.json")
    assert report["proof_report_sha256"] == sha(frontend.PROOF)
    assert report["cases"] == [list(row) for row in cases()]
    assert report["words_per_array"] == {"A":6144,"B":2048,"C":2048}
    assert set(report["helper_sources"]) == set(HELPERS)
    for path, digest in report["helper_sources"].items():
        assert sha(ROOT/path) == digest, path
    assert report["counterexamples"] == json.loads(json.dumps(counterexamples()))
    assert report["reference_sha256"] == sha(WORK/"reference-output.txt")
    assert (WORK/"reference-output.txt").read_text() == expected_output()
    assert set(report["configurations"]) == set(MODES)
    for mode, facts in report["configurations"].items():
        directory = WORK/mode
        assert facts["calls"] == len(cases())
        assert facts["range_policy"] == {"root_cap":4,"bound_lower":1,"bound_upper_exclusive":5}
        for path, digest in facts["artifacts"].items():
            assert sha(directory/path) == digest, (mode, path)
        assert (directory/"output.txt").read_text() == expected_output()
        dump = directory/(SOURCE.stem+".light.c")
        assert set(facts["functions"]) == set(NAMES)
        assert (directory/"compile.log").read_text().count("indexed=true exact=true checked=true depth=3") == 8
        for name, values in facts["functions"].items():
            body = function_body(dump.read_text(), name)
            assert values["loops"] == body.count("for (")
            baseline = 6 if name == "nested_twice" else 3
            assert values["installed"] == (values["loops"]>baseline) == installation_expected(mode,name)
            assert "$row < *($shape + 0) + 1" in body and "$column < *($shape + 1) + 1" in body
            assert values["machine_bytes"] == frontend.machine_bytes(directory/"program", name)
    assert report["new_assembly_calls"] == sum(f["calls"] for f in report["configurations"].values()) == 714
    assert set(report["unguarded_counterexample_assembly"]) == {"interchange","tile-2-3"}
    for mode,facts in report["unguarded_counterexample_assembly"].items():
        directory = WORK/"counterexamples"/mode
        assert (directory/"forced.c").read_text() == counterexample_source(mode)
        for path,digest in facts["artifacts"].items():
            assert sha(directory/path) == digest,(mode,path)
        output = (directory/"output.txt").read_text()
        row = (2,0,0,2,3,1,1)
        assert output == run_model(row,traversal=mode)[0] and output != run_model(row)[0]
        assert facts["calls"] == 1 and facts["unguarded_rewrite_changes_source_behavior"]
    assert not report["timing_or_profitability_measured"]
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-source", action="store_true")
    parser.add_argument("--reference", action="store_true")
    parser.add_argument("--mode", choices=MODES)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.write_source:
        SOURCE.write_text(source_text())
        print("Wrote", SOURCE, "cases", len(cases()), "counterexamples", counterexamples())
        return
    if args.validate:
        validate()
        print(json.dumps({"status":"validated", "report_sha256":sha(WORK/"report.json")},indent=2))
        return
    frontend.check_build()
    assert SOURCE.read_text() == source_text()
    WORK.mkdir(parents=True, exist_ok=True)
    subprocess.run(["gcc", "-O0", "-fwrapv", str(SOURCE), "-o", str(WORK/"reference")],check=True)
    output = subprocess.check_output([str(WORK/"reference")],text=True,timeout=90)
    assert output == expected_output(), "GCC/source-word model mismatch"
    (WORK/"reference-output.txt").write_text(output)
    if args.reference:
        print("Reference agrees:",len(cases()),"calls;",counterexamples())
        return
    modes = [args.mode] if args.mode else MODES
    configurations = {mode:compile_run(mode) for mode in modes}
    if args.mode:
        return
    for mode, facts in configurations.items():
        for name, values in facts["functions"].items():
            expected = installation_expected(mode,name)
            assert values["installed"] == expected, (mode,name,values,expected)
    unguarded = {mode:run_counterexample(mode) for mode in ["interchange","tile-2-3"]}
    report = {"status":"passed", "proved_entrypoint":frontend.ENTRY,
              "compiler_sha256":sha(frontend.COMPILER), "stamp_sha256":sha(frontend.COMPILER.parent/".guard-build.json"),
              "proof_report_sha256":sha(frontend.PROOF),"cases":[list(row) for row in cases()],
              "words_per_array":{"A":6144,"B":2048,"C":2048},
              "source_sha256":sha(SOURCE), "helper_sources":{path:sha(ROOT/path) for path in HELPERS},
              "configurations":configurations, "new_assembly_calls":len(cases())*len(modes),
              "counterexamples":counterexamples(), "reference_sha256":sha(WORK/"reference-output.txt"),
              "unguarded_counterexample_assembly":unguarded,
              "timing_or_profitability_measured":False, "dispatch_path_evidence_pending":True}
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    validate()
    print(json.dumps({"status":"passed","calls":report["new_assembly_calls"],"report_sha256":sha(WORK/"report.json")},indent=2))


if __name__ == "__main__":
    main()
