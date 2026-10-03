"""Check the actual C-to-Asm compiler on multiple dependent C statements."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

from native_memory_tiling import selected
from native_zero_trip import function_body

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "examples" / "native_memory_operations.c"
COMPILER = ROOT / "build" / "compcert-memory-proposed" / "ccomp"
WORK = ROOT / "build" / "native-memory-proposed"
ENTRY = "GuardMemoryProposedCompiler.compile_memory_proposed_regions"
OPERATIONS = {
    "write_update": [("w",37,7),("u",11,19)],
    "update_write": [("u",37,7),("w",11,19)],
    "updates": [("u",37,7),("u",11,19),("u",23,3)],
    "row_mixed": [("w",37,7),("r",11,19),("u",23,3)],
    "duplicate_update": [("u",37,7),("u",37,7),("w",11,19),("u",23,3)]}
for tag in ["goto","global","enclosing","unread_bound"]:
    OPERATIONS[tag] = OPERATIONS["write_update"]
OPERATIONS["other_layout"] = OPERATIONS["row_mixed"]
ACCEPTED = {"operations_" + tag: (15,7,[c for _,c,_ in ops]) if tag == "other_layout"
            else (12,10,[c for _,c,_ in ops]) for tag,ops in OPERATIONS.items()}
REFUSED = ["operations_neighbor","operations_two_arrays"]


def model(tag, start, n, m, extent=120, stride=10):
    a = [-999] * extent
    i,j = start,99
    repeats = 2 if tag == "enclosing" else 1
    for repeat in range(repeats):
        if tag == "enclosing": i = 0
        while i < n:
            j = 0
            while j < m:
                index = i*stride+j
                if tag == "neighbor":
                    a[index] = i*37+j+7
                    a[index] = a[index+1]+i*11+j+19
                elif tag == "array-a": a[index] = i*37+j+7
                elif tag == "array-b": a[index] = i*48+2*j+26
                else:
                    for mode,coefficient,bias in OPERATIONS[tag]:
                        value = i*coefficient+j+bias
                        if mode == "u": value += a[index]
                        if mode == "r": value += a[i*stride]
                        a[index] = value
                j += 1
            i += 1
    return f"{tag} {i} {j} " + " ".join(map(str,a)) + "\n"


def expected_output():
    output = []
    for n in range(13):
        for m in range(11):
            output += [model(tag,0,n,m) for tag in OPERATIONS if tag not in ["other_layout","unread_bound"]]
            output += [model("write_update",2,n,m),model("row_mixed",2,n,m)]
    for n in range(16):
        for m in range(8): output += [model("other_layout",0,n,m,105,7)]
    output += [model("write_update",0,-1,10),model("row_mixed",0,5,-1)]
    output += [model("neighbor",0,10,9),model("array-a",0,12,10),model("array-b",0,12,10),"unread 99 99\n"]
    return "".join(output)


def compile_run(name, environment):
    work = WORK / name
    work.mkdir(parents=True, exist_ok=True)
    result = subprocess.run([str(COMPILER), "-conf", str(COMPILER.parent / "compcert.ini"),
                    "-stdlib", str(COMPILER.parent / "runtime"), "-dclight", "-S",
                    "-o", str(work / "operations.s"), str(SOURCE)],
                   cwd=work, env=os.environ | environment, check=True, capture_output=True,
                   text=True, timeout=180)
    (work / "compiler-output.txt").write_text(result.stdout + result.stderr)
    subprocess.run(["gcc", str(work / "operations.s"), "-o", str(work / "operations")],
                   check=True, text=True, capture_output=True)
    output = subprocess.check_output([str(work / "operations")], text=True)
    if output != expected_output() or output != (WORK / "gcc-output.txt").read_text():
        raise SystemExit(f"C mixed-read/write behavior differs from model or GCC: {name}")
    dumps = list(work.glob("*.light.c"))
    if len(dumps) != 1:
        raise SystemExit(f"expected one Clight dump: {dumps}")
    (work / "output.txt").write_text(output)
    return dumps[0].read_text()


def main():
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    assert stamp["proved_entrypoint"] == ENTRY
    assert stamp["compiler_sha256"] == hashlib.sha256(COMPILER.read_bytes()).hexdigest()
    for path,expected in (stamp["proof_sources"] | stamp["native_sources"]).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == expected,path
    WORK.mkdir(parents=True,exist_ok=True)
    subprocess.run(["gcc","-O0",str(SOURCE),"-o",str(WORK/"gcc-reference")],check=True,capture_output=True)
    reference = subprocess.check_output([str(WORK/"gcc-reference")],text=True)
    assert reference == expected_output()
    (WORK/"gcc-output.txt").write_text(reference)
    results = {}
    templates = ROOT / "examples" / "loop-candidates"
    for name in ["identity","fission","drop-statements","changed-domain","nonaffine",
                 "missing-proposal","resource-limit","invalid-certificate"]:
        environment = {"GUARDCERT_LOOP_CANDIDATE":str(templates/(name+".sexp"))}
        expected = set()
        if name == "identity": expected = set(ACCEPTED)
        if name == "fission": expected = set(ACCEPTED)-{"operations_row_mixed","operations_other_layout"}
        if name == "resource-limit":
            environment = {"GUARDCERT_LOOP_CANDIDATE":str(templates/"fission.sexp"),"GUARDCERT_FM_ROWS":"0"}
        if name == "invalid-certificate":
            environment = {"GUARDCERT_LOOP_CANDIDATE":str(templates/"fission.sexp"),"GUARDCERT_ORACLE_FAULT":"top-certificate"}
        dump = compile_run(name,environment)
        for function,(limit,stride,_) in ACCEPTED.items():
            body = function_body(dump,function)
            if ("switch (0)" in body) != (function in expected):
                raise AssertionError((name,function,body))
            if function in expected:
                checked = re.search(rf"if \(\$m <= {stride}\)",body)
                assert checked
                candidate = body[checked.end():body.find("continue;",checked.end())]
                counters = re.findall(r"for \(; 1; ([^ =;]+) = \1 \+ 1\)",candidate)
                tag = function.removeprefix("operations_")
                assert len(counters) == (2 if name=="identity" else 2*len(OPERATIONS[tag])),(name,function,counters)
                assert "$i = $n;" in candidate and "$j = $m;" in candidate
        for function in REFUSED:
            assert "switch (0)" not in function_body(dump,function),(name,function)
        results[name] = {"guarded_functions":sorted(expected),"all_memory_cells_and_public_exit_match":True,
                         "full_output_lines":len(reference.splitlines())}
    report = {"status":"passed","proved_entrypoint":ENTRY,"configurations":results,
              "compiler_sha256":stamp["compiler_sha256"],"source_sha256":hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
              "candidate_templates_sha256":{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                                             for p in templates.glob("*.sexp")},
              "actual_external_candidate_consumed":True,"actual_dependence_validation_consumed":True,
              "unsafe_row_prefix_fission_refused":True,"candidate_generator_assumed_correct":False,
              "general_c_source_decoder_supported":False,"gcc_and_independent_model_match":True}
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    print("Externally proposed Loop-to-C-to-Asm compiler passed: identity, real loop fission, "
          "eight configurations, unsafe dependence/domain/instruction proposals refused")


if __name__ == "__main__": main()
