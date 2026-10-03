"""Run the guarded C-to-Asm entrypoint on actual multiple array objects."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

from native_zero_trip import function_body
from native_memory_tiling import selected

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "examples" / "native_memory_multiarray.c"
COMPILER = ROOT / "build" / "compcert-memory-unified" / "ccomp"
WORK = ROOT / "build" / "native-memory-multiarray"
ENTRY = "GuardMemoryUnifiedCompiler.compile_memory_unified_regions"
ACCEPTED = {"multi_two","multi_three","multi_global","multi_enclosing",
            "multi_cross_read","multi_cross_read_only","multi_cross_chain","multi_cross_global",
            "multi_copy_read_only","multi_copy_chain"}
REFUSED = {"multi_other_layout","multi_cross_neighbor"}


def model(tag,start,n,m):
    a,b,c = [-999]*120,[-777]*120,[-555]*120
    i,j = start,99
    for repeat in range(2 if tag == "enclosing" else 1):
        if tag == "enclosing": i = 0
        while i < n:
            j = 0
            while j < m:
                index = i*10+j
                a[index] = i*37+j+7
                b[index] += i*11+j+19
                if tag == "three":
                    c[index] = i*13+j+5
                    c[index] = c[i*10]+i*17+j+11
                    c[index] += i*23+j+3
                else: a[index] += i*23+j+3
                j += 1
            i += 1
    arrays = [("a",a),("b",b)]+([("c",c)] if tag == "three" else [])
    return "".join(f"{tag}-{name} {i} {j} "+" ".join(map(str,values))+"\n" for name,values in arrays)


def cross_model(tag,n,m):
    a = ([2147483647 if k%3==0 else -2147483648 if k%3==1 else k*3+1 for k in range(120)]
         if tag == "copy" else [k*3+1 for k in range(120)] if tag == "read" else [-999]*120)
    b,c = [-777]*120,[-555]*120
    i,j = 0,99
    while i < n:
        j = 0
        while j < m:
            index = i*10+j
            if tag not in ["read","copy"]: a[index] = i*37+j+7
            b[index] = a[index+1 if tag == "neighbor" else index]+(0 if tag in ["copy","copy-chain"] else i*11+j+19)
            if tag in ["chain","copy-chain"]: c[index] = b[index]+(0 if tag == "copy-chain" else i*23+j+3)
            j += 1
        i += 1
    arrays = [("a",a),("b",b)]+([("c",c)] if tag in ["chain","copy-chain"] else [])
    return "".join(f"{tag}-{name} {i} {j} "+" ".join(map(str,values))+"\n" for name,values in arrays)


def expected_output():
    result = ""
    for n in range(13):
        for m in range(11):
            result += model("two",0,n,m)+model("three",0,n,m)+model("global",0,n,m)+model("enclosing",0,n,m)
            result += model("two",2,n,m)+model("three",2,n,m)
            result += "".join(cross_model(tag,n,m) for tag in ["cross","read","chain","cross-global","copy","copy-chain"])
    result += model("two",0,-1,10)+model("three",0,5,-1)
    a,b = [-999]*120,[-777]*105
    for i in range(12):
        for j in range(7): a[i*10+j]=i*37+j+7;b[i*7+j]=i*11+j+19
    result += "layout-a 12 7 "+" ".join(map(str,a))+"\nlayout-b 12 7 "+" ".join(map(str,b))+"\n"
    return result+cross_model("neighbor",10,9)+cross_model("cross",-1,10)+cross_model("read",3,-1)+cross_model("copy",3,-1)+cross_model("copy-chain",-1,10)


def compile_run(name,environment):
    work = WORK/name; work.mkdir(parents=True,exist_ok=True)
    run = subprocess.run([str(COMPILER),"-conf",str(COMPILER.parent/"compcert.ini"),
        "-stdlib",str(COMPILER.parent/"runtime"),"-dclight","-S","-o",str(work/"multiarray.s"),str(SOURCE)],
        cwd=work,env=os.environ|environment,text=True,capture_output=True,check=True,timeout=180)
    (work/"compiler-output.txt").write_text(run.stdout+run.stderr)
    subprocess.run(["gcc",str(work/"multiarray.s"),"-o",str(work/"multiarray")],check=True,capture_output=True)
    output = subprocess.check_output([str(work/"multiarray")],text=True)
    assert output == expected_output() == (WORK/"gcc-output.txt").read_text(),name
    (work/"output.txt").write_text(output)
    dumps = list(work.glob("*.light.c")); assert len(dumps)==1,dumps
    return dumps[0].read_text()


def main():
    stamp = json.loads((COMPILER.parent/".guard-build.json").read_text())
    assert stamp["proved_entrypoint"] == ENTRY
    assert stamp["compiler_sha256"] == hashlib.sha256(COMPILER.read_bytes()).hexdigest()
    for path,expected in (stamp["proof_sources"]|stamp["native_sources"]).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==expected,path
    WORK.mkdir(parents=True,exist_ok=True)
    subprocess.run(["gcc","-O0",str(SOURCE),"-o",str(WORK/"gcc-reference")],check=True,capture_output=True)
    reference = subprocess.check_output([str(WORK/"gcc-reference")],text=True)
    assert reference == expected_output()
    (WORK/"gcc-output.txt").write_text(reference)
    configurations = {}
    templates = ROOT/"examples"/"loop-candidates"
    cases = [(name,templates/(name+".sexp"),{},ACCEPTED if name!="fission" else ACCEPTED-{"multi_three"})
             for name in ["identity","interchange","fission","redundant-guard"]]
    for rows,columns in [(1,1),(2,3),(4,4),(17,13)]:
        name = f"tile-{rows}-{columns}"; path = WORK/(name+".sexp");path.write_text(f"(tile {rows} {columns})\n")
        cases.append((name,path,{},ACCEPTED))
    for name,extra in [("resource-limit",{"GUARDCERT_FM_ROWS":"0"}),
                       ("invalid-certificate",{"GUARDCERT_ORACLE_FAULT":"top-certificate"})]:
        cases.append((name,templates/"fission.sexp",extra,set()))
    cases += [(name,templates/(name+".sexp"),{},
               {"multi_cross_read_only","multi_copy_read_only"} if name == "drop-statements" else set()) for name in
              ["wrong-arguments","changed-domain","drop-statements","drop-all-statements","missing-proposal","reverse-dependent"]]
    for name,path,extra,expected in cases:
        dump = compile_run(name,{"GUARDCERT_LOOP_CANDIDATE":str(path)}|extra)
        for function in ACCEPTED:
            body = function_body(dump,function)
            assert ("switch (0)" in body)==(function in expected),(name,function,body)
            if function in expected:
                assert re.search(r"if \([^\n]* != [^\n]*\)",body),(name,function,"missing actual base comparison")
                assert "$i = $n;" in body and "$j = $m;" in body,(name,function,"missing public exits")
                if name.startswith("tile-"):
                    rows,columns = map(int,name.split("-")[1:]);assert selected(body,12,10,rows,columns),(name,function)
        for function in REFUSED: assert "switch (0)" not in function_body(dump,function),(name,function)
        configurations[name] = {"guarded_functions":sorted(expected),"full_output_lines":len(reference.splitlines()),
                                "all_arrays_and_public_exits_match":True}
    report = {"status":"passed","proved_entrypoint":ENTRY,"configurations":configurations,
              "source_sha256":hashlib.sha256(SOURCE.read_bytes()).hexdigest(),"compiler_sha256":stamp["compiler_sha256"],
              "actual_multiple_compcert_array_objects":True,"actual_safe_base_comparisons_emitted":True,
              "two_and_three_arrays":True,"global_and_enclosing_contexts":True,
              "gcc_and_independent_model_match":True,"cross_array_source_reads_supported":True,"direct_array_copy_source_supported":True,
              "read_only_array_registered_and_guarded":True,"unsafe_reversed_cross_dependence_refused":True,
              "arbitrary_pointer_slice_aliasing_supported":False}
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(f"Multiple physical arrays passed: {len(cases)} configurations, {len(reference.splitlines())} output lines each")


if __name__ == "__main__": main()
