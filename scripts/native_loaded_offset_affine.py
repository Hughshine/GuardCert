"""Exercise actual loaded-plus-one roots through the extracted compiler."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

COMPILER = ROOT / "build/loaded-offset-affine/compiler/ccomp"
PROOF = ROOT / "build/loaded-offset-affine/proof/report.json"
WORK = ROOT / "build/loaded-offset-affine/native"
SOURCE = ROOT / "examples/native_loaded_offset_affine.c"
ENTRY = "ClightGuardedLoadedOffsetAffineMultiCompiler.compile_offset_affine_multi_regions"
SIZE, CENTER = 2048, 128
NAMES = ["loaded_accum2", "loaded_accum3", "loaded_multi3", "loaded_chain2",
         "loaded_store3", "loaded_undefined3", "loaded_twice2"]
DEPTHS = [2, 3, 3, 2, 3, 3, 4]


def word(value):
    return (value + 2**31) % 2**32 - 2**31


def cases():
    result = []
    shapes = [(0, 3, 4, 1, 5), (0, 2, 2, 2, -7), (1, 3, 2, 1, 5),
              (-1, 2, 2, 1, 5), (0, 3, 0, 1, 5), (0, 3, 2, 0, 5),
              (0, 9, 2, 1, 5), (0, 2, 2, 1, 2**31-1),
              (0, 2, 2, 1, -2**31)]
    for kind in range(len(NAMES)):
        result += [(kind,7,0,2**31-1,2,1,5), (kind,7,0,-2,2,1,5)]
        for shape in shapes:
            result.append((kind, 0, *shape))
        result += [(kind, 7, 0, -1, 2, 1, 5), (kind, 7, 0, 3, -3, 1, 5),
                   (kind, 3, 0, 3, 2, 1, 5)]
        if kind != 6:
            result.append((kind, 7, 1, 2, 2**31-1, 1, 5))
        if DEPTHS[kind] == 3:
            result += [(kind, 7, 0, 3, 2, -5, 5), (kind, 7, 0, 3, 2, -2**31, 5)]
    for view in [1, 2]:
        result.append((4, view, 0, 3, 4, 1, 5))
    for view in [4, 5, 6]:
        result.append((2, view, 0, 3, 4, 1, 5))
    return result


def run_model(args, *, interchange=False):
    kind, view, start, n, m, p, alpha = args
    arrays = {"A": [word(3*x+1) for x in range(3*SIZE)],
              "B": [word(3*x+18) for x in range(SIZE)],
              "C": [word(3*x+35) for x in range(SIZE)]}
    a, b, c = ("A", CENTER), ("B", CENTER), ("C", CENTER)
    limit = None
    if view in [1, 2, 3]:
        limit = ("A", CENTER + {1: 0, 2: 128, 3: 1800}[view])
        arrays[limit[0]][limit[1]] = n
    if view == 4:
        b = c = a
    elif view == 5:
        b, c = ("A", CENTER+1024), ("A", CENTER+2048)
    elif view == 6:
        b, c = ("A", CENTER+1), ("A", CENTER+2)
    final = [start, 77, 91, 79, 83]
    points = []

    def bound():
        return arrays[limit[0]][limit[1]] if limit else n

    def visit(point):
        i, j, k = point
        index = 128*i + 16*j + (k if DEPTHS[kind] == 3 else 0)
        assert view != 7, (args, point, "null body pointer reached")
        write = a[1] + index
        assert 0 <= write < len(arrays[a[0]]), (args, point)
        if kind == 4:
            value = 1
        elif kind == 2:
            value = arrays[b[0]][b[1]+index] + arrays[c[0]][c[1]+index] + alpha + i-j+k
        else:
            value = arrays[a[0]][write+(112 if kind == 3 else 0)] + alpha+i-j+(k if DEPTHS[kind] == 3 else 0)
        arrays[a[0]][write] = word(value)
        points.append(point)

    for repetition in range(2 if kind == 6 else 1):
        if repetition:
            final[0] = 0
        i = final[0]
        staged = []
        while i < word(bound()+1):
            assert i < 32, (args, "model runaway")
            K = word(i+m)
            final[1], final[3] = 0, K
            for j in range(max(0, K)):
                if DEPTHS[kind] == 3:
                    L = word(j+p)
                    final[2], final[4] = 0, L
                    for k in range(max(0, L)):
                        if interchange:
                            staged.append((i,j,k))
                        else:
                            visit((i,j,k))
                    final[2] = max(0, L)
                elif interchange:
                    staged.append((i,j,0))
                else:
                    visit((i,j,0))
            final[1] = max(0, K)
            i += 1
            final[0] = i
        if interchange:
            assert limit is None
            for point in sorted(staged, key=lambda q: (q[1],q[0],q[2])):
                visit(point)
    values = [*args, *final, bound(), *arrays["A"], *arrays["B"], *arrays["C"]]
    return " ".join(map(str, values))+"\n", points


def expected_output():
    output = "".join(run_model(row)[0] for row in cases())
    return output + "short 2 1 1 1\n"


def literal(value):
    return "(-2147483647-1)" if value == -2**31 else str(value)


def source_text():
    source = "#include <stdio.h>\nint lm_i,lm_j,lm_k,lm_K,lm_L;\n"
    for kind, name in enumerate(NAMES):
        prefix, pv, av = "", "p", "alpha"
        if kind == 5:
            prefix = ("int local_p,local_alpha; if(start<*limit+1 && *limit+m>0)local_p=p; "
                      "if(start<*limit+1 && *limit+m>0 && *limit-1+m+p>0)local_alpha=alpha;")
            pv, av = "local_p", "local_alpha"
        index = "128*i+16*j" + ("+k" if DEPTHS[kind] == 3 else "")
        rhs = ("1" if kind == 4 else
               f"b[{index}]+c[{index}]+{av}+i-j+k" if kind == 2 else
               f"a[{index}{'+112' if kind == 3 else ''}]+{av}+i-j" + ("+k" if DEPTHS[kind] == 3 else ""))
        leaf = f"a[{index}]={rhs};"
        if DEPTHS[kind] == 3:
            leaf = f"L=j+{pv};for(k=0;k<L;k++){{{leaf}}}"
        loop = f"for(;i<*limit+1;i++){{K=i+m;for(j=0;j<K;j++){{{leaf}}}}}"
        loops = loop + ("i=0;"+loop if kind == 6 else "")
        source += (f"void {name}(int *a,int *b,int *c,int *limit,int start,int m,int p,int alpha){{"
                   f"int i=start,j=77,k=91,K=79,L=83;{prefix}{loops}"
                   "lm_i=i;lm_j=j;lm_k=k;lm_K=K;lm_L=L;}\n")
    source += """void loaded_small2(int *a,int *limit){int i=0,j=77,K=79;for(;i<*limit+1;i++){K=1;for(j=0;j<K;j++){a[i+0*j]=1;}}lm_i=i;lm_j=j;}
void loaded_short_run(void){int a[2];a[0]=4;a[1]=3;loaded_small2(a,a+1);printf("short %d %d %d %d\\n",lm_i,lm_j,a[0],a[1]);}
void loaded_case(int kind,int view,int start,int n,int m,int p,int alpha){int A[6144],B[2048],C[2048],x;int *a,*b,*c,*limit;
for(x=0;x<6144;x++)A[x]=3*x+1;for(x=0;x<2048;x++){B[x]=3*x+18;C[x]=3*x+35;}
a=A+128;b=B+128;c=C+128;limit=&n;
if(view==1){limit=a;*limit=n;}if(view==2){limit=a+128;*limit=n;}if(view==3){limit=a+1800;*limit=n;}
if(view==4){b=a;c=a;}if(view==5){b=a+1024;c=a+2048;}if(view==6){b=a+1;c=a+2;}if(view==7){a=0;b=0;c=0;}
"""
    for kind, name in enumerate(NAMES):
        source += f"if(kind=={kind}){name}(a,b,c,limit,start,m,p,alpha);\n"
    source += """printf("%d %d %d %d %d %d %d %d %d %d %d %d %d",kind,view,start,n,m,p,alpha,lm_i,lm_j,lm_k,lm_K,lm_L,*limit);
for(x=0;x<6144;x++)printf(" %d",A[x]);for(x=0;x<2048;x++)printf(" %d",B[x]);for(x=0;x<2048;x++)printf(" %d",C[x]);printf("\\n");}
int main(void){
"""
    for row in cases():
        source += "loaded_case("+",".join(map(literal,row))+");\n"
    return source + "loaded_short_run();return 0;}\n"


def check_build():
    stamp = json.loads((COMPILER.parent/".guard-build.json").read_text())
    proof = json.loads(PROOF.read_text())
    assert stamp["proved_entrypoint"] == ENTRY == proof["whole_program_entrypoint"]
    assert proof["status"] == "compiled" and proof["additional_global_axioms"] == []
    checks = {COMPILER: stamp["compiler_sha256"], COMPILER.parent/"driver/Driver.ml": stamp["driver_sha256"],
              COMPILER.parent/"extract_loaded_offset_affine.v": stamp["extraction_sha256"],
              PROOF: stamp["proof_report_sha256"], ROOT/"scripts/build_loaded_offset_affine.py": stamp["build_script_sha256"],
              ROOT/"scripts/audit_loaded_offset_affine.py": proof["verification_helpers"]["scripts/audit_loaded_offset_affine.py"]}
    checks |= {ROOT/p: digest for p,digest in (stamp["proof_sources"]|stamp["native_sources"]|stamp["build_helpers"]).items()}
    checks |= {(ROOT/p).with_suffix(".vo"): digest for p,digest in proof["compiled_objects"].items()}
    for path,digest in checks.items():
        assert sha(path) == digest, path
    return stamp


def machine_bytes(binary, name):
    symbols = subprocess.check_output(["nm","-S","--defined-only",str(binary)],text=True)
    match = re.search(r"^\w+\s+(\w+)\s+[tT]\s+"+name+r"$",symbols,re.MULTILINE)
    assert match, name
    return int(match.group(1),16)


def compile_run(name, mode, extra, expected):
    work = WORK/name
    work.mkdir(parents=True,exist_ok=True)
    env = {k:v for k,v in os.environ.items() if not k.startswith("GUARDCERT_")}
    env |= {"GUARDCERT_AFFINE_MODE": mode, "GUARDCERT_AFFINE_DIAGNOSTICS": "1",
            "GUARDCERT_AFFINE_PROFILE": "inferred", "GUARDCERT_AFFINE_FLOOR": "0",
            "GUARDCERT_AFFINE_CAP": "4", "GUARDCERT_AFFINE_BOUND_LOW": "-2",
            "GUARDCERT_AFFINE_BOUND_HIGH": "5"} | extra
    with (work/"compile.log").open("w") as log:
        result = subprocess.run([str(COMPILER),"-conf",str(COMPILER.parent/"compcert.ini"),
            "-stdlib",str(COMPILER.parent/"runtime"),"-dclight","-S","-o",str(work/"program.s"),str(SOURCE)],
            cwd=work,env=env,stdout=log,stderr=subprocess.STDOUT,text=True,timeout=240)
    assert result.returncode == 0,(name,(work/"compile.log").read_text()[-4000:])
    subprocess.run(["gcc","-no-pie",str(work/"program.s"),"-o",str(work/"program")],check=True,capture_output=True)
    actual = subprocess.check_output([str(work/"program")],text=True,timeout=90)
    (work/"output.txt").write_text(actual)
    assert actual == expected,name
    dump = work/(SOURCE.stem+".light.c")
    observations = {}
    for function,depth in zip(NAMES+["loaded_small2"],DEPTHS+[2]):
        body = function_body(dump.read_text(),function)
        observations[function] = {"guarded":body.count("for (")>depth,
            "loops":body.count("for ("),"clight_ifs":len(re.findall(r"\bif \(",body)),
            "clight_bytes":len(body.encode()),"machine_bytes":machine_bytes(work/"program",function)}
    return {"functions":observations,"calls":len(cases())+1,"mode":mode,"environment":extra,
            "artifacts":{p:sha(work/p) for p in ["program.s","program","output.txt",dump.name,"compile.log"]}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generate",action="store_true")
    parser.add_argument("--reference-only",action="store_true")
    parser.add_argument("--configurations")
    args = parser.parse_args()
    if args.generate:
        SOURCE.write_text(source_text())
    assert SOURCE.read_text() == source_text(),"C fixture differs from its generator"
    WORK.mkdir(parents=True,exist_ok=True)
    expected = expected_output()
    subprocess.run(["gcc","-O0","-fwrapv",str(SOURCE),"-o",str(WORK/"reference")],check=True)
    reference = subprocess.check_output([str(WORK/"reference")],text=True,timeout=90)
    assert reference == expected,"GCC and independent word model differ"
    (WORK/"reference-output.txt").write_text(reference)
    witness = (3,0,0,3,4,1,5)
    assert run_model(witness)[0] != run_model(witness,interchange=True)[0]
    if args.reference_only:
        print("Reference and word model agree:",len(cases())+1,"calls; real dependence witness checked")
        return
    check_build()
    configurations = [("disabled","disabled",{}),("interchange","interchange",{}),
        ("tile-2-3","tile-2-3",{}),("wrong-reindex","wrong-reindex",{}),
        ("invalid-domain","invalid-domain",{}),("resource-limit","interchange",{"GUARDCERT_FM_ROWS":"0"})]
    selected = set(args.configurations.split(",")) if args.configurations else {n for n,_,_ in configurations}
    assert selected <= {n for n,_,_ in configurations}
    results = {}
    for name,mode,extra in configurations:
        if name not in selected:
            continue
        print("Checking",name,flush=True)
        facts = compile_run(name,mode,extra,expected)
        accepted = {n for n,f in facts["functions"].items() if f["guarded"]}
        if name in ["interchange","tile-2-3"]:
            assert "loaded_accum3" in accepted and "loaded_multi3" in accepted, (name,accepted)
            assert "loaded_twice2" in accepted and "loaded_small2" in accepted, (name,accepted)
        else:
            assert not accepted,(name,accepted)
        if name == "interchange":
            assert "loaded_chain2" not in accepted,"real dependence incorrectly exchanged"
        results[name] = facts
    report = {"status":"passed","proved_entrypoint":ENTRY,"compiler_sha256":sha(COMPILER),
        "stamp_sha256":sha(COMPILER.parent/".guard-build.json"),"proof_report_sha256":sha(PROOF),
        "source_sha256":sha(SOURCE),"verification_script_sha256":sha(Path(__file__)),
        "helper_sources":{p:sha(ROOT/p) for p in ["scripts/native_zero_trip.py","scripts/audit_interface_clight.py"]},
        "source_generated":args.generate,"configurations":results,"calls_per_configuration":len(cases())+1,
        "total_new_calls":sum(r["calls"] for r in results.values()),"cases":cases(),
        "source_generator_and_word_model_bound":True,"true_dependence_counterexample":list(witness),
        "reference_sha256":sha(WORK/"reference-output.txt"),"new_machine_path_probes":False,
        "actual_loaded_plus_one_roots":True, "loaded_child_bounds_supported":False,
        "timing_or_profitability_measured":False}
    path = WORK/"report.json"
    path.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"passed","configurations":len(results),"calls":report["total_new_calls"],
        "report_sha256":sha(path)},indent=2))


if __name__ == "__main__":
    main()
