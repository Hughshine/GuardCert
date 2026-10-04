"""Exercise inferred source profiles on larger real two/three-level nests."""
from pathlib import Path
import argparse
import json
import os
import subprocess
import native_affine_nest as common
from native_zero_trip import function_body

ROOT, COMPILER = common.ROOT, common.COMPILER
SOURCE = ROOT / "examples/native_affine_nest_ranges.c"
WORK = ROOT / "build/native-affine-nest-ranges"
NAMES = ["affine_large2", "affine_large3", "affine_large_chain2"]
DEPTHS = [2, 3, 2]
SIZE, CENTER = 196608, 32768


def inputs():
    shapes = [(-2, 12, 4, 2), (0, 16, 2, 2), (1, 24, 3, 3), (0, 32, 2, 2),
              (-4, 16, 8, 8), (3, 2, 2, 2), (0, 12, -1, 2), (33, 34, 1, 1), (-5, 12, 8, 8)]
    result = [(which, 0, start, n, m, p, alpha) for which in range(3)
              for start, n, m, p in shapes for alpha in [-7, 2**31-1]]
    result += [(which, 1, boundary, boundary, 2**31-1, -2**31, -7)
               for which in range(3) for boundary in [-2**31, 2**31-1]]
    return result


def model(args, interchange=False):
    which, null, start, n, m, p, alpha = args
    array = [3*x+1 for x in range(SIZE)]
    points, final = [], [max(start,n),77,91,79,83]
    for i in range(start, n):
        upper = common.word(i+m)
        final[1],final[3] = max(0,upper),upper
        for j in range(max(0,upper)):
            if DEPTHS[which] == 3:
                inner = common.word(j+p)
                final[2],final[4] = max(0,inner),inner
                points += [(i,j,k) for k in range(max(0,inner))]
            else:
                points.append((i,j))
    if interchange:
        points.sort(key=lambda coordinate:(coordinate[1],coordinate[0],*coordinate[2:]))
    for coordinate in points:
        assert not null, args
        i,j = coordinate[:2]
        k = coordinate[2] if len(coordinate) == 3 else 0
        index = CENTER + (4096*i+64*j+k if which == 1 else 128*i+j)
        read = index + (127 if which == 2 else 0)
        assert 0 <= index < SIZE and 0 <= read < SIZE, (args,coordinate)
        array[index] = common.word(array[read]+alpha+i-j+k)
    return " ".join(map(str,[*args,*final,*array]))+"\n"


def generate():
    source = "#include <stdio.h>\nint affine_range_i,affine_range_j,affine_range_k,affine_range_K,affine_range_L;\n"
    for which,name in enumerate(NAMES):
        index = "4096*i+64*j+k" if which == 1 else "128*i+j"
        read = index + ("+127" if which == 2 else "")
        leaf = "a["+index+"]=a["+read+"]+alpha+i-j"+("+k" if which == 1 else "")+";"
        if which == 1:
            leaf = "L=j+p;for(k=0;k<L;k++){"+leaf+"}"
        source += ("void "+name+"(int *a,int start,int n,int m,int p,int alpha){"
                   "int i=start,j=77,k=91,K=79,L=83;for(;i<n;i++){K=i+m;for(j=0;j<K;j++){"+leaf+"}}"
                   "affine_range_i=i;affine_range_j=j;affine_range_k=k;affine_range_K=K;affine_range_L=L;}\n")
    source += ("void affine_range_case(int which,int null,int start,int n,int m,int p,int alpha){"
               "int a[196608],x;int *base;for(x=0;x<196608;x++)a[x]=3*x+1;base=a+32768;if(null)base=0;\n")
    for which,name in enumerate(NAMES):
        source += "if(which=="+str(which)+")"+name+"(base,start,n,m,p,alpha);\n"
    source += ("printf(\"%d %d %d %d %d %d %d %d %d %d %d %d\",which,null,start,n,m,p,alpha,"
               "affine_range_i,affine_range_j,affine_range_k,affine_range_K,affine_range_L);"
               "for(x=0;x<196608;x++)printf(\" %d\",a[x]);printf(\"\\n\");}\nint main(void){\n")
    for args in inputs():
        source += "affine_range_case("+",".join(common.literal(x) for x in args)+");\n"
    SOURCE.write_text(source+"return 0;}\n")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--generate",action="store_true")
    parser.add_argument("--reference-only",action="store_true")
    parser.add_argument("--cases")
    args = parser.parse_args()
    if args.generate:
        generate()
    WORK.mkdir(parents=True,exist_ok=True)
    expected = "".join(model(row) for row in inputs())
    subprocess.run(["gcc","-O0","-fwrapv",str(SOURCE),"-o",str(WORK/"reference")],check=True)
    reference = subprocess.check_output([str(WORK/"reference")],text=True,timeout=120)
    assert reference == expected
    (WORK/"reference-output.txt").write_text(reference)
    witness = (2,0,-2,12,4,2,-7)
    assert model(witness) != model(witness,interchange=True)
    if args.reference_only:
        print("Larger affine ranges:",len(inputs()),"complete GCC outputs match the word model; dependence witness checked")
        return
    stamp = common.check_build()
    options = [("builtin-interchange","interchange",{}),
               ("inferred-identity","identity",{"GUARDCERT_AFFINE_PROFILE":"inferred"}),
               ("inferred-interchange","interchange",{"GUARDCERT_AFFINE_PROFILE":"inferred"}),
               ("inferred-tile-2-3","tile-2-3",{"GUARDCERT_AFFINE_PROFILE":"inferred"}),
               ("inferred-wrong-witness","wrong-tiling-witness",{"GUARDCERT_AFFINE_PROFILE":"inferred"})]
    selected = set(args.cases.split(",")) if args.cases else {name for name,_,_ in options}
    assert selected <= {name for name,_,_ in options}
    results = {}
    for name,mode,extra in options:
        if name not in selected:
            continue
        print("Checking larger",name,flush=True)
        work = WORK/name
        work.mkdir(parents=True,exist_ok=True)
        environment = {key:value for key,value in os.environ.items() if not key.startswith("GUARDCERT_")}
        environment |= {"GUARDCERT_AFFINE_MODE":mode,"GUARDCERT_AFFINE_CAP":"32","GUARDCERT_AFFINE_DIAGNOSTICS":"1"}|extra
        with (work/"compile.log").open("w") as log:
            result = subprocess.run([str(COMPILER),"-conf",str(COMPILER.parent/"compcert.ini"),"-stdlib",
                str(COMPILER.parent/"runtime"),"-dclight","-S","-o",str(work/"affine.s"),str(SOURCE)],
                env=environment,cwd=work,stdout=log,stderr=subprocess.STDOUT,timeout=180)
        assert result.returncode == 0,name
        subprocess.run(["gcc","-no-pie",str(work/"affine.s"),"-o",str(work/"affine")],check=True,capture_output=True)
        actual = subprocess.check_output([str(work/"affine")],text=True,timeout=120)
        assert actual == reference,name
        (work/"output.txt").write_text(actual)
        dump_path = work/(SOURCE.stem+".light.c")
        dump = dump_path.read_text()
        installed = {fn:function_body(dump,fn).count("for (")>depth for fn,depth in zip(NAMES,DEPTHS)}
        if name in ["inferred-identity","inferred-interchange","inferred-tile-2-3"]:
            assert installed["affine_large2"] and installed["affine_large3"],(name,installed)
        if name == "inferred-interchange":
            assert not installed["affine_large_chain2"]
        if name == "inferred-wrong-witness":
            assert not any(installed.values())
        results[name] = {"actual_calls":len(inputs()),"installed_functions":installed,
                        "all_array_cells_and_public_exits_match_model_and_gcc":True,
                        "assembly_sha256":common.sha(work/"affine.s"),"output_sha256":common.sha(work/"output.txt"),
                        "clight_sha256":common.sha(dump_path)}
        print("Installed",[fn for fn,yes in installed.items() if yes],flush=True)
    (WORK/("smoke-report.json" if args.cases else "report.json")).write_text(json.dumps({
        "status":"passed","compiler_sha256":stamp["compiler_sha256"],"source_sha256":common.sha(SOURCE),
        "proof_report_sha256":stamp["prototype_proof_report_sha256"],"configured_root_cap":32,
        "calls_per_configuration":len(inputs()),"all_configurations_checked":not bool(args.cases),
        "configurations":results,"true_dependence_exchange_counterexample":list(witness),
        "scope":"complete unmodified CompCert assembly; inferred source/child/address ranges; 196608-cell buffers and all public exits"},indent=2)+"\n")


if __name__ == "__main__":
    main()
