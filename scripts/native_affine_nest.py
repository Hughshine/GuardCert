"""Run the extracted deep-affine compiler against complete word-level outputs."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
from native_zero_trip import function_body

ROOT = Path(__file__).resolve().parents[1]
COMPILER = ROOT / "build/compcert-affine-nest/ccomp"
SOURCE = ROOT / "examples/native_affine_nest.c"
WORK = ROOT / "build/native-affine-nest"
SIZE, CENTER = 16384, 8192
NAMES = ["affine_triangular2", "affine_triangular3", "affine_chain2",
         "affine_undefined3", "affine_descending3"]
DEPTHS = [2, 3, 2, 3, 3]


def word(value):
    return (value + 2**31) % 2**32 - 2**31


def full_inputs():
    shapes = [(-2, 3, 4, 2), (0, 3, 2, 2), (1, 4, 2, 2),
              (-3, -1, 4, 2), (-2, 3, 1, 2), (0, 3, -1, 2),
              (-5, 3, 8, 8), (0, 12, 20, 2), (0, 3, 2, -4),
              (3, 2, 2, 2), (0, 3, 0, 0), (-8, -6, 8, 2),
              (-2, 3, 7, 2)]
    result = [(which, 0, start, n, m, p, alpha)
              for which in range(len(NAMES)) for start, n, m, p in shapes
              for alpha in [-7, 0, -2**31, 2**31-1]]
    for which in range(len(NAMES)):
        for start, n in [(-2**31, -2**31), (2**31-1, 2**31-1), (3, 2)]:
            result.append((which, 1, start, n, 2**31-1, -2**31, 2**31-1))
        if which != 4:
            result += [(which, 1, 1, 2, 2**31-1, 2, -7),
                       (which, 1, -2**31, -2**31+1, 2**31-1, 2, -7)]
    return result


def source_points(args):
    which, _, start, n, m, p, _ = args
    result = []
    final = [start, 77, 91, 79, 83]
    for i in range(start, n):
        upper = word(m-i if which == 4 else i+m)
        final[1], final[3] = 0, upper
        for j in range(max(0, upper)):
            if DEPTHS[which] == 2:
                result.append((i, j))
            else:
                inner = word(p-j if which == 4 else j+p)
                final[2], final[4] = 0, inner
                for k in range(max(0, inner)):
                    result.append((i, j, k))
                final[2] = max(0, inner)
        final[1] = max(0, upper)
    final[0] = max(start, n)
    return result, final


def output_model(args, interchange=False):
    which, null, _, _, _, _, alpha = args
    points, final = source_points(args)
    if interchange:
        points.sort(key=lambda point: (point[1], point[0], *point[2:]))
    array = [word(3*x+1) for x in range(SIZE)]
    for coordinate in points:
        assert not null, args
        i, j = coordinate[:2]
        k = coordinate[2] if len(coordinate) == 3 else 0
        index = CENTER + 512*i + 32*j + k
        read = index + (480 if which == 2 else 0)
        assert 0 <= index < SIZE and 0 <= read < SIZE, (args, coordinate)
        array[index] = word(array[read] + alpha + i - j + k)
    return " ".join(map(str, [*args, *final, *array])) + "\n"


def literal(value):
    return "(-2147483647-1)" if value == -2**31 else str(value)


def generate():
    source = "#include <stdio.h>\nint affine_out_i,affine_out_j,affine_out_k,affine_out_K,affine_out_L;\n"
    for which, name in enumerate(NAMES):
        prefix, p_used, alpha_used = "", "p", "alpha"
        if which == 3:
            prefix = ("int local_p,local_alpha; "
                      "if(start<n && n-1+m>0) local_p=p; "
                      "if(start<n && n-1+m>0 && n-2+m+p>0) local_alpha=alpha; ")
            p_used, alpha_used = "local_p", "local_alpha"
        upper = "m-i" if which == 4 else "i+m"
        inner = "p-j" if which == 4 else "j+" + p_used
        index = "512*i+32*j" + ("+k" if DEPTHS[which] == 3 else "")
        read = index + ("+480" if which == 2 else "")
        value = "a[" + read + "]+" + alpha_used + "+i-j" + ("+k" if DEPTHS[which] == 3 else "")
        leaf = "a[" + index + "]=" + value + ";"
        if DEPTHS[which] == 3:
            leaf = "L=" + inner + ";for(k=0;k<L;k++){" + leaf + "}"
        loop = "for(;i<n;i++){K=" + upper + ";for(j=0;j<K;j++){" + leaf + "}}"
        source += ("void " + name + "(int *a,int start,int n,int m,int p,int alpha){"
                   "int i=start,j=77,k=91,K=79,L=83;" + prefix + loop +
                   "affine_out_i=i;affine_out_j=j;affine_out_k=k;affine_out_K=K;affine_out_L=L;}\n")
    source += ("void affine_case(int which,int null,int start,int n,int m,int p,int alpha){"
               "int a[16384],x;int *base;for(x=0;x<16384;x++)a[x]=3*x+1;"
               "base=a+8192;if(null)base=0;\n")
    for which, name in enumerate(NAMES):
        source += "if(which==" + str(which) + ")" + name + "(base,start,n,m,p,alpha);\n"
    source += ("printf(\"%d %d %d %d %d %d %d %d %d %d %d %d\","
               "which,null,start,n,m,p,alpha,affine_out_i,affine_out_j,affine_out_k,affine_out_K,affine_out_L);"
               "for(x=0;x<16384;x++)printf(\" %d\",a[x]);printf(\"\\n\");}\nint main(void){\n")
    for args in full_inputs():
        source += "affine_case(" + ",".join(literal(value) for value in args) + ");\n"
    source += "return 0;}\n"
    SOURCE.write_text(source)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_build():
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    assert stamp["proved_entrypoint"] == "AffineNestWholeCompiler.compile_affine_regions"
    assert sha(COMPILER) == stamp["compiler_sha256"]
    for filename, digest in (stamp["proof_sources"] | stamp["native_sources"]).items():
        assert sha(ROOT / filename) == digest, filename
    proof = ROOT / "build/affine-nest-foundation-prototype-report.json"
    assert sha(proof) == stamp["prototype_proof_report_sha256"]
    return stamp


def compile_run(name, mode, extra, reference):
    work = WORK / name
    work.mkdir(parents=True, exist_ok=True)
    environment = {key: value for key, value in os.environ.items()
                   if not key.startswith("GUARDCERT_")}
    environment |= {"GUARDCERT_AFFINE_MODE": mode, "GUARDCERT_AFFINE_DIAGNOSTICS": "1"} | extra
    with (work / "compile.log").open("w") as log:
        result = subprocess.run([str(COMPILER), "-conf", str(COMPILER.parent / "compcert.ini"),
            "-stdlib", str(COMPILER.parent / "runtime"), "-dclight", "-S", "-o", str(work / "affine.s"),
            str(SOURCE)], cwd=work, env=environment, text=True, stdout=log, stderr=subprocess.STDOUT, timeout=180)
    assert result.returncode == 0, (name, (work / "compile.log").read_text()[-3000:])
    subprocess.run(["gcc", "-no-pie", str(work / "affine.s"), "-o", str(work / "affine")],
                   check=True, capture_output=True)
    actual = subprocess.check_output([str(work / "affine")], text=True, timeout=120)
    (work / "output.txt").write_text(actual)
    assert actual == reference, name
    dump_path = work / (SOURCE.stem + ".light.c")
    dump = dump_path.read_text()
    observations = {}
    for function, depth in zip(NAMES, DEPTHS):
        body = function_body(dump, function)
        loops = body.count("for (")
        observations[function] = {"guarded": loops > depth,
                                  "loops_in_dump": loops, "body_bytes": len(body.encode())}
    return {"functions": observations, "actual_calls": len(full_inputs()),
            "all_array_cells_and_public_controls_match_word_model_and_gcc": True,
            "assembly_sha256": sha(work / "affine.s"), "output_sha256": sha(work / "output.txt"),
            "clight_sha256": sha(dump_path), "compile_diagnostics_sha256": sha(work / "compile.log")}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--generate", action="store_true")
    parser.add_argument("--reference-only", action="store_true")
    parser.add_argument("--cases")
    args = parser.parse_args()
    if args.generate:
        generate()
    WORK.mkdir(parents=True, exist_ok=True)
    expected = "".join(output_model(row) for row in full_inputs())
    subprocess.run(["gcc", "-O0", "-fwrapv", str(SOURCE), "-o", str(WORK / "reference")], check=True)
    reference = subprocess.check_output([str(WORK / "reference")], text=True, timeout=120)
    assert reference == expected, "GCC differs from the independent word model"
    (WORK / "reference-output.txt").write_text(reference)
    witness = (2, 0, -2, 3, 4, 2, -7)
    assert output_model(witness) != output_model(witness, interchange=True)
    if args.reference_only:
        print("GCC and word model agree on", len(full_inputs()), "complete outputs; true-dependence counterexample checked")
        return
    stamp = check_build()
    configurations = [("disabled", "disabled", {}), ("identity", "identity", {}),
        ("box", "box", {}), ("interchange", "interchange", {}), ("reverse", "reverse", {}),
        ("tile-2-3", "tile-2-3", {}), ("tile-17-13", "tile-17-13", {}), ("tile-1-1", "tile-1-1", {}),
        ("wrong-tiling-witness", "wrong-tiling-witness", {}),
        ("missing-tiling-witness", "missing-tiling-witness", {}),
        ("invalid-tile-size", "invalid-tile-size", {}),
        ("oversized-tile-policy", "oversized-tile-policy", {}),
        ("missing-reindex", "interchange", {"GUARDCERT_AFFINE_REINDEX": "none"}),
        ("invalid-domain", "invalid-domain", {}), ("wrong-reindex", "wrong-reindex", {}),
        ("noop-reindex", "noop-reindex", {}),
        ("resource-limit", "interchange", {"GUARDCERT_FM_ROWS": "0"}),
        ("oracle-fault", "interchange", {"GUARDCERT_ORACLE_FAULT": "top-certificate"})]
    selected = set(args.cases.split(",")) if args.cases else {name for name, _, _ in configurations}
    assert selected <= {name for name, _, _ in configurations}
    results = {}
    for name, mode, extra in configurations:
        if name not in selected:
            continue
        print("Checking", name, flush=True)
        result = compile_run(name, mode, extra, reference)
        accepted = [fn for fn, facts in result["functions"].items() if facts["guarded"]]
        print("Accepted guarded functions:", ", ".join(accepted) or "none", flush=True)
        if name in ["box", "interchange", "reverse", "tile-2-3", "tile-17-13", "tile-1-1"]:
            assert result["functions"]["affine_triangular3"]["guarded"], (name, "three-level candidate absent")
        if name == "interchange":
            assert not result["functions"]["affine_chain2"]["guarded"], "unsafe dependent exchange accepted"
        if name == "noop-reindex":
            assert len(accepted) == len(NAMES), "out-of-range swaps are proved identity operations"
        if name in ["disabled", "invalid-domain", "wrong-reindex", "resource-limit", "oracle-fault",
                    "wrong-tiling-witness", "missing-tiling-witness", "invalid-tile-size", "oversized-tile-policy"]:
            assert not accepted, (name, accepted)
        results[name] = result
    report = {"status": "passed", "compiler_sha256": stamp["compiler_sha256"],
        "proved_entrypoint": stamp["proved_entrypoint"], "proof_report_sha256": stamp["prototype_proof_report_sha256"],
        "source_sha256": sha(SOURCE), "calls_per_configuration": len(full_inputs()),
        "all_configurations_checked": not bool(args.cases), "configurations": results,
        "true_dependence_exchange_counterexample": list(witness),
        "scope": "actual complete CompCert assembly, source-derived guards, nonrectangular two/three-level memory nests, "
                 "untrusted boxed/permuted/tiled candidates, complete arrays and all public control exits; single pointer"}
    (WORK / ("smoke-report.json" if args.cases else "report.json")).write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
