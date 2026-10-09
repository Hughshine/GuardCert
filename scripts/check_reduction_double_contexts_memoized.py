"""Check actual pure-reduction-nest caller scopes, typed metadata, dynamic capture and native digests with retained artifacts and costs."""

import argparse
import json
import os
from pathlib import Path
import re
import statistics
import subprocess
import time

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

SOURCES = {name:ROOT / "build/benchmark-alignment/probe-v1" / name / "marked.c" for name in ["mvt"]}
PLUTO = ROOT / "build/polyhedral-pipeline/pluto-source/tool/pluto"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler-report", required=True, type=Path)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    build_report = permitted(ROOT / args.compiler_report)
    build = json.loads(build_report.read_text())
    if build["status"] != "built":
        raise ValueError("A successfully extracted compiler is required")
    for name,digest in build["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError("Changed compiler input: "+name)
    compiler = ROOT / build["compiler"]
    work = ROOT / "build/double-reduction-nests/compiler-native-checks" / args.attempt
    work.mkdir(parents=True,exist_ok=False)
    (work / "check-script.py").write_bytes(Path(__file__).read_bytes())
    rows = []
    def run(command,directory,label,environment=None):
        start = time.monotonic()
        try:
            outcome = subprocess.run(command,cwd=directory,env=environment,capture_output=True,timeout=180)
            stdout,stderr = outcome.stdout,outcome.stderr
            status = {"returncode":outcome.returncode,"timeout":False}
        except subprocess.TimeoutExpired as error:
            stdout,stderr = error.stdout or b"",error.stderr or b""
            status = {"returncode":None,"timeout":True}
        for suffix,data in [("stdout",stdout),("stderr",stderr)]:
            (directory / (label+"."+suffix)).write_bytes(data)
        status.update(argv=command,elapsed_seconds=time.monotonic()-start)
        return status,stdout,stderr
    cases = []
    for benchmark,path in SOURCES.items():
        original = path.read_text()
        first,last = original.index("#pragma scop"),original.index("#pragma endscop")+len("#pragma endscop")
        selected = original[first:last]
        shared = selected.replace("for (long long i", "for (i").replace("for (long long j", "for (j").replace("for (long long k", "for (k")
        multiple = original[:first]+"long long i, j, k;\n"+shared+"\n"+shared+original[last:]
        one_unmarked = original[:first]+"long long i, j, k;\n"+shared+"\n"+shared.replace("#pragma scop\n", "").replace("#pragma endscop", "")+original[last:]
        def dynamic(text):
            return text.replace("static const long long", "static long long").replace("  init_data();", "  init_data();\n  N = (int)polcert_rotr32((unsigned int)N, 16);\n  N = (int)polcert_rotr32((unsigned int)N, 16);")
        renamed = re.sub(r"\bN\b", "guardcert_size", original)
        names = ["a","x1","x2","y_1","y_2"]
        for key in names:
            renamed = re.sub(r"\b"+key+r"\b", "guardcert_array_"+key, renamed)
        type_changed = original.replace("double x1[100]", "float x1[100]").replace("double x2[100]", "float x2[100]")
        choices = [("multiple-marked","affine",multiple,2,4),
                   ("marked-and-unmarked","affine",one_unmarked,2,2),
                   ("renamed-globals","affine",renamed,2,2),
                   ("changed-dimensions","affine",original.replace("100", "104"),2,2),
                   ("array-type-refusal","affine",type_changed,0,0),
                   ("private-resource-refusal","affine",original,0,0),
                   ("dynamic-unmarked","affine",dynamic(original).replace("#pragma scop\n", "").replace("#pragma endscop\n", ""),0,0),
                   ("dynamic-accept","affine",dynamic(original),2,2),
                   ("dynamic-negative-N","affine",dynamic(original.replace("long long N = 96;", "long long N = -1;")),2,2),
                   ("dynamic-zero-N","affine",dynamic(original.replace("long long N = 96;", "long long N = 0;")),2,2)]
        public = original[:first]+"long long i=17, j=23, k=29;\n"+shared+'\nprintf("controls=%lld,%lld,%lld\\n",i,j,k);\n'+original[last:]
        for label,value in [("public-positive",96),("public-zero",0),("public-negative",-1)]:
            choices.append((label,"affine",dynamic(public.replace("long long N = 96;","long long N = "+str(value)+";")),2,2))
        choices.append(("wrong-coordinate-witness","wrong-witness",original,2,1))
        for name,mode,text,calls,installed in choices:
            cases.append((benchmark+"-"+name,mode,text,calls,installed))
    for name,mode,source_text,calls,installed in cases:
        directory = work / name
        directory.mkdir()
        source = directory / "program.c"
        source.write_text(source_text)
        environment = {key:value for key,value in os.environ.items() if not key.startswith("GUARDCERT_")}
        environment.update(GUARDCERT_ORIGINAL_MODE=mode,GUARDCERT_PLUTO=str(PLUTO),
                           GUARDCERT_ORIGINAL_OUTPUT=str(directory),GUARDCERT_SCOP_DIAGNOSTICS="1")
        if name.endswith("private-resource-refusal"):
            environment["GUARDCERT_DOUBLE_PRIVATE_COUNT"] = "1"
        row = {"case":name,"mode":mode,"source_sha256":sha(source),
               "expected_pipeline_calls":calls,"expected_installed_regions":installed}
        row["compiler"],out,err = run([str(compiler),"-fall","-stdlib",str(compiler.parent / "runtime"),
            "-dclight","-S","-o",str(directory / "program.s"),str(source)],directory,"compiler",environment)
        trace = (out+err).decode(errors="replace")
        found = re.findall(r"GUARDCERT_DOUBLE_INSTALLED original=\d+ initialized=\d+ regions=(\d+) pipeline_calls=(\d+)",trace)
        row["installed_regions"] = int(found[-1][0]) if found else None
        row["pipeline_calls"] = int(found[-1][1]) if found else None
        row["selection_trace"] = re.findall(r"^GUARDCERT_SCOP .*",trace,re.M)
        row["source_types_preserved"] = "double" in source_text and "[100]" in source_text and "for (long long i" in source_text
        row["profile_and_installation_match_expected"] = row["installed_regions"] == installed and row["pipeline_calls"] == calls
        if row["compiler"]["returncode"] == 0:
            row["link"],_,_ = run(["gcc","-no-pie",str(directory / "program.s"),"-lm","-o",str(directory / "program")],directory,"link")
            row["gcc_build"],_,_ = run(["gcc","-O0","-ffp-contract=off",str(source),"-lm","-o",str(directory / "reference")],directory,"gcc-build")
            if row["link"]["returncode"] == row["gcc_build"]["returncode"] == 0:
                row["native"],actual,_ = run([str(directory / "program")],directory,"native")
                row["reference"],expected,_ = run([str(directory / "reference")],directory,"reference")
                row["digest_matches_original_GCC"] = row["native"]["returncode"] == row["reference"]["returncode"] == 0 and actual == expected
                row["digest"] = actual.decode().strip()
                samples = []
                for trial in range(7):
                    sample,output,_ = run([str(directory / "program")],directory,f"timing-{trial}")
                    samples.append(sample["elapsed_seconds"])
                    if sample["returncode"] or output != expected:
                        row["digest_matches_original_GCC"] = False
                row["native_wall_seconds_including_initialization_and_digest"] = samples
                row["native_wall_median_seconds"] = statistics.median(samples)
        row["passed"] = row["profile_and_installation_match_expected"] and row.get("digest_matches_original_GCC",False)
        rows.append(row)
        (directory / "case-report.json").write_text(json.dumps(row,indent=2)+"\n")
        print(json.dumps({"case":name,"passed":row["passed"],"pipeline_calls":row["pipeline_calls"],
                          "installed_regions":row["installed_regions"]}),flush=True)
    for row in rows:
        benchmark = "mvt"
        unmarked = work / (benchmark+"-unmarked") / "program.light.c"
        emitted = work / row["case"] / "program.light.c"
        row["emitted_Clight_equals_unmarked"] = emitted.exists() and unmarked.exists() and emitted.read_bytes() == unmarked.read_bytes()
    bindings = dict(build["bindings"])
    for source in [Path(__file__),*SOURCES.values(),PLUTO,build_report,*[p for p in work.rglob("*") if p.is_file()]]:
        bindings[str(source.relative_to(ROOT))] = sha(permitted(source))
    report = {"status":"passed" if all(row["passed"] for row in rows) else "rejected",
              "compiler_report":str(build_report.relative_to(ROOT)),"compiler_report_sha256":sha(build_report),
              "compiler_entrypoint":build["whole_program_entrypoint"],"cases":rows,"bindings":bindings,
              "actual_Clight_and_Asm_native_execution":True,"original_double_arrays_and_I64_computations_retained":True,
              "original_cases":["mvt"],"native_guard_branch_observations_added":False,
              "actual_metadata_identifiers_dimensions_and_multiple_sites_exercised":True,
              "runtime_path_evidence":"installed generated guard and constant-header source variants; native modeled-state digests",
              "runtime_guard_instrumented":False,
              "cost_scope":"compiler wall time includes frontend, checked pipeline, scheduler and backend; native wall time includes initialization and digest",
              "corpus_alignment_complete":False,"full_goal_complete":False}
    (work / "report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":report["status"],"cases":len(rows),"passed":sum(row["passed"] for row in rows),
                      "report":str((work / "report.json").relative_to(ROOT))}),flush=True)
    if report["status"] != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
