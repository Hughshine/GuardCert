"""Check actual raw-frontend original-C installation, refusal and native digests with retained artifacts and costs."""

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

SOURCE = ROOT / "build/benchmark-alignment/probe-v1/matmul/marked.c"
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
    work = ROOT / "build/original-matmul/compiler-native-checks" / args.attempt
    work.mkdir(parents=True,exist_ok=False)
    (work / "check-script.py").write_bytes(Path(__file__).read_bytes())
    original = SOURCE.read_text()
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
    cases = [("original-affine","affine",original,1,1),
             ("original-identity","identity",original,1,1),
             ("unmarked","affine",original.replace("#pragma scop\n","").replace("#pragma endscop\n",""),0,0),
             ("scheduler-refusal","refuse",original,1,0),
             ("reverse-dependences","reverse",original,1,0),
             ("malformed-schedule","malformed",original,1,0),
             ("wrong-coordinate-witness","wrong-witness",original,1,0),
             ("runtime-negative-M","affine",original.replace("long long M = 96;","long long M = -1;"),1,1),
             ("runtime-zero-M","affine",original.replace("long long M = 96;","long long M = 0;"),1,1),
             ("runtime-negative-N","affine",original.replace("long long N = 96;","long long N = -1;"),1,1)]
    for name,mode,source_text,calls,installed in cases:
        directory = work / name
        directory.mkdir()
        source = directory / "program.c"
        source.write_text(source_text)
        environment = {key:value for key,value in os.environ.items() if not key.startswith("GUARDCERT_")}
        environment.update(GUARDCERT_ORIGINAL_MODE=mode,GUARDCERT_PLUTO=str(PLUTO),
                           GUARDCERT_ORIGINAL_OUTPUT=str(directory),GUARDCERT_SCOP_DIAGNOSTICS="1")
        row = {"case":name,"mode":mode,"source_sha256":sha(source),
               "expected_pipeline_calls":calls,"expected_installed_regions":installed}
        row["compiler"],out,err = run([str(compiler),"-fall","-stdlib",str(compiler.parent / "runtime"),
            "-dclight","-S","-o",str(directory / "program.s"),str(source)],directory,"compiler",environment)
        trace = (out+err).decode(errors="replace")
        found = re.findall(r"GUARDCERT_ORIGINAL_INSTALLED regions=(\d+) pipeline_calls=(\d+)",trace)
        row["installed_regions"] = int(found[-1][0]) if found else None
        row["pipeline_calls"] = int(found[-1][1]) if found else None
        row["selection_trace"] = re.findall(r"^GUARDCERT_SCOP .*",trace,re.M)
        row["source_types_preserved"] = "double A[100][100]" in source_text and "for (long long i" in source_text
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
    unmarked = work / "unmarked/program.light.c"
    for row in rows:
        emitted = work / row["case"] / "program.light.c"
        row["emitted_Clight_equals_unmarked"] = emitted.exists() and unmarked.exists() and emitted.read_bytes() == unmarked.read_bytes()
    bindings = dict(build["bindings"])
    for source in [Path(__file__),SOURCE,PLUTO,build_report,*[p for p in work.rglob("*") if p.is_file()]]:
        bindings[str(source.relative_to(ROOT))] = sha(permitted(source))
    report = {"status":"passed" if all(row["passed"] for row in rows) else "rejected",
              "compiler_report":str(build_report.relative_to(ROOT)),"compiler_report_sha256":sha(build_report),
              "compiler_entrypoint":build["whole_program_entrypoint"],"cases":rows,"bindings":bindings,
              "actual_Clight_and_Asm_native_execution":True,"original_double_arrays_and_I64_computations_retained":True,
              "runtime_path_evidence":"installed generated guard and constant-header source variants; native full-state digests",
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
