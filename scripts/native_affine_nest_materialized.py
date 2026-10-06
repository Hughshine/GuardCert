"""Run current-kernel deep affine compiler; preserve all frozen older reports."""
import hashlib
import json
import subprocess

import native_affine_nest as single
import native_affine_nest_multiple_pointers as multi
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/affine-nest-materialized/native"
COMPILER = ROOT / "build/affine-nest-materialized/compiler/ccomp"
PROOF = ROOT / "build/affine-nest-materialized/proof/report.json"
ENTRY = "ClightGuardedAffineNestCompiler.compile_materialized_affine_regions"
HELPERS = ["scripts/native_affine_nest.py", "scripts/native_affine_nest_multiple_pointers.py",
    "scripts/native_zero_trip.py", "scripts/native_sources.py"]


def check_build():
    stamp_path = COMPILER.parent / ".guard-build.json"
    stamp = json.loads(stamp_path.read_text())
    proof = json.loads(PROOF.read_text())
    assert stamp["proved_entrypoint"] == ENTRY == proof["whole_program_entrypoint"]
    assert proof["status"] == "compiled" and proof["additional_global_axioms"] == []
    assert sha(COMPILER) == stamp["compiler_sha256"]
    assert sha(COMPILER.parent/"driver/Driver.ml") == stamp["driver_sha256"]
    assert sha(COMPILER.parent/"extract_materialized_affine.v") == stamp["extraction_sha256"]
    assert sha(PROOF) == stamp["proof_report_sha256"]
    assert sha(ROOT / "scripts/build_affine_nest_materialized.py") == stamp["build_script_sha256"]
    assert sha(ROOT / "scripts/audit_affine_nest_materialized.py") == proof["verification_script_sha256"]
    for source,digest in (stamp["proof_sources"] | stamp["native_sources"] | stamp["build_helpers"]).items():
        assert sha(ROOT/source) == digest,source
    for source,digest in proof["compiled_objects"].items():
        assert sha((ROOT/source).with_suffix(".vo")) == digest,source
    return stamp


def reference(suite,directory):
    directory.mkdir(parents=True,exist_ok=True)
    expected = "".join(suite.output_model(row) for row in suite.full_inputs())
    subprocess.run(["gcc","-O0","-fwrapv",str(suite.SOURCE),"-o",str(directory/"reference")],check=True)
    with (directory/"reference-output.txt").open("w") as output:
        subprocess.run([str(directory/"reference")],stdout=output,text=True,check=True,timeout=180)
    assert (directory/"reference-output.txt").read_text()==expected
    return expected


def main():
    stamp=check_build()
    single.COMPILER=multi.COMPILER=COMPILER
    single.WORK=WORK/"single"
    references={"single":reference(single,WORK/"single"), "multi":reference(multi,WORK/"multi")}
    configurations=[("disabled","disabled",{}),("interchange","interchange",{}),
        ("tile-2-3","tile-2-3",{}),("wrong-reindex","wrong-reindex",{}),
        ("invalid-domain","invalid-domain",{}),
        ("resource-limit","interchange",{"GUARDCERT_FM_ROWS":"0"})]
    results={"single":{},"multi":{}}
    for suite_name,suite in (("single",single),("multi",multi)):
        for name,mode,extra in configurations:
            print("Checking",suite_name,name,flush=True)
            if suite_name=="single":
                facts=suite.compile_run(name,mode,extra,references[suite_name])
            else:
                facts=suite.compile_run(name,mode,extra,references[suite_name],directory=WORK/"multi")
            accepted=[fn for fn,fact in facts["functions"].items() if fact["guarded"]]
            if name in ("interchange","tile-2-3"):
                assert facts["functions"][suite.NAMES[1]]["guarded"],(suite_name,name,"three-level source not installed")
            else:
                assert not accepted,(suite_name,name,accepted)
            if suite_name=="single" and name=="interchange":
                assert not facts["functions"]["affine_chain2"]["guarded"],"unsafe dependency exchange accepted"
            directory=WORK/suite_name/name
            facts["binary_sha256"]=sha(directory/("affine" if suite_name=="single" else "program"))
            facts["mode"]=mode
            facts["environment"]=extra
            results[suite_name][name]=facts
    witness=(2,0,-2,3,4,2,-7)
    assert single.output_model(witness)!=single.output_model(witness,interchange=True)
    report={"status":"passed", "proved_entrypoint":ENTRY,
        "compiler_sha256":sha(COMPILER),"stamp_sha256":sha(COMPILER.parent/".guard-build.json"),
        "proof_report_sha256":sha(PROOF), "verification_script_sha256":sha(ROOT/"scripts/native_affine_nest_materialized.py"),
        "helper_sources":{p:sha(ROOT/p) for p in HELPERS},
        "source_files":{str(suite.SOURCE.relative_to(ROOT)):sha(suite.SOURCE) for suite in (single,multi)},
        "configurations":results,
        "calls_per_configuration":{s:len(suite.full_inputs()) for s,suite in (("single",single),("multi",multi))},
        "total_new_calls":sum(f["actual_calls"] for matrix in results.values() for f in matrix.values()),
        "actual_configuration_count":sum(len(matrix) for matrix in results.values()),
        "true_dependence_counterexample":list(witness),
        "reference_outputs":{s:sha(WORK/s/"reference-output.txt") for s in ("single","multi")},
        "word_model_and_gcc_reference":True,
        "source_generator_run":False,"new_machine_path_probes":False,
        "timing_or_profitability_measured":False,
        "scope":"Existing actual two/three-level nonrectangular C sources recompiled by the new kernel-connected entry; all array cells and public controls, disjoint and overlapping pointer views, conditional unused parameters, static refusal and untrusted tiling; no new domain/body capability claimed."}
    path=WORK/"report.json"
    path.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"passed","configurations":report["actual_configuration_count"],
        "new_calls":report["total_new_calls"],"report_sha256":sha(path)},indent=2))


if __name__=="__main__":
    main()
