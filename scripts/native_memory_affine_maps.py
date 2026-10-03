"""Execute checked compositions of affine iterator maps in full C programs."""
import hashlib
import json
import os
import re
import subprocess

import native_memory_multiarray as arrays

ROOT = arrays.ROOT
WORK = ROOT/"build"/"native-memory-affine-maps"
ACCEPTED = ["shift","skew-inner","skew-negative","skew-diagonal","shift-skew","shift-interchange","reverse-inner"]


def main():
    arrays.WORK = WORK
    stamp = json.loads((arrays.COMPILER.parent/".guard-build.json").read_text())
    assert stamp["proved_entrypoint"] == arrays.ENTRY
    assert hashlib.sha256(arrays.COMPILER.read_bytes()).hexdigest() == stamp["compiler_sha256"]
    for path,expected in (stamp["proof_sources"]|stamp["native_sources"]).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == expected,path
    WORK.mkdir(parents=True,exist_ok=True)
    subprocess.run(["gcc","-O0",str(arrays.SOURCE),"-o",str(WORK/"gcc-reference")],check=True,capture_output=True)
    reference = subprocess.check_output([str(WORK/"gcc-reference")],text=True)
    assert reference == arrays.expected_output()
    (WORK/"gcc-output.txt").write_text(reference)
    templates = ROOT/"examples"/"loop-candidates"
    cases = [(name,templates/(name+".sexp"),{},
              arrays.ACCEPTED-{"multi_three"} if name == "reverse-inner" else arrays.ACCEPTED) for name in ACCEPTED]
    cases += [(name,templates/(name+".sexp"),{},set()) for name in ["wrong-shift","wrong-skew","wrong-diagonal-domain","shift-overflow"]]
    cases += [(name,templates/"skew-inner.sexp",extra,set()) for name,extra in
              [("resource-limit",{"GUARDCERT_FM_ROWS":"0"}),
               ("invalid-certificate",{"GUARDCERT_ORACLE_FAULT":"top-certificate"})]]
    configurations = {}
    for name,path,extra,expected in cases:
        dump = arrays.compile_run(name,{"GUARDCERT_LOOP_CANDIDATE":str(path)}|extra)
        for function in arrays.ACCEPTED:
            body = arrays.function_body(dump,function)
            assert ("switch (0)" in body) == (function in expected),(name,function,body)
            if function in expected:
                assert re.search(r"if \([^\n]* != [^\n]*\)",body),(name,function)
                assert "$i = $n;" in body and "$j = $m;" in body,(name,function)
        for function in arrays.REFUSED:
            assert "switch (0)" not in arrays.function_body(dump,function),(name,function)
        configurations[name] = {"guarded_functions":sorted(expected),"full_output_lines":len(reference.splitlines()),
                                "template_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
                                "gcc_and_independent_model_match":True}
    report = {"status":"passed","proved_entrypoint":arrays.ENTRY,"configurations":configurations,
              "compiler_sha256":stamp["compiler_sha256"],"source_sha256":hashlib.sha256(arrays.SOURCE.read_bytes()).hexdigest(),
              "actual_shift_and_skew_candidates_consumed":True,"composed_maps_checked":True,
              "unsafe_mapping_and_machine_overflow_refused":True,
              "unsafe_row_prefix_reversal_refused":True,"dependence_checker_still_consumed":True}
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(f"Affine coordinate maps passed: {len(cases)} configurations, {len(reference.splitlines())} output lines each")


if __name__ == "__main__": main()
