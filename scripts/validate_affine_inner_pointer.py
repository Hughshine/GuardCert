"""Bind the affine-inner proof, extraction, functional and machine evidence."""
import json
from pathlib import Path

import native_affine_inner_pointer as suite

ROOT, WORK, sha = suite.ROOT, suite.WORK, suite.sha


def main():
    stamp = suite.check_build()
    proof = json.loads(suite.PROOF.read_text())
    report_path = WORK / "report.json"
    native = json.loads(report_path.read_text())
    assert native["status"] == "passed" and native["proved_entrypoint"] == suite.ENTRY
    assert native["compiler_sha256"] == stamp["compiler_sha256"]
    assert native["proof_report_sha256"] == sha(suite.PROOF)
    assert native["compiler_stamp_sha256"] == sha(suite.COMPILER.parent / ".guard-build.json")
    assert native["source_sha256"] == sha(suite.SOURCE)
    assert native["verification_script_sha256"] == sha(ROOT / "scripts/native_affine_inner_pointer.py")
    assert stamp["extraction_sha256"] == sha(suite.COMPILER.parent / "extract_memory.v")
    assert stamp["build_script_sha256"] == sha(ROOT / "scripts/build_memory_compiler.py")
    assert stamp["driver_sha256"] == sha(suite.COMPILER.parent / "driver/Driver.ml")
    assert proof["verification_script_sha256"] == sha(ROOT / "scripts/audit_affine_pointer_domain.py")
    assert native["reference_output_sha256"] == sha(WORK / "reference-output.txt")
    assert native["unique_source_calls"] == len(suite.inputs()) == 81
    assert native["calls_across_configurations"] == 486
    expected = {"triangle":["affine_triangle"], "ragged":["affine_ragged"],
                "schedule":["affine_ragged","affine_triangle"], "ceiling-refused":[],
                "invalid-domain":[], "resource-limit":[]}
    assert set(native["configurations"]) == set(expected)
    for name,configuration in native["configurations"].items():
        assert configuration["compiled_in_this_run"]
        assert configuration["full_buffers_public_exits_prefix_and_suffix_match_model_and_gcc"]
        assert configuration["installed_functions"] == expected[name]
        assert configuration["actual_calls"] == 81
        for file,digest in configuration["artifacts"].items():
            assert sha(WORK / name / file) == digest,(name,file)
    probes = {"triangle-accept":("triangle","accepted-order",[160,97]),
              "triangle-alias-refuse":("triangle","shifted-alias-source-order",[97,160]),
              "triangle-box-refuse":("triangle","overlapping-box-source-order",[97,160]),
              "ragged-accept":("ragged","accepted-order",[160,97]),
              "schedule-accept":("schedule","accepted-order",[160,97])}
    assert set(native["probes"]) == set(probes)
    for key,(configuration,name,order) in probes.items():
        probe = native["probes"][key]
        assert [index for index,value in probe["writes"]] == order,key
        assert probe["binary_sha256"] == sha(WORK / configuration / "affine")
        assert probe["commands_sha256"] == sha(WORK / configuration / (name+".gdb"))
        assert probe["log_sha256"] == sha(WORK / configuration / (name+".gdb.log"))
    assert native["counterexample"] == {"arguments":[0,2,0,3,0],"absolute_index":4597,
        "source_value":4660,"unguarded_candidate_value":4723}
    assert not native["performance_measured"]
    result = {"status":"passed","proof_report_sha256":sha(suite.PROOF),
              "native_report_sha256":sha(report_path),"compiler_stamp_sha256":native["compiler_stamp_sha256"],
              "sources_and_objects_current":True,"calls":486,"machine_probes":5,
              "verification_script_sha256":sha(Path(__file__)),"performance_measured":False}
    (WORK.parent / "validation.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
