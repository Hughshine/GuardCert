"""Validate current proof, extraction, native outputs and guard-path bindings."""
import json
from pathlib import Path
import re

import native_affine_planned_loaded as suite

ROOT, WORK, sha = suite.ROOT, suite.WORK, suite.sha


def main():
    stamp = suite.check_build()
    proof = json.loads(suite.PROOF.read_text())
    report_path = WORK / "report.json"
    report = json.loads(report_path.read_text())
    assert proof["verification_script_sha256"] == sha(ROOT / "scripts/audit_affine_planned_loaded.py")
    assert report["status"] == "passed" and report["entrypoint"] == suite.ENTRY
    assert report["proof_report_sha256"] == sha(suite.PROOF)
    assert report["compiler_stamp_sha256"] == sha(suite.COMPILER_WORK / ".guard-build.json")
    assert report["source_sha256"] == sha(suite.SOURCE)
    assert report["verification_script_sha256"] == sha(ROOT / "scripts/native_affine_planned_loaded.py")
    assert report["shared_proposal_syntax_sha256"] == sha(ROOT / "scripts/native_affine_loaded_pointer.py")
    assert report["reference_output_sha256"] == sha(WORK / "expected.txt")
    assert report["unique_inputs"] == 37 and report["calls"] == 222
    assert report["python_gcc_complete_buffers_public_exits_and_context_agree"]
    assert report["runtime_candidate_fallback_probes"]
    assert report["actual_mapped_guard_comparison_order_and_early_stop_probed"]
    assert report["short_source_has_no_valid_future_row_write_cells"]
    assert not report["performance_measured"]
    expected = "".join(suite.model(kind,*control) for kind in range(6) for control in suite.CONTROLS)+suite.short_model()
    assert (WORK / "expected.txt").read_text() == expected
    installed = {"mapped":True,"schedule":True,"tile-2x3":True,"tile-4x1":True,"default-caps":True,"invalid":False}
    assert set(report["configurations"]) == set(installed)
    for name, configuration in report["configurations"].items():
        assert configuration["installed"] == installed[name] and configuration["calls"] == 37
        for file, digest in configuration["artifacts"].items():
            assert sha(WORK / name / file) == digest,(name,file)
        assert (WORK / name / "output.txt").read_text() == expected
    paths = {
        "different-blocks-accept":("mapped",0,3,0,[32,160,97],[32,96,97,160,161,162]),
        "same-block-offset-accept":("mapped",1,3,0,[32,160,97],[32,96,97,160,161,162]),
        "first-row-bound-refuse":("mapped",2,3,0,[32],[32]),
        "second-row-bound-refuse":("mapped",3,3,0,[32,97],[32,96,97]),
        "body-alias-refuse":("mapped",4,3,0,[32,97,160],[32,96,97,160,161,162]),
        "different-body-base-refuse":("mapped",5,3,0,[32,97,160],[32,96,97,160,161,162]),
        "unreachable-future-row-refuse":("mapped",6,3,0,[32],[32]),
        "cap-refuse":("mapped",0,5,7,[32,97,160],[]),
        "schedule-accept":("schedule",0,3,0,[32,160,97],None),
        "tile-accept":("tile-4x1",0,3,0,[32,160,97],None),
        "tile-bound-refuse":("tile-4x1",3,3,0,[32,97],None),
        "default-caps-accept":("default-caps",0,5,7,[32,160,97],None),
        "invalid-source":("invalid",0,3,0,[32,97,160],None),
    }
    assert set(report["probes"]) == set(paths)
    for name, (configuration,kind,n,a,order,comparisons) in paths.items():
        probe = report["probes"][name]
        assert (probe["kind"],probe["start"],probe["n"],probe["a"]) == (kind,0,n,a)
        assert probe["binary_sha256"] == sha(WORK / configuration / "planned")
        assert probe["commands_sha256"] == sha(WORK / configuration / (name+".gdb"))
        log = WORK / configuration / (name+".gdb.log")
        assert probe["log_sha256"] == sha(log)
        payload = re.findall(r"^GUARDCERT_PLANNED_PATH (.*)$",log.read_text(),re.MULTILINE)
        assert len(payload) == 1 and json.loads(payload[0]) == probe["observed"]
        observed = probe["observed"]
        assert [index for index,value in observed["writes"]] == order,name
        assert observed["bound_comparisons"] == comparisons,name
        if comparisons is not None:
            assert [index for index,offset in observed["comparison_sites"]] == [32,96,97,160,161,162,224,225,226,227]
        words = (suite.short_model() if kind == 6 else suite.model(kind,0,n,a)).split()
        assert observed["public"] == list(map(int,words[4:10]))
        assert observed["final_bound"] == int(words[11])
        assert [value for index,value in observed["writes"]] == [
            int(words[12+index if kind == 6 else 12+2*(4500+index)]) for index in order]
    result = {"status":"passed","proof_report_sha256":sha(suite.PROOF),
        "native_report_sha256":sha(report_path),"compiler_stamp_sha256":report["compiler_stamp_sha256"],
        "compiler_sha256":stamp["compiler_sha256"],"sources_and_objects_current":True,
        "calls":222,"machine_probes":13,"mapped_guard_comparison_order_bound":True,
        "verification_script_sha256":sha(Path(__file__)),"performance_measured":False}
    (WORK.parent / "validation.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
