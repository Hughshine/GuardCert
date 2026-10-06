"""Verify that the deep affine native results still bind their exact inputs."""
import json
from native_affine_nest_materialized import ROOT, WORK, COMPILER, PROOF, check_build
from audit_interface_clight import sha


def validate():
    stamp=check_build()
    path=WORK/"report.json"
    report=json.loads(path.read_text())
    assert report["status"]=="passed"
    assert report["compiler_sha256"]==stamp["compiler_sha256"]
    assert report["stamp_sha256"]==sha(COMPILER.parent/".guard-build.json")
    assert report["proof_report_sha256"]==sha(PROOF)
    assert report["verification_script_sha256"]==sha(ROOT/"scripts/native_affine_nest_materialized.py")
    for source,digest in (report["helper_sources"]|report["source_files"]).items():
        assert sha(ROOT/source)==digest,source
    total=0
    for suite,matrix in report["configurations"].items():
        assert set(matrix)=={"disabled","interchange","tile-2-3","wrong-reindex","invalid-domain","resource-limit"}
        is_single=suite=="single"
        source_name="native_affine_nest" if is_single else "native_affine_nest_multiple_pointers"
        prefix="affine" if is_single else "program"
        for name,facts in matrix.items():
            directory=WORK/suite/name
            bindings={"assembly_sha256":directory/(prefix+".s"),
                "binary_sha256":directory/prefix,"output_sha256":directory/"output.txt",
                "clight_sha256":directory/(source_name+".light.c"),
                "compile_diagnostics_sha256" if is_single else "compile_log_sha256":directory/"compile.log"}
            for key,artifact in bindings.items():
                assert sha(artifact)==facts[key],artifact
            assert sha(directory/"output.txt")==report["reference_outputs"][suite]
            assert facts["actual_calls"]==report["calls_per_configuration"][suite]
            accepted={fn for fn,f in facts["functions"].items() if f["guarded"]}
            if name in {"interchange","tile-2-3"}:
                assert ("affine_triangular3" if is_single else "multi_triangular3") in accepted
            else:
                assert not accepted,(suite,name)
            total+=facts["actual_calls"]
        assert sha(WORK/suite/"reference-output.txt")==report["reference_outputs"][suite]
    assert report["actual_configuration_count"]==12
    assert report["total_new_calls"]==total
    branches=WORK/"branch-report.json"
    if branches.exists():
        branch=json.loads(branches.read_text())
        assert branch["status"]=="passed" and branch["native_report_sha256"]==sha(path)
        assert branch["compiler_sha256"]==stamp["compiler_sha256"]
        assert branch["verification_script_sha256"]==sha(ROOT/"scripts/probe_affine_nest_materialized.py")
        for source,digest in branch["helper_sources"].items():
            assert sha(ROOT/source)==digest,source
        assert branch["instrumented_configuration_count"]==4
        for suite,matrix in branch["configurations"].items():
            assert set(matrix)=={"interchange","tile-2-3"}
            for name,facts in matrix.items():
                directory=WORK/suite/name
                for key,artifact in {"diagnostic_source_sha256":directory/"branch-diagnostic.c",
                        "diagnostic_output_sha256":directory/"branch-output.txt",
                        "diagnostic_binary_sha256":directory/"branch-diagnostic"}.items():
                    assert sha(artifact)==facts[key],artifact
                if suite=="single":
                    assert facts["actual_fast_calls"] and facts["actual_fallback_calls"]
                    assert facts["undefined_parameters_have_zero_guard_reads"]
                else:
                    assert facts["fast"] and facts["fallback"] and facts["shared_storage_disjoint_fast"]
                    assert facts["overlapping_access_fallback"] and facts["undefined_p_zero_guard_reads"]
    regression=ROOT/"build/affine-nest-materialized/cursor-regression/report.json"
    if regression.exists():
        old=json.loads(regression.read_text())
        assert old["status"]=="compiled" and len(old["endpoint_assumptions"])==42
        assert old["materialized_proof_report_sha256"]==sha(PROOF)
        assert old["verification_script_sha256"]==sha(ROOT/"scripts/audit_cursor_after_shared_rebuild.py")
        assert old["new_materialized_objects_unchanged"] and not old["native_rerun"]
        assert old["inherited_frozen_report_sha256"]==sha(ROOT/"build/affine-cursor-dependent-compiler/proof/report.json")
        for source,digest in old["sources"].items():
            assert sha(ROOT/source)==digest,source
        for source,digest in old["compiled_objects"].items():
            assert sha((ROOT/source).with_suffix(".vo"))==digest,source
    print(json.dumps({"status":"passed","bound_configurations":12,"bound_new_calls":total,
        "native_report_sha256":sha(path),"validator_sha256":sha(ROOT/"scripts/validate_affine_nest_materialized.py")},indent=2))
    return report


if __name__=="__main__":
    validate()
