"""Instrument current emitted Clight branches; not a machine-code path claim."""
import json
import native_affine_nest as single
import native_affine_nest_multiple_pointers as multi
import native_affine_nest_paths as single_paths
import native_affine_nest_multiple_pointers_paths as multi_paths
from native_affine_nest_materialized import ROOT, WORK, COMPILER, check_build
from validate_affine_nest_materialized import validate
from audit_interface_clight import sha

HELPERS=["scripts/native_affine_nest_paths.py", "scripts/native_affine_nest_multiple_pointers_paths.py",
    "scripts/native_memory_layout_sequence_paths.py", "scripts/native_zero_trip.py"]


def main():
    check_build()
    native=validate()
    single.COMPILER=multi.COMPILER=COMPILER
    single.WORK=WORK/"single"
    multi.WORK=WORK/"multi"
    results={"single":{},"multi":{}}
    for suite in ("single","multi"):
        for name in ("interchange","tile-2-3"):
            print("Probing emitted Clight",suite,name,flush=True)
            configuration=native["configurations"][suite][name]
            if suite=="single":
                facts=single_paths.diagnostic(name,configuration,fixture=single)
            else:
                facts=multi_paths.diagnostic(name,configuration,directory=WORK/"multi")
            directory=WORK/suite/name
            facts["diagnostic_binary_sha256"]=sha(directory/"branch-diagnostic")
            results[suite][name]=facts
    report={"status":"passed","native_report_sha256":sha(WORK/"report.json"),
        "compiler_sha256":sha(COMPILER),
        "verification_script_sha256":sha(ROOT/"scripts/probe_affine_nest_materialized.py"),
        "helper_sources":{p:sha(ROOT/p) for p in HELPERS},"configurations":results,
        "instrumented_configuration_count":4,
        "scope":"GCC instrumentation of actual emitted Clight: selected candidate/fallback, conditional undefined parameters, public exits and physical alias acceptance. Separate from unmodified CompCert assembly output validation; no assembly branch or guard-order probe."}
    path=WORK/"branch-report.json"
    path.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"passed","report_sha256":sha(path),
        "instrumented_configurations":4,"machine_path_probe":False},indent=2))


if __name__=="__main__":
    main()
