"""Bind original native outcomes and calibrated whole-tree fusion evidence."""
import json
from pathlib import Path
import re

import audit_double_tree_shifted as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked

PORTABLE = ROOT / "docs/double-tree-shifted-native.json"
WORK = ROOT / "build/double-tree-shifted/native-summary-v1"


def scattering_times(text, values, parameters):
    relations = list(re.finditer(r"^SCATTERING\n([0-9 ]+)\n((?:(?:0|1) [^\n]+\n)+)", text, re.M))
    result = []
    for index,match in enumerate(relations):
        _,_,outputs,inputs,locals_,params = map(int,match.group(1).split())
        if inputs != 1 or locals_ or params != len(parameters):
            raise ValueError("Expected the original one-axis exported schedule")
        rows = [list(map(int,line.split())) for line in match.group(2).splitlines()]
        times = []
        for axis in range(outputs):
            row = next(row for row in rows if row[0] == 0 and row[1+axis] == -1
                       and all(row[1+j] == 0 for j in range(outputs) if j != axis))
            coordinates = [values[index],*parameters,1]
            coefficients = row[1+outputs:]
            if len(coordinates) != len(coefficients):
                raise ValueError("Wrong schedule row width")
            times.append(sum(a*b for a,b in zip(coefficients,coordinates)))
        result.append(times)
    return result


def main():
    baseline = proof.validate()
    bindings = dict(baseline["bindings"])
    reports = {}
    for label,name in [
        ("diagnostic_build", "build/double-tree-model/compiler-attempts/native-trace-v4/report.json"),
        ("diagnostic_old", "build/double-tree-model/trace-attempts/phase-v1/report.json"),
        ("diagnostic_final", "build/double-tree-model/trace-attempts/phase-v2/report.json"),
        ("compiler", "build/double-tree-model/compiler-attempts/native-shifted-v1/report.json"),
        ("diagnostic_shifted", "build/double-tree-model/trace-attempts/phase-shifted-v1/report.json"),
        ("native", "build/double-tree-shifted/native-attempts/original-v1/report.json")]:
        report = checked(permitted(ROOT/name),bindings)
        reports[label] = {"path":name,"sha256":sha(ROOT/name)}
        if label == "native":
            native = report
        if label == "compiler":
            build = report
    if native["status"] != "checked" or native["native_matches"] != 15 or native["failures"]:
        raise ValueError("All fifteen unchanged-source configurations must match")
    cases = []
    for row in native["cases"]:
        config = row["configurations"]
        if config["unmarked"]["installed"] != [0,0,0] or config["wrong-shift"]["installed"][0] != 0:
            raise ValueError("Unmarked and wrong-shift controls must install no candidate")
        cases.append({"case":row["case"],"input":row["input"],"input_sha256":row["input_sha256"],
                      "configurations":{mode:{"status":value["status"],"installed":value["installed"]}
                                        for mode,value in config.items()}})
    fusion = ROOT / "build/double-tree-model/trace-attempts/phase-shifted-v1/fusion1"
    generated = permitted(fusion/"tiling-pipeline-1/tree-generated.loop").read_text()
    shifts = permitted(fusion/"tiling-pipeline-1/tree-shifts.txt").read_text()
    if (generated.count("loop [") != 1 or generated.count("instruction array=") != 2
            or "guard 3<=v0" not in generated or "args=((v0+-1))" not in generated or shifts != "0,-1\n"):
        raise ValueError("Expected the original complete fused candidate and coordinate shifts")
    for mode,cap in [("untiled",4096),("tiled",4096),("refuse-profile",4)]:
        path = ROOT/"build/double-tree-shifted/native-attempts/original-v1/fusion1"/mode/"program.light.c"
        text = permitted(path).read_text()
        region = text[text.index("__guardcert_scop_1:"):]
        if region.count("for (; 1;") != 3 or f"if ({cap}LL < N)" not in region:
            raise ValueError("Expected one fused loop and the two original fallback loops")
        if "if (3 <= $" not in region:
            raise ValueError("Expected the actual fused Out dispatch")
    stencil = ROOT/"build/double-tree-model/trace-attempts/phase-v2/multi-stmt-stencil-seq/tiling-pipeline-1/before.scop"
    times = scattering_times(permitted(stencil).read_text(),[1,2,3,4,5],[16])
    if len(times) != 5 or not times[2] < times[1]:
        raise ValueError("Expected the observed exported source-order inversion")
    for path in [Path(__file__),proof.WORK/"report.json"]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    summary = {"status":"checked","reports":reports,"compiler":build["compiler"],
               "compiler_sha256":build["compiler_sha256"],"whole_program_theorem":native["whole_program_theorem"],
               "native_cases":3,"native_configurations":15,"native_matches":15,"cases":cases,
               "complete_marked_tree_fusion_cases":["fusion1"],
               "fusion_requested_untiled_and_tiled_generate_the_same_fused_unblocked_shape":True,
               "fusion_point_shifts":[0,-1],"fusion_lowering_reached_and_accepted":True,
               "wrong_shift_controls_install_no_regions":True,
               "tight_profile_original_N":4096,"tight_profile_cap":4,
               "tight_profile_fusion_guard_installed":True,
               "tight_profile_refusal_inferred_from_emitted_checks_and_fixed_input":True,
               "actual_runtime_guard_branch_observation_added":False,"new_cost_evidence":False,
               "stencil_exported_order_counterexample":{"parameter_N":16,"statement_2_index":2,
                   "statement_3_index":3,"statement_2_timestamp":times[1],"statement_3_timestamp":times[2],
                   "statement_3_exported_before_statement_2":True,
                   "original_C_executes_the_second_range_before_the_third":True},
               "remaining_complete_marked_tree_cases":["multi-stmt-stencil-seq","tricky3"],
               "domain_partition_checker_added":False,"OLO_compact_condition_algorithm_complete":False,
               "aggregate_full_corpus_coverage_recomputed":False,"full_goal_complete":False}
    with PORTABLE.open("x") as out:
        out.write(json.dumps(summary,indent=2)+"\n")
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    WORK.mkdir(parents=True,exist_ok=False)
    (WORK/"report.json").write_text(json.dumps({**summary,"bindings":bindings},indent=2)+"\n")
    print(json.dumps({"status":"checked","complete_fusion_cases":summary["complete_marked_tree_fusion_cases"],
                      "native_matches":15,"bindings":len(bindings),"summary":str(PORTABLE.relative_to(ROOT))}))


if __name__ == "__main__":
    main()
