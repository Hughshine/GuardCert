"""Bind the proved coordinate bridge and actual tiled intra-tile scheduling attempts."""
import argparse
import json
from pathlib import Path
import audit_double_reindexed_tiled_installation as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked

OUTPUT = ROOT / "docs/double-reindexed-tiling.json"
REPORTS = {
    **{f"compiler_v{version}": f"build/affine-double-tiling/compiler-attempts/native-v{version}/report.json"
       for version in range(1, 5)},
    "initial_matrix": "build/double-tiling/original-attempts/affine-original-v1/report.json",
    "reindexed_matrix_before_policy_repair": "build/double-tiling/original-attempts/affine-original-v2/report.json",
    "contexts_before_policy_repair": "build/double-tiling/check-attempts/affine-contexts-v1/report.json",
    "inspection": "build/double-tiling/original-attempts/affine-inspection-v1/report.json",
    "matrix": "build/double-tiling/original-attempts/affine-original-v4/report.json",
    "contexts": "build/double-tiling/check-attempts/affine-contexts-v2/report.json",
    "paths": "build/affine-double-tiling/path-attempts/paths-v1/report.json",
}

def relation(path, name):
    lines = [line.split("#", 1)[0].strip() for line in permitted(path).read_text().splitlines()]
    lines = [line for line in lines if line]
    start = lines.index(name)
    metadata = list(map(int, lines[start+1].split()))
    rows = [list(map(int, line.split())) for line in lines[start+2:start+2+metadata[0]]]
    if len(rows) != metadata[0] or any(len(row) != metadata[1] for row in rows):
        raise ValueError("Malformed recorded relation")
    return metadata, rows

def schedule(path):
    metadata, rows = relation(path, "SCATTERING")
    outputs, inputs, locals_, params = metadata[2:]
    if locals_ or len(rows) != outputs:
        raise ValueError("Expected explicit affine scattering")
    result = [None] * outputs
    for row in rows:
        output_coefficients = row[1:1+outputs]
        if row[0] or output_coefficients.count(-1) != 1 or any(value not in (0, -1) for value in output_coefficients):
            raise ValueError("Expected diagonal output coefficient")
        result[output_coefficients.index(-1)] = row[1+outputs:]
    if any(row is None for row in result):
        raise ValueError("Missing output coordinate")
    return {"input_dimensions": inputs, "parameter_dimensions": params, "rows": result}

def summarize():
    baseline = proof.validate()
    bindings = dict(baseline["bindings"])
    bindings[str((proof.WORK / "report.json").relative_to(ROOT))] = sha(proof.WORK / "report.json")
    reports = {name: checked(permitted(ROOT / path), bindings) for name, path in REPORTS.items()}
    rejected = {"initial_matrix", "reindexed_matrix_before_policy_repair", "contexts_before_policy_repair", "inspection"}
    for name, report in reports.items():
        expected = "built" if name.startswith("compiler_") else "rejected" if name in rejected else "passed"
        if report["status"] != expected:
            raise ValueError("Unexpected status: " + name)
    build = reports["compiler_v4"]
    if build["whole_program_entrypoint"] != proof.ENTRY:
        raise ValueError("Wrong actual compiler entry")
    matrix, contexts, paths = reports["matrix"]["results"], reports["contexts"]["cases"], reports["paths"]["cases"]
    for rows, size in [(matrix, 10), (contexts, 14), (paths, 3)]:
        if len(rows) != size or not all(row["passed"] for row in rows):
            raise ValueError("Incomplete installed-program acceptance")
    for name in rejected:
        rows = reports[name].get("results", reports[name].get("cases"))
        if not all(row.get("native_match", row.get("digest_matches_GCC", False)) for row in rows):
            raise ValueError("Unexpected native mismatch in preserved refusal")
    stages = {}
    for row in matrix:
        if row["mode"] != "tile":
            continue
        if row["installed_phase_calls_adaptations"] != [2, 2, 2]:
            raise ValueError("Missing actual installed tiled candidates")
        stages[row["case"]] = []
        for path in row["actual_phase_directories"]:
            directory = permitted(ROOT / path)
            command = (directory / "command.txt").read_text().splitlines()
            if "--identity" in command or "--intratileopt" not in command or "--tile" not in command:
                raise ValueError("Wrong actual phase options")
            middle = schedule(directory / "before.scop.midtransform.scop")
            after = schedule(directory / "before.scop.afterscheduling.scop")
            point, total = middle["input_dimensions"], after["input_dimensions"]
            added = total-point
            def coordinate(axis, dimensions):
                return [int(index == axis) for index in range(dimensions)] + [0] * (middle["parameter_dimensions"]+1)
            if middle["rows"] != [coordinate(axis, point) for axis in range(point)]:
                raise ValueError("Changed initial affine schedule")
            if added <= 0 or after["rows"][:added] != [coordinate(axis, total) for axis in range(added)]:
                raise ValueError("Changed tile schedule layout")
            point_order = [next(axis for axis in range(point) if coefficients == coordinate(added+axis, total))
                           for coefficients in after["rows"][added:]]
            stages[row["case"]].append({
                "directory": path,
                "middle": middle, "after": after, "point_order": point_order,
                "final_generated": str((directory / "generated.loop").relative_to(ROOT)),
            })
        if not any(stage["point_order"] != list(range(stage["middle"]["input_dimensions"]))
                   for stage in stages[row["case"]]):
            raise ValueError("No recorded point reordering in " + row["case"])
    for path in [Path(__file__), ROOT / "docs/double-reindexed-tiling-proof.json"]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    return {"status": "validated", "narrative_reference": "8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9",
        "whole_program_entrypoint": proof.ENTRY, "whole_program_theorem": proof.ENTRY+"_correct",
        "proof_source_lines": baseline["new_source_lines"], "proof_endpoints": len(baseline["endpoints"]),
        "maximum_inherited_globals": baseline["maximum_endpoint_globals"], "additional_global_axioms": [],
        "kernel_and_host_laws_unchanged": True,
        "new_proof_responsibility": "Domain candidate representation; reuse proved coordinate isomorphism and existing language installation",
        "C_users_supply_semantic_callbacks_or_handwritten_candidates": False,
        "phase_options": "automatic affine scheduling, tiling and intra-tile scheduling; no identity option",
        "initial_affine_schedule_remains_identity_in_these_four_sites": True,
        "actual_intra_tile_point_reordering_installed": True,
        "fixed_actual_parameters_candidate_progress": True,
        "candidate_body_not_rewritten_by_coordinate_witness_search": True,
        "finite_witness_policy": "identity and one adjacent swap; default six axes; bounded configurable axes",
        "original_input_checks": len(matrix), "context_checks": len(contexts), "unchanged_assembly_path_checks": len(paths),
        "original_installed_sites": {"mvt": 2, "matmul-seq": 2}, "stages": stages,
        "public_controls": {row["case"]: row["public_controls"] for row in contexts if "public_controls" in row},
        "paths": {row["case"]: row["actual"] for row in paths},
        "preserved_rejected_reports": sorted(rejected),
        "native_mismatches": [], "complete_corpus_replayed_with_this_build": False,
        "unit_and_general_affine_completion_revalidated_with_this_build": False,
        "controlled_cost_or_profitability_established": False, "full_goal_complete": False,
        "reports": REPORTS, "bindings": bindings}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    report = summarize()
    if args.validate:
        if json.loads(OUTPUT.read_text()) != report:
            raise ValueError("Changed summary or bound evidence")
    else:
        with OUTPUT.open("x") as output:
            output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"status": "validated", "reports": len(REPORTS), "bindings": len(report["bindings"]),
                      "summary_sha256": sha(OUTPUT)}))

if __name__ == "__main__":
    main()
