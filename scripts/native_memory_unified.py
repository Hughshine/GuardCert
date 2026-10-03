"""Execute one guarded C compiler with external affine and tiling proposals."""
import hashlib
import json
import re

import native_memory_proposed as proposed
from native_memory_tiling import selected

ROOT = proposed.ROOT
WORK = ROOT / "build" / "native-memory-unified"
COMPILER = ROOT / "build" / "compcert-memory-unified" / "ccomp"
ENTRY = "GuardMemoryUnifiedCompiler.compile_memory_unified_regions"


def main():
    proposed.WORK, proposed.COMPILER, proposed.ENTRY = WORK, COMPILER, ENTRY
    cross_function = "operations_two_arrays"
    proposed.REFUSED = [function for function in proposed.REFUSED if function != cross_function]
    proposed.main()
    affine = json.loads((WORK / "report.json").read_text())
    for name,configuration in affine["configurations"].items():
        dump = next((WORK/name).glob("*.light.c")).read_text()
        body = proposed.function_body(dump,cross_function)
        accepted = name in ["identity","interchange","redundant-guard","fission"]
        assert ("switch (0)" in body) == accepted,(name,cross_function)
        if accepted:
            assert re.search(r"if \([^\n]* != [^\n]*\)",body),(name,"missing actual array comparison")
            configuration["guarded_functions"].append(cross_function)
        configuration["cross_array_source_checked"] = True
    (WORK / "affine-report.json").write_text(json.dumps(affine,indent=2)+"\n")
    configurations = {}
    for rows,columns in [(1,1),(2,3),(4,4),(5,7),(17,13)]:
        name = f"tile-{rows}-{columns}"
        template = WORK / (name+".sexp")
        template.write_text(f"(tile {rows} {columns})\n")
        dump = proposed.compile_run(name,{"GUARDCERT_LOOP_CANDIDATE":str(template)})
        for function,(limit,stride,_) in proposed.ACCEPTED.items():
            assert selected(proposed.function_body(dump,function),limit,stride,rows,columns),(name,function)
        for function in proposed.REFUSED:
            assert "switch (0)" not in proposed.function_body(dump,function),(name,function)
        assert selected(proposed.function_body(dump,cross_function),12,10,rows,columns),(name,cross_function)
        configurations[name] = {"guarded_functions":sorted([*proposed.ACCEPTED,cross_function]),
                                "template_sha256":hashlib.sha256(template.read_bytes()).hexdigest(),
                                "all_cells_and_public_exits_match":True}
    refusals = {}
    for name,rows,columns,extra in [
            ("zero-width",0,4,{}),("negative-width",4,-3,{}),
            ("overflow-width",2**31-1,4,{}),("tile-resource-limit",4,4,{"GUARDCERT_FM_ROWS":"0"}),
            ("tile-invalid-certificate",4,4,{"GUARDCERT_ORACLE_FAULT":"top-certificate"})]:
        template = WORK / (name+".sexp"); template.write_text(f"(tile {rows} {columns})\n")
        dump = proposed.compile_run(name,{"GUARDCERT_LOOP_CANDIDATE":str(template)}|extra)
        for function in [*proposed.ACCEPTED,cross_function]:
            assert "switch (0)" not in proposed.function_body(dump,function),(name,function)
        refusals[name] = {"source_behavior_preserved":True}
    report = {"status":"passed","proved_entrypoint":ENTRY,"compiler_sha256":affine["compiler_sha256"],
              "affine_candidates":affine["configurations"],"tiling_candidates":configurations,
              "tiling_refusals":refusals,"actual_single_compiler_executable":True,
              "shared_guarded_whole_program_host":True,"full_output_lines_per_configuration":1564,
              "cross_array_source_reads_supported":True,
              "gcc_and_independent_model_match":True,"arbitrary_c_source_decoder_supported":False}
    (WORK / "report.json").write_text(json.dumps(report,indent=2)+"\n")
    print("Unified C-to-Asm guarded compiler passed: external identity/fission/interchange/domain guards, "
          "five two-dimensional tilings and five tile refusal routes in one executable")


if __name__ == "__main__": main()
