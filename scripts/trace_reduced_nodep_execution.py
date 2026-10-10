"""Observe all original nodep candidate updates in unchanged assembly."""
import argparse
import json
from pathlib import Path
import re
import subprocess

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_reduced_literal_combined_corpus import checked

BUILD = ROOT / "build/double-tree-model/compiler-attempts/native-reduced-literal-combined-v1/report.json"
REPLAY = ROOT / "build/benchmark-alignment/current-reduced-literal-combined-attempts/blockers-v1/report.json"
OLD = [ROOT / "build/benchmark-alignment" / directory / "nodep-v1/report.json" for directory in
       ["current-literal-combined-attempts", "current-typed-literal-combined-attempts"]]
PORTABLE = ROOT / "docs/reduced-nodep-execution.json"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not re.fullmatch("[a-z0-9-]+", args.attempt):
        raise ValueError("Use a new simple attempt name")
    bindings = {}
    build, replay, *earlier = [checked(p, bindings) for p in [BUILD, REPLAY, *OLD]]
    observer_failure = ROOT / "build/declared-literal-double/execution-attempts/original-v1/rejection.json"
    checked(observer_failure, bindings)
    checked(ROOT / "build/equality-reduced-codegen/execution-attempts/original-v1/rejection.json", bindings)
    entry = "ReducedLiteralCombinedDoubleCompiler.compile_selected_reduced_literal_combined_double_program"
    if build["whole_program_entrypoint"] != entry or replay["compiler_entrypoint"] != entry:
        raise ValueError("Expected the declared-literal compiler")
    if replay["original_cases_attempted"] != 3 or replay["native_configuration_matches"] != 9:
        raise ValueError("Expected original nodep with three complete matches")
    row, = [row for row in replay["results"] if row["case"] == "nodep"]
    if row["case"] != "nodep" or row["variant"] != "original":
        raise ValueError("Expected the unchanged original computation")
    expected = permitted(ROOT / row["original_GCC_reference"]).read_bytes()
    base = REPLAY.parent / "nodep-original"
    work = ROOT / "build/equality-reduced-codegen/execution-attempts" / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work / "script.py").write_bytes(Path(__file__).read_bytes())
    observations = {}
    for mode in ["unmarked", "untiled", "tiled"]:
        directory = work / mode
        directory.mkdir()
        target = base / mode / "program"
        ast = permitted(base / mode / "program.light.c").read_text()
        ast = ast[ast.rindex("\nint main(void)\n{"):]
        ast = ast[:ast.index("  print_modeled_state_digest();")]
        phase = base / mode / "tiling-pipeline-1"
        if mode != "unmarked":
            if ("$162 = 100;" not in ast or "$163 = 4;" not in ast
                    or "$i < 100" in ast or "$i = (long long) $162;" not in ast
                    or "$j = (long long) $163;" not in ast):
                raise ValueError("Missing actual candidate/private prelude/public exit")
        dis = subprocess.run(["objdump", "-d", "--no-show-raw-insn", "--disassemble=main", str(target)],
                             capture_output=True, text=True, check=True).stdout
        (directory / "disassembly.txt").write_text(dis)
        # The real update 2*A+2 is lowered to two additions followed by
        # its array store. Initialization instead divides. Registers differ
        # between the source and candidate; derive them from each actual body.
        stores = re.findall(r"^\s*[0-9a-f]+:\s+addsd[^\n]*\n\s*[0-9a-f]+:\s+addsd[^\n]*\n\s*([0-9a-f]+):\s+movsd\s+%xmm[0-9]+,\(%([a-z0-9]+),%([a-z0-9]+),8\)", dis, re.M)
        if len(stores) != 1:
            raise ValueError("Expected one identifiable actual update store: " + mode)
        address, base_register, index_register = stores[0]
        command = directory / "observe.gdb"
        trace = directory / "updates.json"
        command.write_text("set pagination off\nset confirm off\nset disable-randomization off\npython\n"
            "import gdb, json\nupdates=[]\n"
            "class Updates(gdb.Breakpoint):\n"
            " def stop(self):\n"
            f"  base=int(gdb.parse_and_eval('${base_register}'))\n"
            f"  index=int(gdb.parse_and_eval('${index_register}'))\n"
            "  origin=int(gdb.parse_and_eval('(char*)&A'))\n"
            "  offset=(base+8*index-origin)//8\n"
            + ("  registers={name:int(gdb.parse_and_eval('$'+name)) for name in ['eax','ebx','ecx','edx','esi','edi','r8d','r9d','r10d','r11d','r12d','r13d','r14d','r15d']}\n"
               if mode == "tiled" else "  registers=None\n")
            + "  updates.append({'array_index':offset,'registers':registers})\n  return False\n"
            f"Updates('*0x{address}')\nend\nrun\npython\n"
            f"with open({str(trace)!r},'x') as out: json.dump(updates,out)\nend\nquit\n")
        argv = ["gdb", "-q", "-batch", "-x", str(command), str(target)]
        run = subprocess.run(argv, cwd=ROOT, capture_output=True, timeout=180)
        (directory / "debugger.stdout").write_bytes(run.stdout)
        (directory / "debugger.stderr").write_bytes(run.stderr)
        (directory / "command.json").write_text(json.dumps({"argv": argv, "returncode": run.returncode}) + "\n")
        if run.returncode or not trace.exists() or expected.strip() not in run.stdout:
            raise ValueError("Debugger did not execute and match complete output: " + mode)
        updates = json.loads(trace.read_text())
        indexes = [item["array_index"] for item in updates]
        if len(indexes) != 400 or sorted(indexes) != list(range(2, 402)):
            raise ValueError("Expected all 400 real original updates exactly once: " + mode)
        tile_register_matches = [[], []]
        if mode == "tiled":
            for axis in [0, 1]:
                for register in updates[0]["registers"]:
                    if all(item["registers"][register] ==
                           (((item["array_index"]-2)//32) if axis == 0 else ((item["array_index"]-2)//128))
                           for item in updates):
                        tile_register_matches[axis].append(register)
            if not all(tile_register_matches):
                raise ValueError("No actual register matches the witness tile coordinate over all updates")
            for item in updates:
                item["tile"] = [item["registers"][matches[0]] for matches in tile_register_matches]
        tiles = sorted({tuple(item["tile"]) for item in updates}) if mode == "tiled" else []
        if mode == "tiled":
            expected_tiles = sorted({((4*i+j)//32, i//32) for i in range(100) for j in range(4)})
            for item in updates:
                i, j = divmod(item["array_index"] - 2, 4)
                if item["tile"] != [(4*i+j)//32, i//32]:
                    raise ValueError("Actual tile registers disagree with witness coordinates")
            if tiles != expected_tiles:
                raise ValueError("Actual updating tile groups differ from original points")
        observations[mode] = {"complete_output_matches": True, "all_update_stores": len(indexes),
            "all_original_array_indexes_exactly_once": True,
            "update_order": indexes, "updating_tile_pairs": tiles,
            "tile_register_matches_across_all_updates": tile_register_matches,
            "literal_candidate_installed": mode != "unmarked",
            "actual_source_header_retained": "$i < 100" in ast,
            "candidate_Loop_depth": sum(line.lstrip().startswith("loop [") for line in
                permitted(phase / "tree-runtime-residual.loop").read_text().splitlines()) if mode != "unmarked" else 2,
            "Clight_conditions": ast.count("if ("), "Clight_lines": len(ast.splitlines()),
            "actual_instruction_address": "0x" + address}
    for path in [ROOT / row["input"], ROOT / row["original_GCC_reference"], Path(__file__),
                 *[p for p in work.rglob("*") if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "passed", "case": "original-nodep", "compiler_entrypoint": entry,
        "whole_program_theorem": entry + "_correct", "original_input": row["input"],
        "original_input_sha256": row["input_sha256"], "observations": observations,
        "unchanged_source_computation": True, "assembly_modified": False, "runtime_guard_refusal_exercised": False,
        "tile_size": 32, "prior_all_fallback_runs_retained": True, "prior_observer_failure_retained": True, "controlled_cost_evidence": False,
        "complete_62_case_replay": False, "OLO_compact_entry_condition_complete": False,
        "full_goal_complete": False, "reports": {"build": str(BUILD.relative_to(ROOT)),
            "replay": str(REPLAY.relative_to(ROOT)), "earlier": [str(p.relative_to(ROOT)) for p in OLD]},
        "bindings": bindings}
    portable = json.loads(json.dumps({k: v for k, v in report.items() if k != "bindings"}))
    for item in portable["observations"].values():
        item.pop("update_order")
    portable["report"] = str((work / "report.json").relative_to(ROOT))
    with PORTABLE.open("x") as out:
        out.write(json.dumps(portable, indent=2) + "\n")
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "passed", "updates_per_mode": 400,
        "updating_tile_pairs": len(observations["tiled"]["updating_tile_pairs"]), "bindings": len(bindings)}))


if __name__ == "__main__":
    main()
