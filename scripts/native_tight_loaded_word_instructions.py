"""Count instructions in untouched old/tight assembly with function-scoped Callgrind.

This is diagnostic evidence, not CPU-cycle attribution or a correctness proof.
The selected/source function runs twice (warmup plus one measured-harness call).
Complete arrays and exits are checked outside the collection scope.
"""
import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import re
import subprocess

from audit_interface_clight import ROOT, sha
import native_tight_loaded_word_cost as cost

WORK = ROOT / "build/loaded-word-machine-profile/tight-v1"
CASES = [0, 1, 7, 9, 10, 11]
SYMBOLS = {"source": "unmarked", "guarded": "selected_one"}
CALLS = 2


def parse_callgrind(text):
    """Decode instruction-position compression and exclude inclusive call costs."""
    names, counts, calls = {}, defaultdict(Counter), Counter()
    function = callee = None
    position = None
    pending_call = False
    assert "positions: instr\n" in text and "events: Ir\n" in text
    summary = int(re.search(r"^summary: (\d+)$", text, re.MULTILINE)[1])
    for line in text.splitlines():
        match = re.fullmatch(r"(c?fn)=\((\d+)\)(?: (.*))?", line)
        if match:
            kind, identifier, name = match.groups()
            if name is not None:
                assert identifier not in names or names[identifier] == name
                names[identifier] = name
            if kind == "fn":
                function, position = identifier, None
            else:
                callee = identifier
            continue
        if line.startswith("calls="):
            assert callee is not None and not pending_call
            calls[callee] += int(line.split()[0].split("=", 1)[1])
            pending_call = True
            continue
        match = re.fullmatch(r"(0x[0-9a-fA-F]+|[+-]\d+|\*|\d+) (\d+)", line)
        if not match:
            continue
        address, count = match.groups()
        if address.startswith(("+", "-")):
            assert position is not None
            position += int(address)
        elif address == "*":
            assert position is not None
        else:
            position = int(address, 0) if address.startswith("0x") else int(address)
        assert function is not None
        if pending_call:
            pending_call = False
        else:
            counts[function][position] += int(count)
    assert not pending_call
    by_name = {names[identifier]: values for identifier, values in counts.items()}
    assert sum(sum(values.values()) for values in by_name.values()) == summary
    return summary, by_name, {names[identifier]: count for identifier, count in calls.items()}


def disassemble(binary, symbol):
    text = subprocess.check_output(["objdump", "-d", "--no-show-raw-insn",
                                    "--disassemble=" + symbol, str(binary)], text=True)
    instructions = {}
    for line in text.splitlines():
        match = re.fullmatch(r"\s*([0-9a-f]+):\s+(.*)", line)
        if match:
            instructions[int(match[1], 16)] = match[2]
    assert instructions
    return text, instructions


def input_bindings():
    paths = [ROOT/"scripts/native_tight_loaded_word_instructions.py",
             ROOT/"scripts/native_tight_loaded_word_cost.py", cost.WORK/"prepared.json"]
    paths += [cost.WORK/layout/"program" for layout in cost.LAYOUTS]
    return {str(path.relative_to(ROOT)): sha(path) for path in paths}


def profile(layout, mode, case):
    directory = WORK/layout/(mode+"-"+str(case))
    directory.mkdir(parents=True)
    binary = cost.WORK/layout/"program"
    symbol = SYMBOLS[mode]
    command = ["valgrind", "--tool=callgrind", "--dump-instr=yes", "--dump-line=no",
               "--collect-atstart=no", "--toggle-collect="+symbol,
               "--callgrind-out-file="+str(directory/"callgrind.out"),
               str(binary), str(case), str(cost.MODES.index(mode)), "1"]
    with (directory/"stderr.txt").open("w") as log:
        output = subprocess.check_output(command, stderr=log, text=True, timeout=60)
    (directory/"stdout.txt").write_text(output)
    lines = output.splitlines()
    assert len(lines) == 3 and lines[0] == cost.expected_result(layout, case, 1)
    assert lines[2] == cost.expected_result(layout, case, CALLS)
    summary, functions, calls = parse_callgrind((directory/"callgrind.out").read_text())
    assert calls[symbol] == CALLS
    assert set(functions) == {symbol}, functions.keys()
    counts = functions[symbol]
    assert sum(counts.values()) == summary and summary % CALLS == 0
    assembly, instructions = disassemble(binary, symbol)
    (directory/"disassembly.txt").write_text(assembly)
    assert set(counts) <= set(instructions)
    # These particular x86 kernels lower their only array RMW writes to a
    # 32-bit mov into a base+index*4 address. Header/context writes lack this
    # addressing form. Check their dynamic count against the independent model.
    stores = {address: code for address, code in instructions.items()
              if re.match(r"mov\s+%\w+,.*\([^)]*,[^)]*,4\)", code)}
    assert stores
    body_points = sum(cost.effect(layout, case)[1].values())
    assert sum(counts[address] for address in stores) == CALLS*body_points
    return {"layout": layout, "mode": mode, "case": case, "function": symbol,
            "function_entries": calls[symbol], "instructions_total": summary,
            "instructions_per_call": summary//CALLS, "original_body_points_per_call": body_points,
            "scaled_word_stores": [{"pc": hex(address), "code": code,
                "executions_total": counts[address]} for address, code in stores.items()],
            "instruction_counts": {hex(address): count for address, count in sorted(counts.items())},
            "command": command}


def artifact_bindings():
    return {str(path.relative_to(WORK)): sha(path) for path in WORK.rglob("*")
            if path.is_file() and path.name != "report.json"}


def validate():
    cost.validate()
    report = json.loads((WORK/"report.json").read_text())
    assert report["status"] == "profiled" and report["bindings"] == input_bindings()
    assert report["artifacts"] == artifact_bindings()
    assert {(row["layout"], row["mode"], row["case"]) for row in report["profiles"]} == {
        (layout, mode, case) for layout in cost.LAYOUTS for mode in cost.MODES for case in CASES}
    for row in report["profiles"]:
        directory = WORK/row["layout"]/(row["mode"]+"-"+str(row["case"]))
        total, functions, calls = parse_callgrind((directory/"callgrind.out").read_text())
        assert total == row["instructions_total"] and calls[row["function"]] == CALLS
        assert set(functions) == {row["function"]}
        assert total % CALLS == 0 and row["instructions_per_call"] == total//CALLS
        assert row["function_entries"] == CALLS
        assert row["original_body_points_per_call"] == sum(cost.effect(row["layout"], row["case"])[1].values())
        assert {hex(pc): n for pc, n in sorted(functions[row["function"]].items())} == row["instruction_counts"]
        assert sum(store["executions_total"] for store in row["scaled_word_stores"]) == CALLS*row["original_body_points_per_call"]
        for store in row["scaled_word_stores"]:
            assert store["executions_total"] == functions[row["function"]][int(store["pc"], 16)]
        lines = (directory/"stdout.txt").read_text().splitlines()
        assert lines[0] == cost.expected_result(row["layout"], row["case"], 1)
        assert lines[2] == cost.expected_result(row["layout"], row["case"], CALLS)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    cost.validate()
    if args.validate or (WORK/"report.json").exists():
        validate()
        print(json.dumps({"status":"validated", "report_sha256":sha(WORK/"report.json")}))
        return
    assert not WORK.exists(), "Refusing to overwrite an instruction checkpoint"
    WORK.mkdir(parents=True)
    rows = []
    for layout in cost.LAYOUTS:
        for mode in cost.MODES:
            for case in CASES:
                rows.append(profile(layout, mode, case))
            print("Profiled", layout, mode, flush=True)
    report = {"status":"profiled", "bindings":input_bindings(), "artifacts":artifact_bindings(),
              "profiles":rows, "valgrind":subprocess.check_output(["valgrind","--version"], text=True).strip(),
              "protocol":{"event":"Ir", "function_toggle":True, "calls_per_profile":CALLS,
                          "assembly_modified":False, "complete_results_checked":True,
                          "inclusive_call_costs_excluded":True, "cpu_cycle_measurement":False},
              "limitations":["instruction execution counts are not native CPU time or cycle counts",
                             "warm capped examples, not a benchmark suite or general profitability claim",
                             "store-PC classification is inspected x86 diagnostic evidence, not a verified lowering theorem"]}
    (WORK/"report.json").write_text(json.dumps(report, indent=2)+"\n")
    validate()
    print(json.dumps({"status":"profiled", "profiles":len(rows), "report_sha256":sha(WORK/"report.json")}))


if __name__ == "__main__":
    main()
