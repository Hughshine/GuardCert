"""Observe real original-matmul tile entries in unchanged compiler assembly."""
import argparse
import itertools
import json
from pathlib import Path
import re
import subprocess

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_combined_residual_traced_corpus import checked

SOURCE = ROOT / "build/benchmark-alignment/current-double-combined-residual-quiet-attempts/corpus-v1/report.json"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not re.fullmatch("[a-z0-9-]+", args.attempt):
        raise ValueError("Use a new simple attempt")
    bindings = {}
    report = checked(SOURCE, bindings)
    row = next(row for row in report["results"] if row["case"] == "matmul" and row["variant"] == "original")
    config = row["configurations"]["tiled"]
    if config["status"] != "native_match" or config["typed_installed"][2] != 1:
        raise ValueError("Expected the original installed matmul and its complete output")
    source = SOURCE.parent / "matmul-original/tiled"
    assembly = permitted(source / "program.s")
    main = assembly.read_text().split("main:\n", 1)[1]
    # The point-loop initializer follows the three tile-loop guards. The
    # selected original's emitted Clight maps tile order to i, k, j.
    point_headers = list(re.finditer(
        r"\tmovq\t%([a-z0-9]+), %([a-z0-9]+)\n"
        r"\tsall\t\$5, %[a-z0-9]+\n"
        r"\tleal\t32\(%[a-z0-9]+\), %[a-z0-9]+\n"
        r"(\.L\d+):\n\tcmpl\t", main))
    if len(point_headers) != 2 or point_headers[0][1] != "r13" or point_headers[1][1] != "r14":
        raise ValueError("Unexpected emitted original-matmul coordinate allocation")
    work = ROOT / "build/double-tree-combined-residual/matmul-path-attempts" / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work / "script.py").write_bytes(Path(__file__).read_bytes())
    binary = work / "program"
    command = ["gcc", "-Wa,-L", "-no-pie", str(assembly), "-lm", "-o", str(binary)]
    link = subprocess.run(command, capture_output=True, text=True)
    (work / "link.stdout").write_text(link.stdout)
    (work / "link.stderr").write_text(link.stderr)
    if link.returncode:
        raise ValueError("Observation linking failed")
    symbols = subprocess.check_output(["nm", "-a", str(binary)], text=True)
    disassembly = subprocess.check_output(["objdump", "-d", "--disassemble=main", str(binary)], text=True)
    (work / "symbols.txt").write_text(symbols)
    (work / "disassembly.txt").write_text(disassembly)
    instructions = [(m[1], m[2]) for m in re.finditer(
        r"^\s*([0-9a-f]+):\s+(?:[0-9a-f]{2}\s+)+\s*([^\n]+)", disassembly, re.M)]
    label = point_headers[0][3]
    point = re.search(r"^([0-9a-f]+) [tT] " + re.escape(label) + r"$", symbols, re.M)
    if point is None:
        raise ValueError("Missing point-loop header symbol")
    index = next(i for i, (address, _) in enumerate(instructions) if address == point[1].lstrip("0"))
    initializer = instructions[index - 3]
    if not re.fullmatch(r"mov\s+%r13,%rsi", initializer[1]):
        raise ValueError("Expected the actual i-point initializer")
    stores = [(address, text) for address, text in instructions
              if re.search(r"\bmovsd\s+%xmm2,0x10\(%r15,%r10,8\)", text)]
    if len(stores) != 1:
        raise ValueError("Expected one actual candidate update position")
    commands = ["set pagination off", "set confirm off", "set disable-randomization off",
                "set $tiles=0", "set $first_update=0", "break *0x" + initializer[0],
                "commands", "silent", "set $tiles=$tiles+1",
                'printf "GUARDCERT_MATMUL_TILE %d,%d,%d\\n", $r13d,$ebp,$r14d',
                "continue", "end", "break *0x" + stores[0][0], "commands", "silent",
                "set $first_update=$first_update+1",
                'printf "GUARDCERT_MATMUL_FIRST_POINT %d,%d,%d\\n", $esi,$edi,$edx',
                "disable 2", "continue", "end", "run",
                'printf "GUARDCERT_MATMUL_COUNTS %d,%d\\n", $tiles,$first_update']
    script = work / "debugger.gdb"
    script.write_text("\n".join(commands) + "\n")
    result = subprocess.run(["gdb", "--batch", "--nx", "-x", str(script), str(binary)],
                            capture_output=True, text=True, timeout=60)
    (work / "debugger.stdout").write_text(result.stdout)
    (work / "debugger.stderr").write_text(result.stderr)
    triples = [list(map(int, x)) for x in re.findall(r"GUARDCERT_MATMUL_TILE (\d+),(\d+),(\d+)", result.stdout)]
    first = [list(map(int, x)) for x in re.findall(r"GUARDCERT_MATMUL_FIRST_POINT (\d+),(\d+),(\d+)", result.stdout)]
    counts = re.search(r"GUARDCERT_MATMUL_COUNTS (\d+),(\d+)", result.stdout)
    expected = [list(x) for x in itertools.product(range(3), repeat=3)]
    output = permitted(source / "native.stdout").read_text().strip()
    passed = (result.returncode == 0 and triples == expected and first == [[0, 0, 0]]
              and counts is not None and list(map(int, counts.groups())) == [27, 1]
              and output in result.stdout)
    for path in [Path(__file__), assembly, *[p for p in work.rglob("*") if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    summary = {"status": "passed" if passed else "rejected", "case": "original-matmul",
               "compiler_entrypoint": report["compiler_entrypoint"],
               "whole_program_theorem": report["whole_program_theorem"],
               "original_input": row["input"], "original_input_sha256": row["input_sha256"],
               "tile_size": 32, "input_dimensions": [96, 96, 96],
               "tile_order": ["i", "k", "j"], "tile_triples": triples,
               "expected_tile_triples": expected, "first_observed_update": first,
               "first_update_breakpoint_disabled_after_observation": True,
               "complete_original_output_matches_in_debugger": output in result.stdout,
               "assembly_not_modified": True, "target_not_instrumented": True,
               "runtime_guard_refusal_exercised_by_this_input": False,
               "all_candidate_updates_counted": False,
               "full_goal_complete": False, "bindings": bindings}
    (work / "report.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"status": summary["status"], "tile_entries": len(triples),
                      "first_observed_update": first, "complete_output_matches": output in result.stdout}), flush=True)
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
