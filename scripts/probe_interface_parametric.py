"""Observe an accepted interchange and a refused entry in each real executable.

This x86-64/GDB probe uses two array writes to distinguish source iteration
order from interchange order. It is a functional witness, not a performance
measurement or an addition to the formal correctness theorem.
"""
import json
import re
import subprocess
from pathlib import Path

from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/interface-parametric-native"
PROBES = {
    "accepted": {"function": "affine_growing", "arguments": [0, 2, 2, 0], "indices": [1, 20],
                 "expected_order": [20, 1], "expected_values": [44, 8]},
    "refused-start": {"function": "affine_growing", "arguments": [2, 4, 5, 1], "indices": [41, 60],
                      "expected_order": [41, 60], "expected_values": [82, 118]},
    "refused-empty-first-row": {"function": "affine_growing", "arguments": [0, 3, 0, 0], "indices": [21, 40],
                                "expected_order": [21, 40], "expected_values": [45, 81]},
    "accepted-negative-coefficient": {"function": "affine_descending", "arguments": [0, 2, 5, -1], "indices": [1, 20],
                                      "expected_order": [20, 1], "expected_values": [44, 8]},
    "refused-negative-last-width": {"function": "affine_descending", "arguments": [0, 3, 3, 0], "indices": [1, 20],
                                    "expected_order": [1, 20], "expected_values": [8, 44]},
}


def main():
    results = {}
    for mode in ["direct", "shared"]:
        directory = WORK / "parametric" / mode / "interchange"
        assembly, binary = directory / "program.s", directory / "program"
        for name, probe in PROBES.items():
            function = probe["function"]
            body = re.search(r"^" + re.escape(function) + r":\n(.*?)^\s*\.cfi_endproc", assembly.read_text(),
                             re.MULTILINE | re.DOTALL).group(1)
            frame = int(re.search(r"subq\s+\$(\d+),\s*%rsp", body).group(1))
            before_initializer = body.split("$-999", 1)[0]
            array_offset = int(re.findall(r"leaq\s+(\d+)\(%rsp\)", before_initializer)[-1])
            condition = " && ".join(f"${register} == {value}" for register, value in
                                     zip(["edi", "esi", "edx", "ecx"], probe["arguments"]))
            commands = directory / (name + ".gdb")
            commands.write_text("set pagination off\nset confirm off\nset startup-with-shell off\nset inferior-tty /dev/null\npython\n" + f'''
import gdb, json
gdb.execute("break {function} if {condition}", to_string=True)
gdb.execute("run", to_string=True)
original_stack = int(gdb.parse_and_eval("$rsp"))
gdb.execute("si", to_string=True)
stack = int(gdb.parse_and_eval("$rsp"))
assert original_stack - stack == {frame}, "unexpected prologue"
events = []
class ArrayWrite(gdb.Breakpoint):
    def __init__(self, index):
        self.index = index
        self.watched_lvalue = "*((int*) %d)" % (stack + {array_offset} + index * 4)
        super().__init__(self.watched_lvalue, gdb.BP_WATCHPOINT, wp_class=gdb.WP_WRITE, internal=True)
    def stop(self):
        value = int(gdb.parse_and_eval(self.watched_lvalue))
        if value != -999 and all(index != self.index for index, old in events):
            events.append((self.index, value))
        return len(events) == 2
watchpoints = [ArrayWrite(index) for index in {probe["indices"]!r}]
gdb.execute("continue", to_string=True)
assert [index for index, value in events] == {probe["expected_order"]!r}, events
assert [value for index, value in events] == {probe["expected_values"]!r}, events
print("GUARDCERT_PROBE " + json.dumps(events))
gdb.execute("kill", to_string=True)
end
''')
            process = subprocess.run(["gdb", "-q", "-batch", "-x", commands, binary],
                                     cwd=ROOT, capture_output=True, text=True, timeout=180)
            (directory / (name + ".gdb.log")).write_text(process.stdout + process.stderr)
            assert process.returncode == 0, (mode, name, process.stdout, process.stderr)
            observations = re.findall(r"^GUARDCERT_PROBE (.*)$", process.stdout, re.MULTILINE)
            assert len(observations) == 1, (mode, name, process.stdout, process.stderr)
            events = json.loads(observations[0])
            results[mode + "/" + name] = {
                **probe, "observed_writes": events, "binary_sha256": sha(binary),
                "assembly_sha256": sha(assembly), "commands_sha256": sha(commands),
                "gdb_log_sha256": sha(directory / (name + ".gdb.log")),
                "array_stack_offset": array_offset, "stack_frame_bytes": frame,
            }
            print(mode, name, events, flush=True)
    report = {"status": "passed", "verification_script_sha256": sha(Path(__file__)),
              "architecture": "x86-64 System V", "probes": results,
              "actual_accepted_and_refused_orders_observed": True, "performance_measured": False}
    (WORK / "runtime-order-report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
