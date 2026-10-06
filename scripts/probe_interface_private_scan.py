"""Observe actual accepted and alias-refused iteration orders with GDB."""
import json
import re
import subprocess
from pathlib import Path

from native_interface_private_scan import ROOT, WORK, check_build, sha

PROBES = {
    "accepted-disjoint": {"counts": [2, 3, 1], "parameters": [3, 7], "equal_pointers": False,
        "indices": [36, 51], "expected_order": [51, 36], "expected_values": [-10958, -10443]},
    "refused-alias": {"counts": [3, 2, 2], "parameters": [0, 0], "equal_pointers": True,
        "indices": [33, 48], "expected_order": [33, 48], "expected_values": [-6096, -6401]},
}


def main():
    stamp = check_build()
    results = {}
    for configuration in ["direct-interchange-2", "schedule-interchange-2"]:
        directory = WORK / configuration
        binary, assembly = directory / "affine", directory / "affine.s"
        for name, probe in PROBES.items():
            n, m, s = probe["counts"]
            u, v = probe["parameters"]
            pointer_relation = "==" if probe["equal_pointers"] else "!="
            condition = (f"$edx == 0 && $ecx == {n} && $r8d == {m} && $r9d == {s} && "
                f"*(int*)($rsp+8) == {u} && *(int*)($rsp+16) == {v} && "
                f"$rdi {pointer_relation} $rsi")
            commands = directory / (name + ".gdb")
            commands.write_text("set pagination off\nset confirm off\nset startup-with-shell off\n"
                "set inferior-tty /dev/null\npython\n" + f'''
import gdb, json
gdb.execute("break param_copy2 if {condition}", to_string=True)
gdb.execute("run", to_string=True)
pointer = int(gdb.parse_and_eval("$rdi"))
events = []
class ArrayWrite(gdb.Breakpoint):
    def __init__(self, index):
        self.index = index
        self.lvalue = "*((int*) %d)" % (pointer + index * 4)
        super().__init__(self.lvalue, gdb.BP_WATCHPOINT, wp_class=gdb.WP_WRITE, internal=True)
    def stop(self):
        if all(index != self.index for index, value in events):
            events.append((self.index, int(gdb.parse_and_eval(self.lvalue))))
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
            log = directory / (name + ".gdb.log")
            log.write_text(process.stdout + process.stderr)
            assert process.returncode == 0, (configuration, name, process.stdout, process.stderr)
            observations = re.findall(r"^GUARDCERT_PROBE (.*)$", process.stdout, re.MULTILINE)
            assert len(observations) == 1, (configuration, name, process.stdout, process.stderr)
            events = json.loads(observations[0])
            results[configuration + "/" + name] = {**probe, "observed_writes": events,
                "binary_sha256": sha(binary), "assembly_sha256": sha(assembly),
                "commands_sha256": sha(commands), "gdb_log_sha256": sha(log)}
            print(configuration, name, events, flush=True)
    report = {"status": "passed", "compiler_sha256": stamp["compiler_sha256"],
        "verification_script_sha256": sha(Path(__file__)), "architecture": "x86-64 System V",
        "probes": results, "actual_accepted_and_refused_orders_observed": True,
        "performance_measured": False, "scope": "four functional assembly execution witnesses"}
    (WORK / "runtime-order-report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
