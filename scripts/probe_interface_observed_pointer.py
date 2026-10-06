"""Observe actual iteration order and whether the pointer scan executes."""
import argparse
import json
import re
import subprocess
from pathlib import Path

from native_interface_observed_pointer import ROOT, WORK, check_build, model, sha

CONFIGURATIONS = ["direct-interchange-2", "schedule-interchange-2"]
PROBES = {
    "shortcut-separated": {"args": [0, 0, 0, 2, 2, 1, 0], "relation": "$rdi == $rsi", "scan": False, "candidate": True},
    "overlap-fallback": {"args": [0, 0, 0, 7, 2, 1, 0], "relation": "$rdi == $rsi", "scan": True, "candidate": False},
    "distinct-base-scan-accept": {"args": [0, 1, 0, 2, 2, 1, 0], "relation": "($rsi-$rdi > 8192 || $rdi-$rsi > 8192)", "scan": True, "candidate": True},
    "shifted-base-scan-reject": {"args": [0, 2, 0, 2, 2, 1, 0], "relation": "$rsi-$rdi == -376", "scan": True, "candidate": False},
    "empty-null-source-branch": {"args": [2, 6, 0, 0, 2, 1, -2147483648], "relation": "$rdi == 0 && $rsi == 0", "scan": False, "candidate": False},
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--configurations")
    args = parser.parse_args()
    selected = args.configurations.split(",") if args.configurations else CONFIGURATIONS
    assert set(selected) <= set(CONFIGURATIONS)
    stamp = check_build()
    results = {}
    for configuration in selected:
        directory = WORK / configuration
        binary, assembly = directory / "affine", directory / "affine.s"
        symbols = subprocess.check_output(["nm", "-S", str(binary)], text=True)
        for name, probe in PROBES.items():
            which, kind, start, n, m, s, t = probe["args"]
            function = "observed_conditional2" if which == 2 else "observed_flat2"
            size_match = re.search(r"^[0-9a-f]+ ([0-9a-f]+) T " + function + r"$", symbols, re.MULTILINE)
            assert size_match, function
            size = int(size_match[1], 16)
            condition = (f"$edx == {start} && $ecx == {n} && $r8d == {m} && $r9d == {s} && "
                         f"*(int*)($rsp+8) == {t} && ({probe['relation']})")
            indices = [] if kind == 6 else [33, 48]
            order = ([48, 33] if probe["candidate"] else [33, 48]) if indices else []
            _, arrays = model(probe["args"], interchange=probe["candidate"])
            values = [arrays[0][256+index] for index in order]
            commands = directory / (name + ".gdb")
            commands.write_text("set pagination off\nset confirm off\nset startup-with-shell off\n"
                "set inferior-tty /dev/null\npython\n" + f'''
import gdb, json, re
gdb.execute("break {function} if {condition}", to_string=True)
gdb.execute("run", to_string=True)
pointer = int(gdb.parse_and_eval("$rdi"))
incoming_q = int(gdb.parse_and_eval("$rsi"))
begin = int(gdb.parse_and_eval("(void*){function}"))
instructions = gdb.selected_frame().architecture().disassemble(begin, begin+{size})
# The selected functions use int32 control and data arithmetic. Their only
# comparisons of 64-bit registers are the base equality and footprint address
# comparisons. Match registers used as operands, excluding memory-address
# registers in int32 comparisons. Inspect actual linked machine instructions.
pattern = re.compile(r"(?:^|,)\\s*%r(?:ax|bx|cx|dx|si|di|bp|sp|[89]|1[0-5])(?:\\s|$)")
comparisons = [item for item in instructions if item["asm"].split()[0].startswith("cmp")
    and pattern.search(item["asm"].split(None,1)[1])]
assert len(comparisons) > 1, comparisons
for item in comparisons:
    operands = re.sub(r"\\s+", "", item["asm"].split(None,1)[1])
    item["kind"] = "base" if operands in ["%rdi,%rsi", "%rsi,%rdi"] else "scan"
events, pointer_comparisons = [], []
base_comparisons, scan_comparisons = [], []
class Comparison(gdb.Breakpoint):
    def __init__(self, instruction):
        self.instruction = instruction
        super().__init__("*%d" % instruction["addr"], internal=True)
    def stop(self):
        if self.instruction["kind"] == "base":
            assert int(gdb.parse_and_eval("$rdi")) == pointer
            assert int(gdb.parse_and_eval("$rsi")) == incoming_q
        pointer_comparisons.append(self.instruction["addr"]-begin)
        (base_comparisons if self.instruction["kind"] == "base" else scan_comparisons).append(self.instruction["addr"]-begin)
        return False
class ArrayWrite(gdb.Breakpoint):
    def __init__(self, index):
        self.index = index
        self.lvalue = "*((int*) %d)" % (pointer+index*4)
        super().__init__(self.lvalue, gdb.BP_WATCHPOINT, wp_class=gdb.WP_WRITE, internal=True)
    def stop(self):
        if all(index != self.index for index, value in events):
            events.append((self.index, int(gdb.parse_and_eval(self.lvalue))))
        return False
class Finished(gdb.FinishBreakpoint):
    def stop(self):
        return True
breaks = [Comparison(instruction) for instruction in comparisons]
watches = [ArrayWrite(index) for index in {indices!r}]
finished = Finished(gdb.newest_frame(), internal=True)
gdb.execute("continue", to_string=True)
assert [index for index, value in events] == {order!r}, events
assert [value for index, value in events] == {values!r}, events
expected = {('"scan"' if probe['scan'] else '0' if kind == 6 else '2')}
if expected == "scan":
    assert scan_comparisons, pointer_comparisons
else:
    assert not scan_comparisons, pointer_comparisons
    assert len(base_comparisons) == expected, pointer_comparisons
print("GUARDCERT_OBSERVED " + json.dumps({{"writes":events,"pointer_comparisons":pointer_comparisons,
    "base_comparisons":base_comparisons,"scan_comparisons":scan_comparisons,
    "static_pointer_comparison_sites":[{{"offset":item["addr"]-begin,"asm":item["asm"],"kind":item["kind"]}} for item in comparisons]}}))
gdb.execute("kill", to_string=True)
end
''')
            process = subprocess.run(["gdb", "-q", "-batch", "-x", str(commands), str(binary)],
                                     cwd=ROOT, capture_output=True, text=True, timeout=180)
            log = directory / (name+".gdb.log")
            log.write_text(process.stdout+process.stderr)
            assert process.returncode == 0, (configuration, name, process.stdout, process.stderr)
            observations = re.findall(r"^GUARDCERT_OBSERVED (.*)$", process.stdout, re.MULTILINE)
            assert len(observations) == 1, (configuration, name, process.stdout, process.stderr)
            observed = json.loads(observations[0])
            results[configuration+"/"+name] = {**probe, "expected_order": order, "expected_values": values,
                **observed, "binary_sha256": sha(binary), "assembly_sha256": sha(assembly),
                "commands_sha256": sha(commands), "gdb_log_sha256": sha(log)}
            print(configuration, name, observed["writes"], len(observed["pointer_comparisons"]), flush=True)
    report = {"status": "passed", "compiler_sha256": stamp["compiler_sha256"],
              "verification_script_sha256": sha(Path(__file__)), "architecture": "x86-64 System V",
              "probes": results, "full_configuration_suite": not bool(args.configurations),
              "actual_shortcut_scan_and_iteration_paths_observed": True,
              "performance_measured": False,
              "scope": "functional instruction-path witnesses; compare-site classification is specific to these int32 fixtures"}
    (WORK / ("runtime-path-smoke-report.json" if args.configurations else "runtime-path-report.json")).write_text(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
