"""Observe emitted Clight dispatch and unmodified x86-64 write/comparison order."""
import json
from pathlib import Path
import re
import subprocess

import native_loaded_offset_affine as suite
from validate_loaded_offset_affine import validate
from native_memory_layout_sequence_paths import printer_for_gcc
from native_affine_nest_paths import closing_brace
from audit_interface_clight import sha


def expected_branches(row, installed):
    if not installed:
        return [0,0]
    kind,view,start,n,m,p,_ = row
    result = [0,0]
    for initial in [start,0] if kind == 6 else [start]:
        accepted = (initial == 0 and 1 <= suite.word(n+1) <= 4 and 1 <= m < 5 and view != 7
                    and (suite.DEPTHS[kind] != 3 or 1 <= p < 5)
                    and view not in [1,2] and (kind != 2 or view not in [4,6]))
        result[0 if accepted else 1] += 1
    return result


def clight_probe(name, facts):
    directory = suite.WORK/name
    source = printer_for_gcc((directory/(suite.SOURCE.stem+".light.c")).read_text())
    names = suite.NAMES+["loaded_small2"]
    counts = {}
    for slot,function in enumerate(names):
        body = suite.function_body(source,function)
        insertions = []
        for condition in re.finditer(r"if \(\$[0-9]+\) \{",body):
            opening = condition.end()-1
            end = closing_brace(body,opening)
            no = re.match(r"\s*else\s*\{",body[end+1:])
            if no is None:
                continue
            fallback = end+1+no.end()-1
            finish = closing_brace(body,fallback)
            if "< *$limit" not in body[fallback:finish] or "*($a" not in body[opening:end]:
                continue
            insertions += [(opening+1,f"guard_fast[{slot}]++;"),(fallback+1,f"guard_fallback[{slot}]++;")]
        counts[function] = len(insertions)//2
        assert counts[function] == ((2 if function == "loaded_twice2" else 1)
            if facts["functions"][function]["guarded"] else 0),(name,function,counts)
        changed = body
        for offset,text in sorted(insertions,reverse=True):
            changed = changed[:offset]+text+changed[offset:]
        source = source.replace(body,changed,1)
    source = f"int guard_fast[{len(names)}],guard_fallback[{len(names)}];\n"+source
    calls = []
    for row in suite.cases():
        slot = row[0]
        calls += [f"guard_fast[{slot}]=0;guard_fallback[{slot}]=0;loaded_case("+",".join(map(suite.literal,row))+");",
                  f'printf("PATH %d %d\\n",guard_fast[{slot}],guard_fallback[{slot}]);']
    calls += ['loaded_short_run();printf("PATH %d %d\\n",guard_fast[7],guard_fallback[7]);']
    source += "\nint main(void){"+"\n".join(calls)+"return 0;}\n"
    src = directory/"branch-diagnostic.c"
    src.write_text(source)
    binary = directory/"branch-diagnostic"
    subprocess.run(["gcc","-O0","-fwrapv","-Wno-builtin-declaration-mismatch","-Wno-discarded-qualifiers",
                    str(src),"-o",str(binary)],check=True,capture_output=True)
    output = subprocess.check_output([str(binary)],text=True,timeout=90)
    (directory/"branch-output.txt").write_text(output)
    lines = output.splitlines()
    actual = [list(map(int,line.split()[1:])) for line in lines if line.startswith("PATH ")]
    expected = [expected_branches(row,facts["functions"][suite.NAMES[row[0]]]["guarded"]) for row in suite.cases()]
    expected.append([0,1])
    assert actual == expected,[(suite.cases()[i] if i<len(suite.cases()) else "short",a,e)
        for i,(a,e) in enumerate(zip(actual,expected)) if a != e]
    assert "\n".join(line for line in lines if not line.startswith("PATH "))+"\n" == suite.expected_output()
    return {"calls":len(expected),"dispatch_sites":counts,"fast":sum(a[0] for a in actual),
        "fallback":sum(a[1] for a in actual),"expected_and_actual_branches":actual,
        "artifacts":{p:sha(directory/p) for p in [src.name,binary.name,"branch-output.txt"]},
        "machine_code_path_claim":False}


def machine_probe(configuration,name,kind,view,order,*,comparisons=False):
    directory = suite.WORK/configuration
    binary = directory/"program"
    if kind == 7:
        entry = '''gdb.execute("break loaded_short_run",to_string=True)
gdb.execute("run",to_string=True)
gdb.execute("delete breakpoints",to_string=True)
gdb.execute("break loaded_small2",to_string=True)
gdb.execute("continue",to_string=True)'''
        function,a_register,bound_register = "loaded_small2","rdi","rsi"
        watch_indices = [0,1]
        expected_public,expected_bound = [2,1],1
        expected_values = [1,1]
    else:
        function,a_register,bound_register = suite.NAMES[kind],"rdi","rcx"
        relation = {0:"$rsi != $rdi && $rsi-$rdi != 4 && $rsi-$rdi != 4096 && $rcx != $rdi",
                    1:"$rcx == $rdi",2:"$rcx-$rdi == 512",3:"$rcx-$rdi == 7200",
                    4:"$rsi == $rdi && $rdx == $rdi",5:"$rsi-$rdi == 4096 && $rdx-$rdi == 8192",
                    6:"$rsi-$rdi == 4 && $rdx-$rdi == 8"}[view]
        entry = f'''gdb.execute("break {function} if $r8d == 0 && $r9d == 4 && *(int*)$rcx == 3 && ({relation})",to_string=True)
gdb.execute("run",to_string=True)'''
        watch_indices = [48,128,256]
        words = list(map(int,suite.run_model((kind,view,0,3,4,1,5))[0].split()))
        expected_public,expected_bound = words[7:12],words[12]
        expected_values = [words[13+suite.CENTER+index] for index in order]
        if kind == 6:
            # The first pass has changed each watched cell once, the second twice.
            expected_values = [words[13+suite.CENTER+index]-(5+i-j) for index in order[:3]
                for i,j in [(index//128,(index%128)//16)]]+expected_values[3:]
    commands = directory/(name+".gdb")
    public_names = ["lm_i","lm_j"] if kind == 7 else ["lm_i","lm_j","lm_k","lm_K","lm_L"]
    commands.write_text("set pagination off\nset confirm off\nset startup-with-shell off\nset inferior-tty /dev/null\npython\n"+f'''
import gdb,json,re
{entry}
pointer=int(gdb.parse_and_eval("${a_register}"))
bound=int(gdb.parse_and_eval("${bound_register}"))
events=[]
comparison_events=[]
class Write(gdb.Breakpoint):
    def __init__(self,index):
        self.index=index
        self.lvalue="*((int*) %d)" % (pointer+4*index)
        super().__init__(self.lvalue,gdb.BP_WATCHPOINT,wp_class=gdb.WP_WRITE,internal=True)
    def stop(self):
        events.append([self.index,int(gdb.parse_and_eval(self.lvalue))])
        return False
class Comparison(gdb.Breakpoint):
    def __init__(self,pc,first,second):
        self.first,self.second=first,second
        super().__init__("*0x%x" % pc,internal=True)
    def stop(self):
        a=int(gdb.parse_and_eval("$"+self.first))
        b=int(gdb.parse_and_eval("$"+self.second))
        other=b if a==bound else a if b==bound else None
        if other is not None and pointer<=other<=pointer+8 and (other-pointer)%4==0:
            comparison_events.append((other-pointer)//4)
        return False
class Finished(gdb.FinishBreakpoint):
    def stop(self): return True
watches=[Write(index) for index in {watch_indices!r}]
comparison_sites=[]
if {comparisons!r}:
    begin=int(gdb.parse_and_eval("&{function}"))
    instructions=gdb.selected_frame().architecture().disassemble(begin,begin+{suite.machine_bytes(binary,function)})
    registers={{"rax","rbx","rcx","rdx","rsi","rdi","rbp","rsp"}}|{{"r"+str(i) for i in range(8,16)}}
    for ins in instructions:
        match=re.fullmatch(r"cmp[q]?\\s+%([a-z0-9]+),%([a-z0-9]+)",ins["asm"].strip())
        if match and set(match.groups())<=registers:
            comparison_sites.append(Comparison(ins["addr"],*match.groups()))
    assert comparison_sites,"no pointer comparison instruction identified"
finish=Finished(gdb.newest_frame(),internal=True)
gdb.execute("continue",to_string=True)
assert [i for i,v in events]=={order!r},events
assert [v for i,v in events]=={expected_values!r},events
public=[int(gdb.parse_and_eval("*(int*)&"+n)) for n in {public_names!r}]
assert public=={expected_public!r},public
final_bound=int(gdb.parse_and_eval("*((int*) %d)" % bound))
assert final_bound=={expected_bound!r},final_bound
if {comparisons!r}: assert comparison_events==[0,1],comparison_events
print("GUARDCERT_LOADED_AFFINE_PATH "+json.dumps({{"writes":events,"public":public,
    "final_bound":final_bound,"comparison_indices":comparison_events,"comparison_sites":len(comparison_sites)}}))
gdb.execute("kill",to_string=True)
end
''')
    result = subprocess.run(["gdb","-q","-batch","-x",str(commands),str(binary)],capture_output=True,text=True,timeout=120)
    log = directory/(name+".gdb.log")
    log.write_text(result.stdout+result.stderr)
    parsed = re.findall(r"^GUARDCERT_LOADED_AFFINE_PATH (.*)$",result.stdout,re.MULTILINE)
    assert result.returncode == 0 and len(parsed) == 1,(name,result.stdout,result.stderr)
    observed = json.loads(parsed[0])
    print(configuration,name,observed,flush=True)
    return {"configuration":configuration,"name":name,"kind":kind,"view":view,
        "observed":observed,"commands_sha256":sha(commands),"log_sha256":sha(log),"binary_sha256":sha(binary)}


def main():
    native = validate()
    branches = {name:clight_probe(name,native["configurations"][name]) for name in ["interchange","tile-2-3"]}
    probes = []
    for name in ["disabled","interchange","tile-2-3"]:
        order = {"disabled":[48,128,256],"interchange":[128,256,48],"tile-2-3":[128,48,256]}[name]
        probes += [machine_probe(name,"three-axis",1,0,order),
                   machine_probe(name,"multi-array",2,0,order),
                   machine_probe(name,"repeated-regions",6,0,order+order)]
    for name in ["interchange","tile-2-3"]:
        order = [128,256,48] if name == "interchange" else [128,48,256]
        probes += [machine_probe(name,"same-block-slices",2,5,order),
                   machine_probe(name,"body-alias-fallback",2,4,[48,128,256]),
                   machine_probe(name,"partial-body-alias-fallback",2,6,[48,128,256]),
                   machine_probe(name,"bound-first-write",4,1,[48,128]),
                   machine_probe(name,"bound-second-row",4,2,[48,128]),
                   machine_probe(name,"short-source",7,0,[0,1],comparisons=True)]
    report = {"status":"passed","native_report_sha256":sha(suite.WORK/"report.json"),
        "compiler_sha256":sha(suite.COMPILER),"verification_script_sha256":sha(Path(__file__)),
        "helper_sources":{p:sha(suite.ROOT/p) for p in ["scripts/native_loaded_offset_affine.py",
            "scripts/validate_loaded_offset_affine.py","scripts/native_affine_nest_paths.py",
            "scripts/native_memory_layout_sequence_paths.py","scripts/audit_interface_clight.py"]},
        "clight_branch_probes":branches,"instrumented_clight_calls":sum(v["calls"] for v in branches.values()),
        "unmodified_machine_probes":probes,"machine_probe_count":len(probes),
        "store_order_observes_actual_reordering_and_tiling":True,
        "short_source_pointer_comparisons_stop_before_future_unlicensed_address":True,
        "timing_or_profitability_measured":False}
    path = suite.WORK/"path-report.json"
    path.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"passed","machine_probes":len(probes),"clight_calls":report["instrumented_clight_calls"],
                      "report_sha256":sha(path)},indent=2))


if __name__ == "__main__":
    main()
