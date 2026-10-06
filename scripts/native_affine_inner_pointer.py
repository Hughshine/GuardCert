"""Exercise the new affine-inner compiler with full buffers and public exits.

This suite binds current proof/extraction artifacts, checks actual frontend
installation, and distinguishes source/candidate order with machine probes.
It makes no timing or generality claim from the number of calls.
"""
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

from native_zero_trip import function_body

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build/affine-pointer-compiler/native"
COMPILER = ROOT / "build/affine-pointer-compiler/compiler/ccomp"
PROOF = ROOT / "build/affine-pointer-compiler/proof/report.json"
SOURCE = ROOT / "examples/native_affine_inner_pointer.c"
ENTRY = "ClightAffineInnerPointerCompiler.compile_affine_inner_pointer"
NAMES = ["affine_triangle", "affine_ragged", "affine_missing"]
TRIANGLE = "(map-index ((swap 0)) (loop (constant 0) (var 0) (loop (var 0) (var 1) (each (instr current ((var 0) (var 1) (var 2) (var 3)))))))"
CEILING = "(map-index ((swap 0)) (loop (constant 0) (sum (scale 2 (var 0)) (constant -1)) (loop (div (sum (var 0) (constant 1)) 2) (var 1) (each (instr current ((var 0) (var 1) (var 2) (var 3)))))))"
RAGGED = "(map-index ((swap 0)) (loop (constant 0) (sum (scale 2 (var 0)) (constant -1)) (loop (constant 0) (var 1) (guard (le (var 1) (scale 2 (var 0))) (each (instr current ((var 0) (var 1) (var 2) (var 3))))))))"
SCHEDULE = "(schedule-explicit ((((0 0 0 1) 0) ((0 0 1 0) 0) (() 0))) ((swap 0)))"
INVALID = TRIANGLE.replace("(loop (var 0) (var 1)", "(loop (var 0) (sum (var 1) (constant -1))")
TILE_MISSING_ROW = """(tile-loop 4 1
  (loop (constant 0) (constant 17)
    (loop (constant 0) (constant 64)
      (loop (scale 4 (var 1)) (sum (scale 4 (var 1)) (constant 4))
        (loop (var 1) (sum (var 1) (constant 1))
          (guard (and (le (var 1) (sum (var 4) (constant -2)))
                      (le (var 0) (var 1)))
            (each (instr current ((var 1) (var 0) (var 4) (var 5))))))))))"""


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inputs():
    controls = [(0,0,-13), (0,1,-13), (0,3,0), (0,32,7), (0,63,-13),
                (0,64,7), (1,3,0), (3,3,0), (0,-1,0)]
    return [(which,kind,*control) for which in range(3) for kind in range(3) for control in controls]


def model(arguments, interchange=False):
    which,kind,start,n,a = arguments
    storage,other = list(range(20000)), [3*x+7 for x in range(20000)]
    q,base = (storage,4500) if kind == 0 else (storage,499) if kind == 2 else (other,4500)
    rp,rq = storage[4500], q[base] if which != 2 else 0
    width = lambda i: (2*i+1 if which == 1 else i+1)
    points = [(i,j) for i in range(start,n) for j in range(width(i))]
    if interchange:
        points.sort(key=lambda point: (point[1],point[0]))
    for i,j in points:
        storage[4500+32+64*i+j] = q[base+4096+64*i+j]+a
    final_i = n if start < n else start
    final_j = final_k = width(n-1) if start < n else None
    if final_j is None:
        final_j,final_k = 77,91
    storage[4500] = rp+17
    q[base] = rq+19
    header = [*arguments,final_i,final_j,final_k,rp,rq,31+final_i+final_j+final_k,storage[4597]]
    return " ".join(map(str,header+[value for pair in zip(storage,other) for value in pair]))+"\n",storage


def check_build():
    proof = json.loads(PROOF.read_text())
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    assert proof["status"] == "compiled" and proof["whole_program_entrypoint"] == ENTRY
    assert proof["additional_global_axioms"] == []
    assert stamp["proved_entrypoint"] == ENTRY and stamp["proof_report_sha256"] == sha(PROOF)
    assert stamp["compiler_sha256"] == sha(COMPILER)
    for path,digest in (stamp["proof_sources"] | stamp["native_sources"]).items():
        assert sha(ROOT / path) == digest,path
    for path,digest in proof["compiled_objects"].items():
        assert sha((ROOT / path).with_suffix(".vo")) == digest,path
    return stamp


def run_configuration(name,syntax,extra,expected,functions):
    directory = WORK / name
    directory.mkdir(parents=True,exist_ok=True)
    proposal = directory / "candidate.sexp"
    proposal.write_text(syntax+"\n")
    command = [str(COMPILER),"-conf",str(COMPILER.parent / "compcert.ini"),"-stdlib",
               str(COMPILER.parent / "runtime"),"-dclight","-S","-o",str(directory / "affine.s"),str(SOURCE)]
    process = subprocess.run(command,cwd=directory,env=os.environ | {"GUARDCERT_LOOP_CANDIDATE":str(proposal)} | extra,
                             capture_output=True,text=True,timeout=900)
    (directory / "compiler.log").write_text(process.stdout+process.stderr)
    assert process.returncode == 0,(name,process.stdout,process.stderr)
    dump = directory / (SOURCE.stem+".light.c")
    found = {function for function in NAMES if re.search(r"\$[pq] == \$[pq]",function_body(dump.read_text(),function))}
    assert found == set(functions),(name,found,functions)
    subprocess.run(["gcc",str(directory / "affine.s"),"-o",str(directory / "affine")],check=True)
    actual = subprocess.check_output([str(directory / "affine")],text=True,timeout=120)
    assert actual == expected,name
    (directory / "output.txt").write_text(actual)
    result = {"actual_calls":len(inputs()),"installed_functions":sorted(found),"environment":extra,
              "compiled_in_this_run":True,"full_buffers_public_exits_prefix_and_suffix_match_model_and_gcc":True,
              "artifacts":{file:sha(directory / file) for file in ["candidate.sexp",dump.name,"affine.s","affine","output.txt","compiler.log"]}}
    print(name,sorted(found),len(inputs()),flush=True)
    return result


def probe(configuration,name,function,n,relation,candidate,a=0):
    directory = WORK / configuration
    binary = directory / "affine"
    _,storage = model((NAMES.index(function),2 if relation == "shifted" else 0,0,n,a),interchange=candidate)
    order = [] if n <= 1 else [160,97] if candidate else [97,160]
    values = [storage[4500+index] for index in order]
    condition = "$rdi == $rsi" if relation == "same" else "$rdi-$rsi == 16004"
    commands = directory / (name+".gdb")
    commands.write_text("set pagination off\nset confirm off\nset startup-with-shell off\nset inferior-tty /dev/null\npython\n"+f'''
import gdb,json
gdb.execute("break {function} if $edx == 0 && $ecx == {n} && $r8d == {a} && ({condition})",to_string=True)
gdb.execute("run",to_string=True)
pointer=int(gdb.parse_and_eval("$rdi"))
events=[]
class Write(gdb.Breakpoint):
    def __init__(self,index):
        self.index=index
        self.lvalue="*((int*) %d)" % (pointer+4*index)
        super().__init__(self.lvalue,gdb.BP_WATCHPOINT,wp_class=gdb.WP_WRITE,internal=True)
    def stop(self):
        if all(index != self.index for index,value in events):
            events.append((self.index,int(gdb.parse_and_eval(self.lvalue))))
        return False
class Finished(gdb.FinishBreakpoint):
    def stop(self): return True
watches=[Write(index) for index in [97,160]]
finish=Finished(gdb.newest_frame(),internal=True)
gdb.execute("continue",to_string=True)
assert [index for index,value in events] == {order!r},events
assert [value for index,value in events] == {values!r},events
print("GUARDCERT_AFFINE_PATH "+json.dumps({{"writes":events}}))
gdb.execute("kill",to_string=True)
end
''')
    process = subprocess.run(["gdb","-q","-batch","-x",str(commands),str(binary)],capture_output=True,text=True,timeout=120)
    log = directory / (name+".gdb.log")
    log.write_text(process.stdout+process.stderr)
    observed = re.findall(r"^GUARDCERT_AFFINE_PATH (.*)$",process.stdout,re.MULTILINE)
    assert process.returncode == 0 and len(observed) == 1,(name,process.stdout,process.stderr)
    print(configuration,name,json.loads(observed[0]),flush=True)
    return {"function":function,"n":n,"a":a,"pointer_relation":relation,"candidate_expected":candidate,
            "writes":json.loads(observed[0])["writes"],"commands_sha256":sha(commands),"log_sha256":sha(log),
            "binary_sha256":sha(binary)}


def main():
    WORK.mkdir(parents=True,exist_ok=True)
    stamp = check_build()
    expected = "".join(model(arguments)[0] for arguments in inputs())
    subprocess.run(["gcc","-O0",str(SOURCE),"-o",str(WORK / "reference")],check=True)
    reference = subprocess.check_output([str(WORK / "reference")],text=True,timeout=120)
    assert reference == expected,"independent model disagrees with source"
    (WORK / "reference-output.txt").write_text(reference)
    source,original = model((0,2,0,3,0))
    target,reordered = model((0,2,0,3,0),interchange=True)
    assert source != target and original[4597] == 4660 and reordered[4597] == 4723
    choices = [("triangle",TRIANGLE,{},["affine_triangle"]),
               ("ragged",RAGGED,{},["affine_ragged"]),
               ("schedule",SCHEDULE,{},["affine_triangle","affine_ragged"]),
               ("tile-2-3","(tile 2 3)",{},["affine_triangle","affine_ragged"]),
               ("tile-4-1","(tile 4 1)",{},["affine_triangle","affine_ragged"]),
               ("tile-wrong-witness","(tile-wrong-witness 4 1)",{},[]),
               ("tile-missing-row",TILE_MISSING_ROW,{},[]),
               ("tile-zero","(tile 0 3)",{},[]),
               ("ceiling-refused",CEILING,{},[]),
               ("invalid-domain",INVALID,{},[]),
               ("resource-limit",TRIANGLE,{"GUARDCERT_FM_ROWS":"0"},[])]
    results = {}
    for name,syntax,extra,functions in choices:
        results[name] = run_configuration(name,syntax,extra,expected,functions)
        (WORK / "partial-report.json").write_text(json.dumps(results,indent=2)+"\n")
    probes = {"triangle-accept":probe("triangle","accepted-order","affine_triangle",3,"same",True),
              "triangle-alias-refuse":probe("triangle","shifted-alias-source-order","affine_triangle",3,"shifted",False),
              "triangle-box-refuse":probe("triangle","overlapping-box-source-order","affine_triangle",64,"same",False,7),
              "ragged-accept":probe("ragged","accepted-order","affine_ragged",3,"same",True),
              "schedule-accept":probe("schedule","accepted-order","affine_triangle",3,"same",True),
              "tile-accept":probe("tile-4-1","accepted-order","affine_triangle",3,"same",True),
              "tile-alias-refuse":probe("tile-4-1","shifted-alias-source-order","affine_triangle",3,"shifted",False)}
    report = {"status":"passed","proved_entrypoint":ENTRY,"compiler_sha256":stamp["compiler_sha256"],
              "proof_report_sha256":sha(PROOF),"compiler_stamp_sha256":sha(COMPILER.parent / ".guard-build.json"),
              "source_sha256":sha(SOURCE),"verification_script_sha256":sha(Path(__file__)),
              "reference_output_sha256":sha(WORK / "reference-output.txt"),"configurations":results,"probes":probes,
              "unique_source_calls":len(inputs()),"calls_across_configurations":len(inputs())*len(results),
              "counterexample":{"arguments":[0,2,0,3,0],"absolute_index":4597,"source_value":4660,"unguarded_candidate_value":4723},
              "extraction_and_native_execution":True,"performance_measured":False,
              "scope":"two affine-inner source domains; mapped/schedule and tiling checks, wrong quotient witness and missing-point refusal, actual guarded paths and full buffer/public context agreement"}
    (WORK / "report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"passed","calls":report["calls_across_configurations"],"machine_probes":len(probes)}))


if __name__ == "__main__":
    main()
