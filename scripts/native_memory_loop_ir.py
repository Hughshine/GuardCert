"""Run the proved Loop extractor/checker on general affine control trees."""
from pathlib import Path
import copy
import hashlib
import json
import os

from memory_validator_input import ROOT, EXECUTABLE, validate

WORK = ROOT / "build" / "native-memory-loop-ir"


def var(index): return ["var", index]
def add(first, second): return ["sum", first, second]
def loop(lower, upper, body): return {"kind":"loop", "lower":lower, "upper":upper, "body":body}
def sequence(*statements): return {"kind":"seq", "statements":list(statements)}
def guard(test, body): return {"kind":"guard", "test":test, "body":body}
def instruction(arguments, *, coefficients=(1,), bias=20, reads=(), value=None):
    return {"kind":"instr", "write":[3, [*coefficients,bias]], "reads":list(reads),
            "value":value if value is not None else ["add",["mul",["parameter",0],37],7],
            "arguments":arguments}
def program(body, context=(1,)):
    return {"context":list(context), "variables":[1,2,3], "body":body}
def request(source, candidate=None):
    return {"mode":"loops", "source":source, "candidate":copy.deepcopy(source if candidate is None else candidate)}


def fixtures():
    write = instruction([var(0)])
    update = instruction([var(0)], reads=[[3,[1,20]]], value=["add",["loaded",0],11])
    pure = loop(0,var(0),write)
    triangular = loop(0,var(0),loop(0,add(var(0),1),
        instruction([var(1),var(0)],coefficients=(10,1))))
    tetrahedron = loop(0,var(0),loop(0,add(var(0),1),loop(0,add(var(0),1),
        instruction([var(2),var(1),var(0)],coefficients=(100,10,1)))))
    conjunctive = loop(0,var(0),loop(0,var(1),guard(
        ["and",["le",var(0),var(1)],["eq",var(0),var(1)]],
        sequence(instruction([var(1),var(0)],coefficients=(10,1)),sequence()))))
    fission = sequence(loop(0,var(0),write),loop(0,var(0),update))
    fusion = loop(0,var(0),sequence(write,update))
    duplicates = loop(0,var(0),sequence(update,update))
    duplicate_fission = sequence(loop(0,var(0),update),loop(0,var(0),update))
    dependent = instruction([var(0)], bias=21, reads=[[3,[1,20]]],value=["add",["loaded",0],1])
    bad_fused = loop(0,var(0),sequence(write,dependent))
    bad_fission = sequence(loop(0,var(0),write),loop(0,var(0),dependent))
    changed_domain = loop(0,add(var(0),1),write)
    divided = loop(0,["div",var(0),2],write)
    min_bound = loop(0,["min",var(0),3],write)
    disjunction = loop(0,var(0),guard(["or",["le",var(0),1],["eq",var(0),3]],write))
    write2 = instruction([var(1),var(0)],coefficients=(10,1),bias=0)
    update2 = instruction([var(1),var(0)],coefficients=(10,1),bias=0,
                          reads=[[3,[10,1,0]]],value=["add",["loaded",0],11])
    fused2 = loop(0,var(0),loop(0,var(2),sequence(write2,update2)))
    fission2 = sequence(loop(0,var(0),loop(0,var(2),write2)),loop(0,var(0),loop(0,var(2),update2)))
    assumption = ["and",["and",["le",1,var(0)],["le",var(0),12]],
                        ["and",["le",1,var(1)],["le",var(1),10]]]
    reordered = ["and",assumption[2],assumption[1]]
    return {
        "bounded-two-dimensional-fission": (request(program(guard(assumption,fused2),(1,2)),
                                                     program(guard(assumption,fission2),(1,2))),True),
        "same-domain-reordered-conjuncts": (request(program(guard(assumption,fused2),(1,2)),
                                                   program(guard(reordered,fused2),(1,2))),True),
        "unbounded-two-dimensional-fission": (request(program(fused2,(1,2)),program(fission2,(1,2))),False),
        "one-dimensional-identity": (request(program(pure)),True),
        "negative-lower-bound": (request(program(loop(-2,var(0),write))),True),
        "affine-triangular-upper-bound": (request(program(triangular)),True),
        "three-dimensional-tetrahedron": (request(program(tetrahedron)),True),
        "conjunctive-equality-guard-and-empty-sequence": (request(program(conjunctive,(1,2))),True),
        "loop-fusion-with-real-read-after-write": (request(program(fission),program(fusion)),True),
        "loop-fission-with-real-read-after-write": (request(program(fusion),program(fission)),True),
        "duplicate-updates-fission": (request(program(duplicates),program(duplicate_fission)),True),
        "cross-iteration-dependent-fission": (request(program(bad_fused),program(bad_fission)),False),
        "changed-domain": (request(program(pure),program(changed_domain)),False),
        "non-affine-division-bound": (request(program(divided)),False),
        "non-affine-min-bound": (request(program(min_bound)),False),
        "unsupported-disjunctive-domain": (request(program(disjunction)),False),
    }


def machine(value): return (value+2**31) % 2**32-2**31


def simulate(program, parameters, seed):
    memory = {(3,index):machine(index*17+seed) for index in range(1000)}
    operations = 0
    def expression(value, environment):
        if isinstance(value,int): return value
        op,*args = value
        if op == "var": return environment[args[0]] if args[0]<len(environment) else 0
        if op == "sum": return expression(args[0],environment)+expression(args[1],environment)
        if op == "scale": return args[0]*expression(args[1],environment)
        if op == "div": return expression(args[0],environment)//args[1]
        if op == "mod": return expression(args[0],environment)%args[1]
        if op == "min": return min(expression(x,environment) for x in args)
        if op == "max": return max(expression(x,environment) for x in args)
        raise AssertionError(op)
    def test(value,environment):
        op,*args = value
        if op == "le": return expression(args[0],environment)<=expression(args[1],environment)
        if op == "eq": return expression(args[0],environment)==expression(args[1],environment)
        if op == "and": return test(args[0],environment) and test(args[1],environment)
        if op == "or": return test(args[0],environment) or test(args[1],environment)
        if op == "not": return not test(args[0],environment)
        raise AssertionError(op)
    def cell(access,arguments):
        assert len(access)==2
        row=access[1]
        return access[0],sum(a*b for a,b in zip(row[:-1],arguments))+row[-1]
    def value(code,arguments,loaded):
        if isinstance(code,int): return machine(code)
        op,*args=code
        if op == "parameter": return machine(arguments[args[0]])
        if op == "loaded": return loaded[args[0]]
        a,b=value(args[0],arguments,loaded),value(args[1],arguments,loaded)
        return machine({"add":lambda:a+b,"sub":lambda:a-b,"mul":lambda:a*b}[op]())
    def execute(statement,environment):
        nonlocal operations
        kind=statement["kind"]
        if kind == "loop":
            for index in range(expression(statement["lower"],environment),expression(statement["upper"],environment)):
                execute(statement["body"],[index,*environment])
        elif kind == "seq":
            for member in statement["statements"]: execute(member,environment)
        elif kind == "guard":
            if test(statement["test"],environment): execute(statement["body"],environment)
        elif kind == "instr":
            arguments=[expression(x,environment) for x in statement["arguments"]]
            loaded=[memory[cell(access,arguments)] for access in statement.get("reads",[])]
            memory[cell(statement["write"],arguments)]=value(statement["value"],arguments,loaded)
            operations+=1
        else: raise AssertionError(kind)
    execute(program["body"],list(reversed(parameters)))
    return memory,operations


def main():
    stamp=json.loads((EXECUTABLE.parent/"build.json").read_text())
    assert stamp["executable_sha256"]==hashlib.sha256(EXECUTABLE.read_bytes()).hexdigest()
    for path,expected in (stamp["proof_sources"]|stamp["native_sources"]).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==expected, path
    WORK.mkdir(parents=True,exist_ok=True)
    results,comparisons,counterexamples={},0,{}
    for name,(proposal,expected) in fixtures().items():
        (WORK/(name+".json")).write_text(json.dumps(proposal,indent=2)+"\n")
        result=validate(proposal)
        if result["accepted"] != expected or not result["alarm_free"]: raise AssertionError((name,result))
        results[name]=result
        if expected or name in ["cross-iteration-dependent-fission","changed-domain"]:
            for n in range(-2,6):
                for m in range(-1,5):
                    parameters=[n,m][:len(proposal["source"]["context"])]
                    for seed in [-900,2**31-2]:
                        before=simulate(proposal["source"],parameters,seed)
                        after=simulate(proposal["candidate"],parameters,seed)
                        if expected and before != after: raise AssertionError((name,parameters,seed))
                        if not expected and before != after: counterexamples.setdefault(name,{"parameters":parameters,"seed":seed})
                        comparisons+=1
    assert len(counterexamples)==2
    for name,environment in [("invalid-certificate",dict(os.environ,GUARDCERT_ORACLE_FAULT="top-certificate")),
                             ("resource-limit",dict(os.environ,GUARDCERT_FM_ROWS="0"))]:
        result=validate(fixtures()["loop-fusion-with-real-read-after-write"][0],environment=environment)
        assert not result["accepted"]
        results[name]=result
    report={"status":"passed","cases":results,"independent_machine_integer_executions_compared":comparisons,
            "semantic_counterexamples":counterexamples,"executable_sha256":stamp["executable_sha256"],
            "actual_general_loop_extractor_and_validator_consumed":True,
            "runtime_parameters_enumerated_by_checker":False,"complete_c_source_decoder_tested":False}
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(f"General Loop IR checker passed: {len(results)} proposals, {comparisons} independent executions, "
          "affine 3D domains, fusion/fission, real reads and rejection witnesses")


if __name__ == "__main__": main()
