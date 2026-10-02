#!/usr/bin/env python3
"""Independent presumption/condition model, not extracted Rocq code."""

from dataclasses import dataclass, replace
from itertools import product
import json
from pathlib import Path

from demo import State, Transfer, Exit, Rewrite, apply_plan, run, write


@dataclass(frozen=True)
class Node:
    op: str
    args: tuple = ()


def node(op: str, *args) -> Node:
    return Node(op, args)


def mathematical_value(s: State, e: Node) -> int:
    if e.op == "literal":
        return e.args[0]
    if e.op == "scalar":
        return s.x
    left, right = (mathematical_value(s, child) for child in e.args)
    return left + right if e.op == "sum" else left - right


def in_word(value: int, modulus: int) -> bool:
    return 0 <= value < modulus


def mathematical_safe(s: State, e: Node, modulus: int) -> bool:
    own_range = in_word(mathematical_value(s, e), modulus)
    if e.op in ("literal", "scalar"):
        return own_range
    return own_range and all(mathematical_safe(s, child, modulus) for child in e.args)


def evaluate(s: State, e: Node, modulus: int) -> tuple[int, bool]:
    if e.op in ("literal", "scalar"):
        value = e.args[0] if e.op == "literal" else s.x
        return value % modulus, in_word(value, modulus)
    (left, left_ok), (right, right_ok) = (evaluate(s, c, modulus) for c in e.args)
    exact = left + right if e.op == "sum" else left - right
    return exact % modulus, left_ok and right_ok and in_word(exact, modulus)


def offset(s: State, pointer: int) -> int:
    return s.p if pointer == 0 else s.q


def bounds_meaning(s: State, pointer: int, length: int) -> bool:
    start = offset(s, pointer)
    return start >= 0 and length >= 0 and start + length <= len(s.heap)


def disjoint_meaning(s: State, p: int, left: int, q: int, right: int) -> bool:
    # The executable examples use two pointers into the same toy block.
    return (left >= 0 and right >= 0 and
            (left == 0 or right == 0 or offset(s, p) + left <= offset(s, q)
             or offset(s, q) + right <= offset(s, p)))


def meaning(s: State, p: Node, modulus: int = 256) -> bool:
    op, args = p.op, p.args
    if op == "truth":
        return True
    if op == "falsity":
        return False
    if op == "both":
        return meaning(s, args[0], modulus) and meaning(s, args[1], modulus)
    if op == "either":
        return meaning(s, args[0], modulus) or meaning(s, args[1], modulus)
    if op == "negation":
        return not meaning(s, args[0], modulus)
    if op in ("le", "equal"):
        left, right = (mathematical_value(s, e) for e in args)
        return left <= right if op == "le" else left == right
    if op == "no_overflow":
        return mathematical_safe(s, args[0], modulus)
    if op == "in_bounds":
        return bounds_meaning(s, args[0], mathematical_value(s, args[1]))
    if op == "disjoint":
        p, left, q, right = args
        return disjoint_meaning(s, p, mathematical_value(s, left), q,
                                mathematical_value(s, right))
    raise ValueError(op)


def synthesize(p: Node) -> Node:
    if p.op in ("truth", "falsity"):
        return node("boolean", p.op == "truth")
    if p.op == "both":
        return node("if", synthesize(p.args[0]), synthesize(p.args[1]),
                    node("boolean", False))
    if p.op == "either":
        return node("if", synthesize(p.args[0]), node("boolean", True),
                    synthesize(p.args[1]))
    if p.op == "negation":
        return node("not", synthesize(p.args[0]))
    return node("check_atom", p)


def endpoint_ok(s: State, p: int, length: int, modulus: int) -> bool:
    return in_word(offset(s, p), modulus) and in_word(offset(s, p) + length, modulus)


def execute_atom(s: State, a: Node, modulus: int) -> bool | None:
    op, args = a.op, a.args
    if op == "no_overflow":
        return evaluate(s, args[0], modulus)[1]
    if op in ("le", "equal"):
        (left, ok_l), (right, ok_r) = (evaluate(s, e, modulus) for e in args)
        if not (ok_l and ok_r):
            return None
        return left <= right if op == "le" else left == right
    if op == "in_bounds":
        p, expr = args
        length, ok = evaluate(s, expr, modulus)
        if not (ok and endpoint_ok(s, p, length, modulus)):
            return None
        return bounds_meaning(s, p, length)
    if op == "disjoint":
        p, le, q, re = args
        left, ok_l = evaluate(s, le, modulus)
        right, ok_r = evaluate(s, re, modulus)
        if not (ok_l and ok_r and endpoint_ok(s, p, left, modulus)
                and endpoint_ok(s, q, right, modulus)):
            return None
        return disjoint_meaning(s, p, left, q, right)
    raise ValueError(op)


def execute(s: State, c: Node, modulus: int = 256) -> bool | None:
    if c.op == "boolean":
        return c.args[0]
    if c.op == "check_atom":
        return execute_atom(s, c.args[0], modulus)
    if c.op == "not":
        result = execute(s, c.args[0], modulus)
        return None if result is None else not result
    if c.op == "if":
        test, yes, no = c.args
        result = execute(s, test, modulus)
        return None if result is None else execute(s, yes if result else no, modulus)
    raise ValueError(c.op)


X, ONE = node("scalar", 0), node("literal", 1)
INCREMENT = node("sum", X, ONE)
NO_WRAP = node("no_overflow", INCREMENT)
IMPOSSIBLE = node("both", node("le", X, node("literal", 5)),
                  node("le", node("literal", 10), X))
MEMORY = node("both", node("in_bounds", 0, ONE),
              node("both", node("in_bounds", 1, ONE), node("disjoint", 0, ONE, 1, ONE)))


def synthesized_rewrite(p: Node, original, optimized) -> Rewrite:
    condition = synthesize(p)
    return Rewrite(original, optimized, lambda s: execute(s, condition) is True)


def rewrites() -> dict[int, Rewrite]:
    def conditional_source(s: State) -> Transfer:
        if (s.x + 1) % 256 < s.x:
            return Transfer((900,), Exit("trap"), replace(s, result=1))
        return Transfer((), Exit("jump", 2), replace(s, result=0))

    conditional_candidate = lambda s: Transfer((), Exit("jump", 2), replace(s, result=0))
    alias_source = lambda s: Transfer((), Exit("jump", 3), replace(
        s, heap=write(write(s.heap, s.p, 1), s.q, 2)))
    alias_candidate = lambda s: Transfer((), Exit("jump", 3), replace(
        s, heap=write(write(s.heap, s.q, 2), s.p, 1)))

    def always_dead_source(s: State) -> Transfer:
        if s.x < s.x:
            return Transfer((901,), Exit("trap"), s)
        return Transfer((), Exit("jump", 4), replace(s, result=7))

    always_dead_candidate = lambda s: Transfer((), Exit("jump", 4), replace(s, result=7))
    return {1: synthesized_rewrite(NO_WRAP, conditional_source, conditional_candidate),
            2: synthesized_rewrite(MEMORY, alias_source, alias_candidate),
            3: synthesized_rewrite(node("truth"), always_dead_source, always_dead_candidate)}


def to_json(value):
    if isinstance(value, Node):
        return {"op": value.op, "args": [to_json(arg) for arg in value.args]}
    return value


def main() -> None:
    overflow_cmp = node("le", INCREMENT, node("literal", 255))
    atoms = [node("truth"), node("falsity"), node("le", X, node("literal", 5)),
             node("equal", X, X), NO_WRAP, overflow_cmp,
             node("no_overflow", node("difference", X, ONE)), MEMORY, IMPOSSIBLE]
    presumptions = atoms + [node("negation", a) for a in atoms]
    presumptions += [node(op, a, b) for op, a, b in product(("both", "either"), atoms, atoms)]
    conditions = [(p, synthesize(p)) for p in presumptions]
    synthesis_checks = 0
    for x, p, q in product(range(256), range(3), range(3)):
        s = State(x, 99, p, q, (0, 0))
        for presumption, condition in conditions:
            result = execute(s, condition)
            if result is not None:
                assert result == meaning(s, presumption), (s, presumption, result)
            synthesis_checks += 1
        for expr in (X, INCREMENT, node("difference", X, ONE),
                     node("difference", INCREMENT, INCREMENT)):
            value, ok = evaluate(s, expr, 256)
            assert ok == mathematical_safe(s, expr, 256)
            if ok:
                assert value == mathematical_value(s, expr)
        assert execute(s, synthesize(IMPOSSIBLE)) is not True

    bad = State(255, 99, 0, 1, (0, 0))
    assert evaluate(bad, INCREMENT, 256) == (0, False)
    assert execute(bad, synthesize(node("negation", overflow_cmp))) is None
    assert execute(bad, synthesize(node("negation", NO_WRAP))) is True
    assert execute(bad, synthesize(node("either", node("truth"), overflow_cmp))) is True
    # Converting failure to false under not would accept an incorrect condition.
    failing_true = node("equal", INCREMENT, INCREMENT)
    broken_not = not bool(execute(bad, synthesize(failing_true)))
    assert broken_not and not meaning(bad, node("negation", failing_true))

    plan = rewrites()
    program = {0: lambda s: Transfer((100,), Exit("jump", 1), s),
               **{pc: rewrite.original for pc, rewrite in plan.items()},
               4: lambda s: Transfer((s.result,), Exit("return"), s)}
    transformed = apply_plan(program, plan)
    program_checks = 0
    for x, p, q in product(range(256), range(5), range(5)):
        s = State(x, 99, p, q, (0, 0, 0, 0))
        assert run(program, s, 8) == run(transformed, s, 8), s
        program_checks += 1
    for x in (-1, 256, 511):
        s = State(x, 99, 0, 1, (0, 0))
        assert run(program, s, 8) == run(transformed, s, 8)

    output = Path(__file__).resolve().parents[1] / "build" / "synthesized-conditions.json"
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps({name: {"presumption": to_json(p),
                                        "condition": to_json(synthesize(p))}
                                  for name, p in (("no_wrap", NO_WRAP),
                                                  ("memory", MEMORY),
                                                  ("impossible", IMPOSSIBLE),
                                                  ("always_dead", node("truth")))}, indent=2) + "\n")
    print(f"Presumption synthesis: {synthesis_checks} comparisons across {len(conditions)} formulas passed")
    print(f"Synthesized whole-program rewrites: {program_checks} comparisons passed")
    print("Failure beneath negation remains failure; explicit NoOverflow can be negated.")
    for label, s in (("safe", State(254, 99, 0, 1, (0, 0))),
                     ("wrapping", bad), ("aliasing", State(12, 99, 0, 0, (0, 0)))):
        out = run(transformed, s, 8)
        print(f"  {label}: trace={out.events}, status={out.status}, heap={out.state.heap}")
    print(f"Generated condition ASTs: {output}")


if __name__ == "__main__":
    main()
