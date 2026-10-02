#!/usr/bin/env python3
"""Independent executable regression model; this is not Coq extraction."""

from dataclasses import dataclass, replace
from itertools import product
from typing import Callable


@dataclass(frozen=True)
class State:
    x: int
    result: int
    p: int
    q: int
    heap: tuple[int, ...]


@dataclass(frozen=True)
class Exit:
    kind: str
    value: int = 0


@dataclass(frozen=True)
class Transfer:
    events: tuple[int, ...]
    exit: Exit
    state: State


Region = Callable[[State], Transfer]
Program = dict[int, Region]


@dataclass(frozen=True)
class Rewrite:
    original: Region
    optimized: Region
    check: Callable[[State], bool]

    def versioned(self, state: State) -> Transfer:
        return (self.optimized if self.check(state) else self.original)(state)


@dataclass(frozen=True)
class Outcome:
    # Fuel exhaustion is a finite prefix, never evidence of divergence.
    status: str
    value: int
    state: State
    events: tuple[int, ...]


def checked_add(a: int, b: int) -> int | None:
    if 0 <= a < 256 and 0 <= b < 256 and a <= 255 - b:
        return (a + b) % 256
    return None


def overflow_check(state: State) -> bool:
    total = checked_add(state.x, 1)
    return total is not None and total <= 255


def write(heap: tuple[int, ...], address: int, value: int) -> tuple[int, ...]:
    # Same list model as Examples.v: an out-of-bounds write leaves it intact.
    if 0 <= address < len(heap):
        return heap[:address] + (value,) + heap[address + 1:]
    return heap


def alias_check(state: State) -> bool:
    return (0 <= state.p < len(state.heap)
            and 0 <= state.q < len(state.heap) and state.p != state.q)


def overflow_rewrite(next_pc: int) -> Rewrite:
    def original(s: State) -> Transfer:
        result = int((s.x + 1) % 256 < s.x)
        return Transfer((), Exit("jump", next_pc), replace(s, result=result))

    def optimized(s: State) -> Transfer:
        return Transfer((), Exit("jump", next_pc), replace(s, result=0))

    return Rewrite(original, optimized, overflow_check)


def alias_rewrite(next_pc: int) -> Rewrite:
    def original(s: State) -> Transfer:
        heap = write(write(s.heap, s.p, 1), s.q, 2)
        return Transfer((), Exit("jump", next_pc), replace(s, heap=heap))

    def optimized(s: State) -> Transfer:
        heap = write(write(s.heap, s.q, 2), s.p, 1)
        return Transfer((), Exit("jump", next_pc), replace(s, heap=heap))

    return Rewrite(original, optimized, alias_check)


def apply_plan(program: Program, plan: dict[int, Rewrite]) -> Program:
    result = dict(program)
    for pc, rewrite in plan.items():
        # This executable restriction binds the exact callable at the slot.
        # It is not an extracted implementation of the Coq plan_matches proof.
        if program.get(pc) is not rewrite.original:
            raise ValueError(f"rewrite does not match original slot {pc}")
        result[pc] = rewrite.versioned
    return result


def run(program: Program, state: State, fuel: int, pc: int = 0) -> Outcome:
    events: tuple[int, ...] = ()
    for _ in range(fuel):
        region = program.get(pc)
        if region is None:
            return Outcome("fault", 0, state, events)
        transfer = region(state)
        events += transfer.events
        state = transfer.state
        if transfer.exit.kind == "return":
            return Outcome("halted", transfer.exit.value, state, events)
        if transfer.exit.kind == "trap":
            return Outcome("fault", 0, state, events)
        pc = transfer.exit.value
    return Outcome("prefix", pc, state, events)


def context(kind: str) -> tuple[Program, dict[int, Rewrite]]:
    arithmetic, alias = overflow_rewrite(2), alias_rewrite(3)
    program = {
        0: lambda s: Transfer((100,), Exit("jump", 1), s),
        1: arithmetic.original,
        2: alias.original,
    }
    if kind == "linear":
        program[3] = lambda s: Transfer((s.result,), Exit("return"), s)
    elif kind == "branch":
        program[3] = lambda s: Transfer((), Exit("jump", 5 if s.result else 4), s)
        program[4] = lambda s: Transfer((111, sum(s.heap)), Exit("return", 4), s)
        program[5] = lambda s: Transfer((222, sum(s.heap)), Exit("return", 5), s)
    elif kind == "loop":
        def back_edge(s: State) -> Transfer:
            out = Exit("return") if s.x == 255 else Exit("jump", 1)
            next_state = s if s.x == 255 else replace(s, x=s.x + 1)
            return Transfer((s.result, sum(s.heap)), out, next_state)
        program[3] = back_edge
    elif kind == "missing_exit":
        program[3] = lambda s: Transfer((s.result,), Exit("jump", 99), s)
    elif kind == "silent_loop":
        program[3] = lambda s: Transfer((), Exit("jump", 1), s)
    else:
        raise ValueError(kind)
    return program, {1: arithmetic, 2: alias}


def checks() -> dict[str, int]:
    counts = {"checked_add_pairs": 0, "local_replacements": 0,
              "whole_program_comparisons": 0, "rejected_mutations": 0}
    for a, b in product(range(256), repeat=2):
        actual = checked_add(a, b)
        expected = a + b if a + b < 256 else None
        assert actual == expected, (a, b, actual)
        counts["checked_add_pairs"] += 1
    for a, b in product((-1, 0, 1, 255, 256), repeat=2):
        if not (0 <= a < 256 and 0 <= b < 256):
            assert checked_add(a, b) is None

    heaps = ((0, 0, 0, 0), (7, 8, 9, 10), (-3, 2, 1, 99))
    arithmetic, alias = overflow_rewrite(2), alias_rewrite(3)
    for x, p, q, heap in product(range(256), range(5), range(5), heaps):
        state = State(x, 99, p, q, heap)
        for rewrite in (arithmetic, alias):
            assert rewrite.versioned(state) == rewrite.original(state), state
            counts["local_replacements"] += 1
    for kind in ("linear", "branch", "missing_exit"):
        program, plan = context(kind)
        transformed = apply_plan(program, plan)
        for x, p, q, heap in product(range(256), range(5), range(5), heaps):
            state = State(x, 99, p, q, heap)
            assert run(program, state, 8) == run(transformed, state, 8), (kind, state)
            counts["whole_program_comparisons"] += 1
    for kind in ("loop", "silent_loop"):
        program, plan = context(kind)
        transformed = apply_plan(program, plan)
        for x, p, q, heap in product(range(252, 256), range(5), range(5), heaps):
            state = State(x, 99, p, q, heap)
            before, after = run(program, state, 20), run(transformed, state, 20)
            assert before == after, (kind, state)
            assert before.status == ("prefix" if kind == "silent_loop" else "halted")
            counts["whole_program_comparisons"] += 1

    # Mutation checks demonstrate observable failures if an obligation is lost.
    wrapping = State(255, 99, 0, 1, (0, 0))
    naive_check = lambda s: (s.x + 1) % 256 <= 255
    assert naive_check(wrapping) and not overflow_check(wrapping)
    assert arithmetic.optimized(wrapping) != arithmetic.original(wrapping)
    counts["rejected_mutations"] += 1

    overlapping = State(12, 99, 0, 0, (0, 0))
    bounds_only = lambda s: 0 <= s.p < len(s.heap) and 0 <= s.q < len(s.heap)
    assert bounds_only(overlapping) and not alias_check(overlapping)
    assert alias.optimized(overlapping) != alias.original(overlapping)
    counts["rejected_mutations"] += 1

    program, plan = context("loop")
    initial = State(254, 99, 0, 1, (0, 0))
    cached = dict(program)
    cached[1] = plan[1].optimized if plan[1].check(initial) else plan[1].original
    assert run(cached, initial, 20) != run(program, initial, 20)
    assert run(apply_plan(program, plan), initial, 20) == run(program, initial, 20)
    counts["rejected_mutations"] += 1

    observable, local_plan = context("linear")
    observable[3] = lambda s: Transfer((s.result, s.x), Exit("return"), s)
    for mutation in ("exit", "events", "live_out"):
        def broken(s: State, mutation: str = mutation) -> Transfer:
            reference = local_plan[1].original(s)
            if mutation == "exit":
                return replace(reference, exit=Exit("return"))
            if mutation == "events":
                return replace(reference, events=(999,))
            return replace(reference, state=replace(reference.state, x=0))
        faulty = dict(observable)
        faulty[1] = broken
        before, after = run(observable, initial, 8), run(faulty, initial, 8)
        assert before != after
        assert before.events != after.events
        counts["rejected_mutations"] += 1

    stale_program = dict(program)
    stale_program[1] = lambda s: Transfer((), Exit("return"), s)
    try:
        apply_plan(stale_program, plan)
    except ValueError:
        counts["rejected_mutations"] += 1
    else:
        raise AssertionError("stale rewrite was installed")
    return counts


def main() -> None:
    counts = checks()
    print("Independent Python regression model: all checks passed")
    for name, value in counts.items():
        print(f"  {name}: {value}")
    program, plan = context("linear")
    transformed = apply_plan(program, plan)
    for label, state in (
        ("safe", State(254, 99, 0, 1, (0, 0))),
        ("overflow fallback", State(255, 99, 0, 1, (0, 0))),
        ("alias fallback", State(12, 99, 0, 0, (0, 0))),
    ):
        outcome = run(transformed, state, 8)
        print(f"  {label}: guard=({overflow_check(state)}, {alias_check(state)}), "
              f"trace={outcome.events}, heap={outcome.state.heap}, "
              f"status={outcome.status}")
    print("  Silent-loop runs above compare finite prefixes only; "
          "the Coq coinductive theorem covers infinite execution.")


if __name__ == "__main__":
    main()
