# Abstract guarded choice: syntax-independent host control

Date: 2026-10-05.

A generic GuardCert theorem should not be phrased around a concrete source-language
`if`.  The framework should depend on an abstract **guarded-choice host
structure** whose semantics is the pure conditional behavior needed by the proof.
A language/IR instance is responsible for constructing some concrete code with
that behavior and proving the required laws.

## 1. Core idea

At the framework level we want an operator of the form

```
choose : check -> code -> code -> code
```

with an abstract semantic law:

```
run check from an admissible entry
   = Accept, related state  -> choose behaves as the yes branch
   = Reject, related state  -> choose behaves as the no branch
```

and the dispatch itself contributes no additional public effect beyond the check
and the selected branch.

This is deliberately a *semantic* interface, not a syntax requirement.

A concrete host may realize `choose` with:

- an ordinary `if`;
- conditional branches in a CFG;
- `goto` plus labels;
- a small `while`/state machine;
- a private Boolean/result slot followed by shared exits;
- another control encoding that proves the same law.

The generic GuardCert proof should be insensitive to which representation is
used.

## 2. Separate check semantics from dispatch semantics

Two abstractions should remain distinct.

### Check execution

A check may use private temporaries, safe reads, checked arithmetic, short
circuiting, and conservative failure.  Its contract is something like:

```
run_check : entry_state -> decision * check_state
```

together with:

- finite/safe execution on the stated domain;
- a public-state relation/projection between entry and check state;
- `Accept -> semantic precondition`;
- rejection/failure preserves an admissible source fallback state.

### Guarded choice

The host then proves that its concrete control structure dispatches according to
that decision and otherwise contributes no public behavior:

```
choose_spec:
  check accepts  -> choose check yes no  ~=  check ; yes
  check rejects  -> choose check yes no  ~=  check ; no
```

The exact statement should use the host's trace/state/control relation rather
than literal sequential syntax.

This split is useful because a condition compiler and a branch lowering solve
different problems.

## 3. "No-side-effect if" means observational purity, not literal state equality

A host implementation may write compiler-private locals or CFG bookkeeping
state.  Therefore the law should not require literal equality of all machine
state.

Instead the host supplies a public observation/state relation `Rpub`, e.g.

```
Rpub entry after_dispatch
```

which hides fresh temporaries and other private representation details.

Thus a shared-exit lowering that stores the check result in a fresh local can
still implement the abstract pure conditional.

## 4. Why this belongs in the language adapter

The framework should not prove that C `if`, Clight `Sifthenelse`, RTL
branches, or assembly jumps have the desired semantics separately for every
transformation.

Instead each language/IR instance provides once:

1. the concrete code type and execution semantics;
2. the check execution interface;
3. the guarded-choice constructor/lowering;
4. a proof that the constructor has the abstract conditional semantics;
5. freshness/frame/control obligations needed to hide private implementation
   state.

Then transformation-specific proofs can work solely against the abstract
`choose` law.

## 5. Consequence for GuardCert architecture

A cleaner layering is:

```
conditional transformation theorem
        |
        | requires only abstract check + choose laws
        v
generic GuardCert kernel
        |
        | instantiated by
        v
Host instance
  - observable state relation
  - check primitives/lowering
  - guarded choice lowering
  - control/entry/exit proof
        |
        v
Clight / RTL / LLVM / assembly / ...
```

This keeps "the framework is general" meaningful: the generic theorem is not
secretly tied to one syntax tree constructor.

## 6. First Clight instance

For Clight, `Sifthenelse` is the most direct realization, but it should be
treated as merely one implementation of the abstract choice law.

If code-size or control-flow engineering later prefers:

- a private Boolean;
- branches to shared candidate/fallback blocks;
- labels and `goto`;

the framework theorem should remain unchanged.  Only the Clight host proof is
reused or extended.

This is also the right abstraction boundary for comparing higher- and
lower-level hosts: they may implement the same semantic guarded-choice
interface using very different concrete control structures.
