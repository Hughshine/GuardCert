# Verified finite schedule checking

`AbstractScheduleChecker.check_schedule` is an executable checker for proposed
finite instruction orders. It takes instruction equality and a Boolean
independence test. The language instance proves that an accepting independence
test supplies the commutation property of its `scheduling_model`. The kernel
does not interpret memory, arithmetic, or read/write sets.

For each next target instruction, the checker finds that occurrence in the
remaining source sequence. It moves the instruction to the front only when
each crossed instruction has a certified commutation. It then removes that
occurrence and continues. An absent instruction, an uncertified crossing, or
unconsumed source instructions causes refusal. Equal instructions may occur
more than once; removal preserves their multiplicity.

`check_schedule_sound` turns acceptance into an `AbstractSchedule` certificate.
`check_schedule_preserves` constructs a target execution from a source
execution on the model invariant and relates their final states through the
instance's equivalence. Both theorems are closed under the global context.
Identity schedules always pass. There is no claim of completeness for every
semantically equivalent order or every possible independence analysis.

`CompCertIndexSchedule` supplies a concrete property library. A natural index
names a signed32 store at byte offset `4 * index` in a fixed array block; its
payload can be any immutable entry-dependent integer value. Distinct indices
give disjoint byte ranges, so actual `Mem.store` operations commute and produce
equal complete memories. The executable checker needs only the indices; it
does not read CompCert block identifiers or permissions at runtime. Source
execution supplies the permissions used to construct the reordered stores.

The native matrix recognizer executes this checker on `[0,1,2,3]` and the
proposed column order `[0,2,1,3]`. Its region rule consumes the success
certificate through
`checked_matrix_interchange_preserves_actual_memory`, replacing the previous
hand-built swap certificate in the compiler's proof chain. Full source AST
binding and the runtime guard remain separate obligations.

```sh
make proof demo
```

`scripts/schedule_checker_demo.py` extracts the actual Rocq checker into OCaml
and runs all 120 permutations of five independent instruction identifiers. It
also checks refusal when no commutations are provided, missing/extra/duplicated
actions, repeated instructions, and the empty identity. Its report is
`build/schedule-checker-demo/report.json`. These executions supplement the
universal proof; they do not establish commutation for a new language instance.

This is a finite instruction-order checker. The direct memory instance is not
an arbitrary-index Clight code generator: the matrix bridge separately proves
its small indices and pointer calculations valid. General affine domains,
correspondence between dynamically sized loop iterations, tiling, and
dependence analysis still require additional certificates. A future optimizer
can propose orders without becoming trusted, but the current native proposer
still selects one fixed matrix template and one candidate loop layout.
