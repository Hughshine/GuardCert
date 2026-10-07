# Source-Licensed Loaded-Column Scans

This stage closes the loaded child loop around the existing literal-component
scan. The address grammar retains signed32 variable products, so it can express
the runtime Horner index used by the target tensor family. It proves actual
Clight scan execution and accepted original-to-cached column transport.
It also connects a checked current row to the next original outer prefix.
The complete outer scan and loaded tensor compiler remain unfinished.

## Execution Dependency

`ClightTensorWordColumn.v` implements one private column cursor around the
existing private component cursor. The generated code initializes the column
limit from the captured child word, resets its cursor to zero, and runs a
short-circuit loop. Its incoming success flag is already initialized.

`tensor_word_column_component_prefix_open` opens the current original component
execution from a reached original child-loop prefix. The virtual source
coordinates and the private guard coordinates share the captured memory anchor;
the reached original execution may run in memory modified by earlier stores.
The existing permission-transport service licenses the point comparison at the
guard entry from that actual source store.

`tensor_word_column_component_execution` runs the whole component scan for
the current column. Accepting its checks supplies preservation of every
captured raw observation through that original component body.
`tensor_word_column_next_prefix` advances the original child prefix only with
that acceptance evidence. A failed check does not advance or require a future
source-domain premise. `tensor_word_column_first_refusal` proves that a first
column refusal leaves the private column cursor at zero.

`tensor_word_column_scan_execution` closes the full private column/component
scan. Its memory is unchanged, protected temporaries agree, and its Boolean
matches all checked columns. Complete acceptance supplies each column body's
observation-preservation law. `tensor_word_column_accepted_source_transport`
uses those laws to derive an actual cached child-loop execution with exactly
the original trace, exit temporaries, memory and outcome.

`tensor_word_column_current_row_execution` opens the child prefix from the
original outer prefix and uses complete current-row acceptance to produce the
next original outer prefix. This is the induction step needed by a future
outer scan, not a theorem that all rows have already been checked.

The standalone zero-column theorem requires no source prefix, observer receipts
or executable component. It evaluates only the defined cached zero count and
private loop controls. The component and success flag are never read. This
keeps empty paths separate from active-point permission and word-definedness
obligations.

## Actual Memory Fixtures

The fixtures use the existing real CompCert allocation, with header words at
bytes 0 and 4. The source child bound is `grid[1]+2`, and each column executes
five stores with index `2*MAX+7+k`. Exact signed32 evaluation gives `5+k`.
This fixture does not use the column in its address; the general service admits
indices using both column and component coordinates.

With pointer offset 16, the ten source points write bytes 36 through 52.
The complete private scan accepts. `twc_actual_cached_source` proves that the
original loaded child loop and the cached loop execute to the same temporaries
and memory, including the source component counter, and preserve both headers.

With pointer offset -20, the first component overlaps header storage. The
actual scan refuses. The original-source completion proof permits raw child
words zero or seven, hence bounds two or nine; it does not assume that the
captured bound remains stable on this source path. The full-word store library
proves the observation alternatives and permission preservation used to
construct that original execution.

`twc_empty_skips_undefined_check` supplies only a zero cached count. The component
would load through an undefined temporary, and the incoming Boolean is also
undefined. Actual Clight execution completes without evaluating either, leaves
both temporaries undefined and preserves memory.

These are Rocq proofs of actual Clight executions. The wrapping address example
tests safe check licensing; it does not claim acceptance by later mathematical
no-wrap/model conditions. There is no new native C or assembly run in this stage.

## Responsibilities and Evidence

The minimal kernel is unchanged. The Clight library supplies word execution,
permission transport, private frames, short-circuit scan execution and cached
loop transport. The domain instance supplies the loaded-bound shape, header
laws, captured observations and coordinate wiring. These are internal library
proof inputs. The new family's data-only factory must still derive its static
syntax, scope, typing and freshness evidence and instantiate the header laws
from concrete capture receipts; they are not new end-user semantic callbacks.

The independent audit is `scripts/audit_tensor_word_column.py`. It binds the
unchanged component-stage parent, sources, compiled objects, helper files and
toolchain. It queries 37 endpoints over 452 dependencies; 13 endpoints are closed
and the others use at most six existing CompCert baseline globals. No new global
axiom is added. Its required closure excludes the preserved untracked local
column drafts. The report is `build/tensor-word-column/proof/report.json`, SHA256
`bb766431372686764d500c57b0cd0b6982e050cbdca1435ddf63b967281dd328`.

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_tensor_word_column.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_tensor_word_column.py --validate
```

Next, execute the complete outer scan using this current-row step, derive full
nested cached-source execution and canonical tensor correspondence, then connect
the complete numeric/layout guard, actual generated candidate, data-only
factory and selected Clight host. The acceptance gate remains the same
loaded/dynamic C input through the real polyhedral pipeline and Csem-to-Asm
proof, including refusal and public continuation effects. This column stage
adds no whole-program endpoint, profitability result or author-effort measurement.
