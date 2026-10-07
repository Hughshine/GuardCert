# Complete Source-Licensed Word Scans

This stage closes the private row/column/component stability scan for a loaded
root and child bound with a literal component loop. Complete acceptance derives
actual nested cached-source execution. A second transport theorem starts that
cached execution at the actual scan exit, with the original final memory and
agreement on protected temporaries. The loaded tensor compiler is still pending.

## Source and Check Execution

`ClightTensorWordOuter.v` uses the audited current-row service as its induction
step. It copies the root cache into a private limit, initializes a private
success flag and row cursor, and runs a short-circuit loop of full column and
component scans. The check leaves memory unchanged and protects its declared
live temporaries.

`tensor_word_outer_row_execution` opens the original child prefix for the
current row. Complete row acceptance proves preservation of both captured raw
header observations and produces the next original outer prefix. The proof
therefore obtains future address permissions only after earlier checks accept;
it never assumes that the full cached source is already executable.

`tensor_word_outer_scan_execution` constructs the complete actual Clight scan
and relates its Boolean to the nested point checks. On acceptance,
`tensor_word_outer_cached_source` derives actual cached nested execution with
the original trace, exit temporaries, memory and outcome.
`tensor_word_outer_original_scan_at_exit` additionally protects the cached
source's syntax footprint and transports this execution to the actual checked
temporary environment. Private scan controls may differ; the final memory is
the original source's final memory, and the declared live exit temporaries agree.

These are finite silent normal-execution services. The installation host must
still supply its original-source progress and placement evidence. A completed
source execution does not by itself establish whole-program simulation.

## Static Syntax and Actual Header Receipts

`ClightTensorWordOuterHeaders.v` instantiates the generic header laws from an
actual `ncs_observation_receipt`. The receipt already records successful reads,
captured cache words, address expressions and initial observations. Existing
capture services can produce it on the active-child capture path.

`tensor_word_header_scan_at_exit` derives root and child evaluation, cache
definedness and observer scope from this receipt. Its caller does not supply
semantic callbacks asserting that the loaded bounds evaluate correctly when
their observations are preserved. Source shape, word grammar, protected scope,
renaming and resource freshness remain internal adapter inputs; the new family's
data-only factory must still produce them.

The generated scan uses `ncs_observer_templates`, whose address expressions are
fixed by the source shape. Ghost physical locations and captured values are
not embedded in runtime syntax. `tensor_word_outer_same_addresses` and
`tensor_word_header_scan_receipt` prove that receipt observers and these static
templates generate the same check code. The Boolean specification uses the
actual receipt locations, not the dummy physical fields of the templates.

## Empty and Refused Paths

`tensor_word_outer_empty_execution` requires only a defined zero root cache,
private controls and their freshness. It executes no row code and requires no
observer, data pointer, child cache, source-prefix or word-expression premise.
It initializes the private Boolean to true and preserves memory/public state.

`tensor_word_outer_first_refusal` consumes only the first row's actual execution
and control frame. It proves that the outer cursor remains zero and no later row
executes. It has no later-row safety or execution premise.

The header-receipt adapter is for paths on which both headers were captured.
The unconditional empty-scan service is separate; this stage does not yet
assemble conditional capture, profile gates and scanning into a complete
loaded-family guard driver.

## Actual Memory Fixtures

`ClightTensorWordOuterExample.v` uses a real CompCert allocation with raw header
words zero at bytes 0 and 4. The original two loaded bounds add two, so the
captured counts are two. Each of the four row/column pairs executes five stores
of word seven. Their index `2*MAX+7+k` wraps to `5+k` in exact signed32 semantics.
This fixture deliberately ignores row and column in its address. The general
service admits both coordinates and variable products, but this fixture is not
the full dynamic Horner RMW input or an OLO benchmark result.

With pointer offset 16, all twenty point checks accept. The original source and
the cached source from the actual scan exit reach the same final memory and
related protected temporaries. With offset -20, the scan refuses a header alias.
The original completion proof allows both raw headers to become seven, so their
loaded bounds may change from two to nine. It does not assume their stability.

The fixtures construct actual receipts and use the receipt-derived scan adapter.
Separate executions show that a zero root skips an undefined child load, and
that refusal at row zero skips a later-row branch that would read an undefined
pointer. Neither test assumes that unavailable future accesses are safe.

## Evidence and Remaining Integration

The independent audit is `scripts/audit_tensor_word_outer.py`. It validates the
frozen column parent before and after auditing, binds sources, compiled objects,
helpers and toolchain, and excludes the preserved local draft modules from its
required closure. It queries 41 endpoints over 456 dependencies; 13 endpoints
are closed, and the others use at most six existing CompCert baseline globals.
No global axiom is added; the minimal kernel is unchanged.

The report is `build/tensor-word-outer/proof/report.json`, SHA256
`fbd5a4803b483a8ad1382d70a60774ff98bcf6d630e428601caa61032fe03177`.

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_tensor_word_outer.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_tensor_word_outer.py --validate
```

The next integration composes conditional capture and numeric/profile gating
with this scan, derives canonical tensor execution and complete-guard parameter
bindings, and feeds the actual generated candidate checker. Its family factory
must then produce local guarded and site evidence for selected installation and
Csem-to-Asm. The same loaded/dynamic C input must cover acceptance, alias/profile
refusal, conditional empty paths, selection, repeated sites and public exits.
This stage adds no compiler entry, C/assembly calls, runtime cost or profitability
measurement. The full goal remains active.
