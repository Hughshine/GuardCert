# Shared fallback without scratch or labels

`ClightSharedRegion` provides a second Clight lowering for a certified
decision tree. The original lowering places the source region at every
refusal leaf. This lowering places a local `break` at each such leaf and
stores one copy of the source after a constant switch. Successful leaves run
the candidate followed by `continue`; a surrounding loop exits from its
increment part. No state slot, fresh temporary, or label is introduced.

The actual statement has this shape:

```text
loop {
  switch (0) {
    case 0:
      condition_tree(
        accept = candidate; continue,
        refuse = break
      )
  }
  source
} increment { break }
```

Refusal breaks out of the switch, runs the source, and reaches the increment
break. Acceptance continues the surrounding loop, skips the source, and
reaches the same increment break. Clight's `outcome_switch` catches `break`
but propagates `continue`, which makes these two destinations distinct.
The enclosing loop contains both control outcomes, so the complete region
returns normally on either path.

`shared_guarded_statement_execution` proves this correspondence using actual
Clight big-step constructors and the existing decision-tree execution proof.
It preserves the selected fragment's complete temporaries and memory and
adds no trace. `shared_guarded_region_contract` constructs the required
small-step execution for any surrounding function and continuation.
`shared_encoded_region_rule_sound` consumes the same `encoded_region_rule`
as the original lowering, without changing its premise or local proof.
The label-free property is also proved.

The untrusted point-order compiler now uses this lowering. Its complete
C-to-Asm theorem retains CompCert's 35 baseline assumptions. Native checking
still covers every four-point permutation and invalid proposal, and now
requires exactly one original outer-loop fallback in each accepted region.

The recorded x86-64 fixture comparison is:

| Function | Duplicated fallback | Shared fallback |
| --- | ---: | ---: |
| `matrix_dynamic` | 353 bytes | 221 bytes |
| `matrix_goto` | 284 bytes | 222 bytes |
| `matrix_global` | 258 bytes | 201 bytes |
| `matrix_context` | 309 bytes | 240 bytes |
| `matrix_unread_bound` | 341 bytes | 212 bytes |

Sizes come from `nm -S` on linked CompCert-generated assembly. The first
column was recorded at commit `6b3db97`; the comparison artifacts are in
`build/shared-fallback-comparison/`, and current per-proposal sizes are in
`build/native-scheduled-matrix/report.json`. All 24 accepted orders had the
same size for each function. These are fixture measurements, not a code-size
theorem or a runtime-speed comparison. Refused proposals use the existing
zero-trip selector and are a separate baseline, not stock CompCert.

This first sharing scheme removes repeated source code. A general tree can
still duplicate the candidate across several acceptance leaves. Other
expression and default loop-interchange paths retain their earlier lowering.
Broader control-flow sharing and cost selection remain separate work.
