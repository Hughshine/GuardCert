# 原 matmul：实际生成 Loop 在 captured 参数下的有限进展

2026-10-09 后继补上[固定参数 backward 阶段](original-matmul-prepared-parameters.md)
所留的 model forward 缺口。给定原 selected Clight source 的有限正常执行，
实际 capture 接受且最终候选检查成功，就能推出 **prepared codegen 真正返回的
Loop 在同一 captured M/N/K 下有有限执行，最终 memory 与原 source 相同**。
新检查器接受真实 Pluto i/j/k→i/k/j 输出，保留原 double instruction 与 IEEE
运算树。Candidate Clight lowering、静态前提 producer 和 selected Csem→Asm
仍未完成；没有新增已安装优化 benchmark。

## 复用已有证明，保持原语义

仓库原 signed32 memory 路径已有完整 source→point-list 证明。缺口是它不能
直接用于 `DoubleAssignmentIRs`，并非仓库中没有 forward proof。本后继将
trace、实际 extractor 的域覆盖、时间戳顺序与执行证明参数化为 `POLIRS`
functors，不改冻结的 signed32 实现、optimizer 或 kernel。

原 source trace 每一事件仍调用 `IRs.Instr.instr_semantics`。通用 forward
方向只用 `State.eq_refl` 将空 trace 接到 point-list semantics，不要求
抽象 `State.eq` 等于 Leibniz equality。固定参数 backward 服务仍返回
`State.eq` 相关的最终状态；double 实例的既有状态等价就是相等，实例化后
才得到同一最终 runtime state。

| 服务 | 调用者提供／检查器取得 | 证明结论 |
| --- | --- | --- |
| `PolCertExtractorForwardFor(IRs)` | actual extractor receipt、参数长度、source Loop 有限执行 | 同一指令、rev θ 下的 point-list execution |
| `PolCertCandidateRepresentationFor(IRs)` | point isomorphism，或 adjacent swaps；actual extracted identity representation／row widths | 相同参数下的表示转换保留指令执行与时间戳 |
| `memory_check_domain_equivalence` | 两个整数不等式域，既有 checked emptiness certificates | 两域对任意 index 的 membership 相同 |
| `validated_double_candidate_loops_at` | 两个 actual Loop、context/vars、swaps、检查接受、NonAlias | source 与 candidate 在 θ 下的有限执行 iff |
| `checked_double_prepared_loop_progress_at` | actual prepared pipeline 加最终检查的成功 receipt | source body 与实际返回 generated body 在 θ 下的有限执行 iff |

参数名类型也由语言实例提供。框架使用调用者已有 context 和显式长度，
不制造某种具体语言的虚拟参数名。通用服务仍属于优化实现的适配库；
具体 Clight、memory、safe invocation 和 host/context 责任没有移入 kernel。

## 为什么还需最终生成结果的检查

Prepared pipeline 原证明是 backward correspondence，不能直接推出候选能
执行。新函数 `checked_double_prepared_loop_progress schedule swaps source`
消费原 pipeline 返回的 body，再实际提取这个 body。最终检查使用 source
的 named context/vars 来解释该 body；这不改变 body AST，也不另写 i/k/j
程序来代替 generator 的返回值。

生成器的迭代坐标与 source 坐标可能不同，重新提取还可能加入冗余的正维
guard 约束。检查分两项处理表示，再检查依赖：

1. Untrusted producer 给出 adjacent-coordinate swaps。已证 point isomorphism
   转换 domain、schedule 和 argument transformation，保持实际指令与执行。
   参数前缀不交换，实际 extractor 的 wf 检查取得精确 row widths。
2. 双向域包含通过逐行反证检查：违反某个整数不等式与另一域的合取必须为空。
   Emptiness oracle 仍需返回原 validator 接受的证书。接受后仅替换等价 domain
   表示；它不证明调度合法，也不更换指令。
3. 实际 double dependence validator 双向验证两个已对齐模型。随后组合 source
   forward、候选表示转换、validation 和 fixed-parameter reconstruction。

本次可运行 producer 的 swaps 是见证数据：identity 为 `[]`，matmul 的
实际 i/k/j 输出为 `[1]`。错误 witness 在最终检查拒绝。通用 point-isomorphism
接口支持其他已证对应，但本次 executable 没有新增 affine shear、tiling
或 ISS witness producer。带 min/max/floordiv 的实际生成结果仍需适配，
不能因 final extractor 的 affine-bound 限制将这些顺序路线移出总目标。

## 实际 source、capture 与 candidate

`OriginalMatmulCandidateProgress.original_matmul_capture_to_candidate_progress`
消费相同 exported selected source、static/layout/bindings 和给定有限正常
source execution，复用已证 reached-header license 和实际 capture。它保留：

- Capture 的 E0／memory frame、已定义 flag、program-wide fresh caches；
- 从实际 checked entry 出发的原 source/fallback execution 与 public frame；
- 接受时私有 caches 中的精确 M/N/K，及原 i/j/k 的精确出口；
- 任何最终 pipeline receipt 接受的 generated body，都在这些实际值下完成
  Loop execution，最终 memory 是该原 source execution 的 final memory。

这关闭 conditional finite **model** progress，不是无前提 source-total
progress、divergence preservation 或 candidate Clight execution。证明中的
source execution 是 receipt，不在运行时先执行 source。C 用户仍只应提供
原 marked C 和 strategy；实际 factory 还必须自动交付静态前提与 host 义务。

## 可复现证据与下一步

机器摘要见 [original-matmul-candidate-progress.json](original-matmul-candidate-progress.json)。
七模块 1,860 行，12 个实例化审计端点，256 reachable sources／7,468 bindings。
端点均有继承 globals，至多14项，全部属于原42-global baseline；无新增公理。
八次成功和14次失败证明尝试全部保留。

- Proof：`build/original-matmul/candidate-progress-proof-v1/report.json`，SHA-256
  `0216603a293e2f88aa118b8e8780c50c125e3b0b5872c1e04218d0c98d11dc26`。
- Actual source：`build/original-matmul/source-candidate-progress-v1/report.json`，SHA-256
  `a3cc835437fd82a628069ee77270e46e63064ce9579be86917fd7aecc8163cf6`。
- Native checker：`build/original-matmul/candidate-progress-native-check-v1/report.json`，SHA-256
  `3a98c142af5ae0626df97cfde242e6b69481797b63e0da5039dcc0fdf9070fd0`。

Native 验收六种模式：identity／real affine 接受，wrong-witness／reverse／
malformed／external Err 拒绝，均无 alarm。另保留并重现第一版 probe 的静态
输出字段错误：external Err 已提前停止时仍标为 final-checker-executed；后继
字段准确标为 checker 在 executable 中。该问题不改变检查结果。总七项
验收；另两个早期 accept 诊断保持绑定。Probe 没有执行 source/candidate
model、fallback 或完整 C/Asm，也没有测量收益或成本。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_original_matmul_candidate_progress.py --validate
python3 scripts/verify_original_matmul_candidate_progress.py --validate
python3 scripts/summarize_original_matmul_candidate_progress.py --validate
```

下一条实际链复用 `FramedNestedClightFor(I)(M)` 的 lowering／private frame，
实现保持原运算树的 double assignment backend，消费真实 model reads/stores。
它要把私有 I32 affine operands 接到原数组地址，并完成 candidate Clight
execution、公开出口恢复与 source metadata producer，再接 selected host 的
Csem→Asm。Final model progress 不代替这些步骤。全 corpus、顺序路线、
实际优化效果和完整调用成本验收继续保留。
