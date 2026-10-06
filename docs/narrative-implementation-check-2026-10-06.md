# Narrative 澄清的实现核对与下一项验收

2026-10-06。面向框架使用者及实现者。重新 fetch 后，
`origin/topdown/research-positioning` 为 `7d94d81`；主线的
[paper narrative](topdown/paper-narrative.md) 和
[context-lifting](topdown/context-lifting.md) 正文与该分支一致。
本次核对采用其最小 kernel 截止与三方责任划分，没有新的功能或证明结果。

## 澄清怎样落实到现有接口

最小 kernel 的结论是局部 guarded replacement 正确。只读前台、条件组合、
prefix scan、简化和条件推导属于核上的库。语言 host 另证完整程序安装；
优化方和具体 rewrite site 提交该定理要求的 region 与 placement 证据。

| 责任边界 | 当前实际消费者 | 使用者仍需提供什么 |
| --- | --- | --- |
| Kernel：组合局部证书 | [guardify_preservation](../prototype/interface/GuardInterface.v) 消费 guard 与 conditional preservation，处理接受及拒绝两种入口关系 | 对实际 source、candidate、check 的证书；核不发现优化前提 |
| Clight 检查库：实现检查语义 | [materialized_execution_certificate](../prototype/interface/ClightMaterializedCertificate.v) 从实际检查执行与确定性取得安全、可用性和全部完成执行的 soundness | `ENCODE`：在安全域 D 中的真实执行、defined Boolean、protected frame，以及 `accepts ⇒ P(original entry)` |
| Domain／优化：连接源与候选 | [materialized_preserving_rule](../prototype/interface/ClightMaterializedPreservation.v) 消费 source-domain producer 和 cross-entry candidate-local | 原源支持 D；接受前提足够；候选从检查后的真实入口执行并保持公开出口和 memory |
| Clight region 库：局部到可安装契约 | 同文件的 `materialized_preserving_region_contract` 复用 temp transport 和 big-step→small-step | 作用域、源 writes、protected ports；该契约仍以 silent normal 源完成为前提 |
| Language host＋具体 site：完整程序 | [compile_materialized_affine_regions_correct](../prototype/interface/ClightGuardedAffineNestCompiler.v) 消费 checked table、实际安装证明和 CompCert 后端 | 实际 source key、supported/progress、pool freshness、placement；局部正确性本身不免除这些证据 |

这些接口字段是证明义务，不能当作框架已经自动解决的功能。
`context_certificate.lift_refinement`／`rewrite_context.rewrite_lift` 是语言定律
的输入接口，也不能作为已完成 contextual closure 的独立证据。
Finite host 与 open host 的进展责任仍按
[Clight boundary 核对](clight-boundary-contract-review.md) 区分。

## 下一项的真正阻碍：安全域不能依赖缓存优化已经合法

当前已接入的 deep affine 源使用稳定 temps；loaded/dependent compiler 则
已经处理受限的两层源。把两者组合时，需要从**原 loaded 源**生产检查许可，
再证明缓存和重排合法。

以下只是说明证明义务的 C 例子，不计为 matcher 或 compiler 的新能力：

```c
int n = 2, out[1];
int *bound = &n;
for (int i = 0; i < *bound; ++i)
  for (int j = 0; j < i + 1; ++j) {
    out[i] = j;
    *bound = 0;
  }
```

原源只执行 `(i,j)=(0,0)`，随后 outer header 读到零并退出。若先缓存
入口的 2，后续将访问 `out[1]`。因此“原源有限正常完成”不能推出
“缓存源有限正常完成”，也不能推出按整个缓存域探测地址的安全性。
非 alias／观察稳定性正是待检查的前提，不能预置在 D 中。

源码给出一个可复用的起点：
[affine_source_domain_guard_execution](../prototype/affine-nest/AffineNestSourceGuard.v)
先从完整 stable-temp 源取得 first-header 与 active-first-path 参数 receipt；
它调用的
[affine_domain_guard_execution](../prototype/affine-nest/AffineNestDomainGuard.v)
只消费这两类 receipt，不要求完整缓存源执行。
下一实现应从真正 loaded 源及安全 private capture 生产这些 receipt，复用
后者的 numeric guard；这一 producer 尚未证明。

[loaded_header_snapshot_read](../prototype/interface/ClightLoadedSnapshotInsertion.v)
已提供实际首次 header 的读取许可，零次 body 也有该 header。
同文件的 `private_source_preparation_contract` 已提供 private 初值无需一致的
原源运输桥。二者不会自动证明未来写入不改变观察。

## 已纳入活动目标的验收顺序

1. 从原 loaded header 和实际到达的 child/body 取得 numeric guard 所需的
   first-path receipt。未到达 body 时保守拒绝，并核对未定义参数没有被读取。
2. 从已到达的实际读写生产物理比较许可；只有检查成功才能安全推进后续
   点。Domain 另证完整写足迹覆盖、足够 scan fuel 和观察保持。入口的某个
   cell 有权限，不代表整个数学包络都可安全比较。
3. 在稳定性已成立后，用语言执行运输接到缓存源，再消费原 candidate
   certificate。可复用的
   [strict_active_loop_transport](../prototype/interface/ClightActiveLoopTransport.v)
   仍要求实例提交 `TEST`、`BODY`、`WEAKEN` 和 `INCREMENT`，不是自动缓存器。
4. 用真正原 AST 作 source key，保留原 loaded fallback；绑定 typed private
   pool、scope、公开出口、独立 source progress 和完整程序安装。之后才提取
   并验收真实 C 的接受、拒绝与上下文，包括 bound 被写后提前停的源。

各项分别记录新语言定律、domain 证据和复用的库。当前没有发现需要修改
kernel 的不可表达义务；contract clause factoring 保留为实际受阻案例驱动
的设计问题。P4 计时和同例已有工作／作者责任比较继续独立验收，完整目标
保持 active。
