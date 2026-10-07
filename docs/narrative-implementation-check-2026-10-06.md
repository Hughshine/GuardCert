# Narrative 澄清的实现核对与下一项验收

2026-10-07 更新。面向框架使用者及实现者。重新 fetch 后，
`origin/topdown/research-positioning` 为 `271f6fc`；主线的
[paper narrative](topdown/paper-narrative.md) 和
[context-lifting](topdown/context-lifting.md) 正文与该分支一致。
本次按实现 `ea55a6f` 复核。原 `db6704c` 的核对已有 BODY／inner loop 后继；
下表更新到当前消费者，不再用当时的缺口描述已经接通的 inner scan。
此次重新阅读与计划更新没有新增功能、证明或运行测量。

后继实现已连接 [constant BODY joint scan](constant-body-joint-scan.md)：从真实原
BODY permissions 许可写地址与两个观察地址的实际比较；接受后生产所有 BODY
执行的观察保持，并填入 inner-prefix advance。30 端点审计及完整五次 source
stores／实际 scan fixture 通过。以下责任表按该消费者更新；原文的文档复核与
这项证明交付分开。完整 inner/outer runtime loops 和新 compiler 仍未安装。

2026-10-07 后继 [inner 短路扫描](constant-joint-inner-scan.md)已证明实际 loop、
first refusal／empty execution，并从整行接受直接生产全 column preservation 和
outer-prefix advance。14 端点审计通过。下表已按这个消费者更新责任与剩余缺口；
当前未完成项是实际 outer runtime loop、完整模型与原 AST／compiler 安装。

后继 [outer scan／完整双缓存源](constant-joint-outer-scan.md)已落实下面要求：实际
outer 运行消费 row producer，整段接受生产所有 rows／columns preservation，再
填入旧 two-cache transport。14 端点审计通过，kernel／既有 compiler 保持。
下表及验收顺序按这个后继更新；下面“重新阅读后的执行决策”仍保留 `ea55a6f`
复核时的任务说明，不将当时的计划算作本阶段证明。当前下一项是完整 canonical
model、实际输入 producer 和原 AST／candidate／whole-program 安装。

## 重新阅读后的执行决策

三方责任是代码与证明的归属；四个 `C_opt`／`C_derive`／`C_guard`／`C_host`
是逻辑环节，两者没有一一对应关系。比如一个安全比较会同时用语言的 pointer
definedness 定律和 domain 的 reached-write receipt。`C_host` 的 guarded-choice
分派也不等于 whole-program installation；后者还消费 region 与具体 site 证据。
不增加四个需要用户手写的 record 作为默认使用流程。

当前下一项保持为 domain 的真实 outer scan，复用现成语言服务和 inner producer，
不因这次澄清扩大 kernel。需交付的结论是：每个实际到达的 row 检查有许可；
拒绝不探测下一 row；整段接受生产所有 `(row,column)` 的观察保持，足以填入
`nested_expression_initial_cached` 的 `PRESERVE`。不能以一个新的同名语义回调
替代这项生产证明。

这里有两份不同的状态：原源 prefix 在执行过 stores 的 memory 中，guard 在原
入口 memory 中用 private cursors 读地址。逻辑 row／column 与 private cursors 的
word 对应、受保护参数／指针的 frame 都须实际建立；权限运输只能给比较许可，
不能给未来 header 稳定性或完整 cached execution。Empty outer 不读取 child，
empty child 不要求 BODY 参数／output pointer；负的 computed count 的保守回退策略
须由实际入口 gate 明确，不能以非负数学域代替原 machine test。

沿 narrative 第 8 节，先闭合这个约定范围的功能链；随后在同一 source／candidate
上替换或补充 certified compact 条件。验收分别记录代码大小、检查工作与计时、
有用接受域，且追踪替换条件时是否复用原候选与安装证明。同例作者负担区分数据
提案、checker 自动证明、手写语义桥和新增 language 定律；端点数量不代表复用收益。
这些仍是未完成项，已有 cursor scan 不作为它们的替代证据。

## 本轮澄清的执行含义

最小 kernel 只证明局部 guarded correctness。条件处理库和具体 language host
保持各自责任，不因目录或 record 名称而被算入核。`C_opt`、`C_derive`、
`C_guard`、`C_host` 是四个逻辑环节；使用者可以通过已验证的库或 checker
取得证据，不必重复填写四个 record，也不能省略某个环节。

验收顺序沿 `226ba94`：先闭合约定范围的实际功能链，随后改进条件推导与
生成；scan 可作中间实现。紧凑条件、运行成本、实际接受域和 per-instance
人工工作仍是最终要求。`271f6fc` 增加并行 CAV 写作，已有
[实际稿件](../paper/README.md)；相关里程碑同时更新正文和 evidence map。
不等待所有未来扩展，也不把文档核对算作功能交付。

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

当前 root-loaded-plus-offset 使用者已有
[compile_offset_affine_multi_regions_correct](../prototype/interface/ClightGuardedLoadedOffsetAffineMultiCompiler.v)
和提取／native 验收。它支持单个 loaded expression 根与 canonical affine
children，不能据此声称原 Figure 2 的第二 loaded child 已安装。

这些接口字段是证明义务，不能当作框架已经自动解决的功能。
`context_certificate.lift_refinement`／`rewrite_context.rewrite_lift` 是语言定律
的输入接口，也不能作为已完成 contextual closure 的独立证据。
Finite host 与 open host 的进展责任仍按
[Clight boundary 核对](clight-boundary-contract-review.md) 区分。

## 下一项的真正阻碍：安全域不能依赖缓存优化已经合法

单 loaded 根与 recursive affine body 的运行链已闭合。当前连接的是两个
loaded headers 与第三层原 `<5` 子循环：检查许可仍须由**原 loaded 源**生产，
随后才能证明完整缓存和重排合法。

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
早先要求的单 loaded 根 producer 已由
[affine_loaded_numeric_capture_domain](../prototype/interface/ClightLoadedAffineNumericGuard.v)
提供；后继
[affine_captured_package_guard_execution](../prototype/interface/ClightCapturedAffineNumericGuard.v)
从 captured words 许可 numeric probe，不要求完整 cached-source completion。
它们只关闭对应 numeric 检查义务，不提供两项观察的实际 joint scan。

[loaded_header_snapshot_read](../prototype/interface/ClightLoadedSnapshotInsertion.v)
已提供实际首次 header 的读取许可，零次 body 也有该 header。
同文件的 `private_source_preparation_contract` 已提供 private 初值无需一致的
原源运输桥。二者不会自动证明未来写入不改变观察。

## 当前最难连接的责任归属

| 当前服务／缺口 | 已有证据 | 接下来由谁完成什么 |
| --- | --- | --- |
| 有序读取 | `nested_expression_capture_execution`：outer 活动才读取 child，保持原 source public 执行 | 具体 site 绑定实际两个 header expressions、类型、freshness；不是任意 dependent preload |
| 已到达子域的权限 | `constant_body_joint_scan_execution` 已把原 `<5` BODY capabilities 接到全部写地址与 observer expressions 的实际比较 | Factory 仍须生产 checked leaf、scope／freshness 和原源绑定；权限不带回已改写数据，也不许可下一 column |
| 接受与推进 | `constant_joint_outer_scan_execution` 已运行真实 outer；`constant_joint_outer_acceptance_preserves_all` 生产全部 rows／columns preservation，first-row refusal／empty execution 有独立端点 | Factory 从实际 capture／numeric 和 namespace checker 生产 DOMAIN／SOURCE_WORDS／scope／header 等 typed inputs，组装真正完整 guard certificate |
| 缓存模型与候选 | `constant_joint_outer_cached_source` 已消费实际 preservation 取得整段双缓存源；private model-bound 桥和旧 candidate checker 可复用 | Domain 组装完整 canonical model 与 cross-entry candidate execution；cached source 已是接受的结果，不能移到检查许可的前提中 |
| 整程序安装 | 原 root-offset compiler 的具体语言 host 已有 | Factory／site 核对新 original AST、typed pool、scope／progress／placement 和 fallback；语言 host 消费这些证据，随后提取并验收原 Figure 2 适配 C |

上述表格列的是已有服务和待实例化义务。`BODY_CHECK`／`PRESERVE`／`ENCODE`
有类型，不代表实际检查实现或其 producer 已完成。当前未发现必须扩充
最小 kernel 才能表达的责任；主要工作在 language/domain 库及实际接入。

## 已纳入活动目标的验收顺序

1. 实际 inner／outer scan、全部 rows preservation 和接受后的完整双缓存源已
   完成。下一项连接 canonical model 与实际入口 producer；未到达 child 时
   消费独立 empty 服务，不为得到双观察 prefix 而读取第二 word。
2. 每个 BODY 的实际读写许可其内部全部比较；只有检查成功才能扫描下一
   BODY。Domain 另证跨 column/row 的完整覆盖和足够 scan fuel；入口的某个
   cell 有权限，不代表整个数学包络都可安全比较。
3. 在稳定性已成立后，用语言执行运输接到缓存源，再消费原 candidate
   certificate。可复用的
   [strict_active_loop_transport](../prototype/interface/ClightActiveLoopTransport.v)
   仍要求实例提交 `TEST`、`BODY`、`WEAKEN` 和 `INCREMENT`，不是自动缓存器。
4. 用真正原 AST 作 source key，保留原 loaded fallback；绑定 typed private
   pool、scope、公开出口、独立 source progress 和完整程序安装。之后才提取
   并验收真实 C 的接受、拒绝与上下文，包括 bound 被写后提前停的源。

各项分别记录新语言定律、domain 证据和复用的库；每个实际使用者列明数据
提案、checker 自动取得的证明和仍需手写的语义桥。Contract clause factoring
保留为实际受阻案例驱动的设计问题。功能链闭合后验收 compact sufficient
conditions、P4 计时和同例已有工作／作者责任比较；代码大小、运行检查成本、
有用接受域分别报告。完整目标保持 active。
