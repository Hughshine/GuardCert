# Narrative 澄清的实现核对与下一项验收

2026-10-07 最新实运行：[actual nested frontend](nested-frontend-native.md)已在既有
Figure 2 适配源实际安装并运行 interchange／tiling；zero-index root 和 prefixed
resets 的执行对应由语言库证明，fallback 保留原 AST。新 Csem→Asm entry 已提取；
75 full assembly calls、16 Clight dispatch calls 与 6 machine probes 单列并通过。
Kernel 未改，三方责任／四条证书链保持。下面旧阶段与原 16-call `not-supported`
报告固定保留其当时范围；当前能力以新 native 报告为准，仍无 compact 条件／
成本／完整 BT layout／作者工作验收，完整目标 active。

2026-10-07 最新后继：[nested guarded candidate／compiler](nested-constant-multi.md)
已连接实际 canonical source→alias guard→candidate→kernel preservation→projected region
contract→typed factory／语言 host→Csem→Asm。Model anchor 及实际 checked-entry frame
由执行 receipt 生产，没有 source/model 语义回调；kernel 不变。三层原 AST 的 host
progress 支持有 fixture。后文阶段记录保留当时边界；新入口的 extraction／实际 C
识别和非空数组非 identity 优化运行仍待验收，原 Figure 2 16-call report 不变。
Narrative 重新 fetch 到 `271f6fc`，正文与 main 一致；三方责任和四条证书链按新文档核对。

2026-10-07 更新。面向框架使用者及实现者。重新 fetch 后，
`origin/topdown/research-positioning` 为 `271f6fc`；主线的
[paper narrative](topdown/paper-narrative.md) 和
[context-lifting](topdown/context-lifting.md) 正文与该分支一致。
本次对 `18e1b50` 和本轮完整 header-stability guard 后继复核。远端基线为 `271f6fc`，
没有新的未同步正文。下表按当前消费者更新；重新阅读本身不计作功能交付。
本轮另有原源入口证据的实际 producer 与独立 proof audit，见下段；没有新运行测量。

[Canonical 后继](nested-constant-model.md)已将整段双缓存源接到旧 affine AST，
并从 checked package 取得真实 Loop 内存执行。12 端点审计通过，helper/frame
和 leaf quiet/write 的具体循环运输已闭合，没有 source/model 语义回调。
[Capture／numeric 后继](nested-constant-numeric.md)已从实际首次 leaf 生产参数
定义性，执行有序双 gate，并由接受生产逐点 DOMAIN／SOURCE_WORDS。24 端点
审计通过。[Checked site／actual entry](nested-constant-site.md)后继已核对原 AST、
scope／namespace，实际生产 observer receipts、header laws 和检查后的初始 prefix。
Runtime ROW0 gate 去掉额外的 context 初值前提，template AST 与 runtime ghost
fields 的分离也已证明。37 端点审计通过。[完整 physical guard](nested-constant-physical.md)
已完成 helper 新入口与全部 scan inputs；接受生产真实 canonical/Loop source 执行，
model entry 明确 framed 到实际 guard exit。39 端点审计通过。下一项 candidate
跨入口／dependency-alias checker、guarded factory 和 whole-program 安装；原源
silent normal completion 域不替代 host progress/divergence 合同。三方责任、四个
逻辑环节及独立语言安装边界继续有效。

后继实现已连接 [constant BODY joint scan](constant-body-joint-scan.md)：从真实原
BODY permissions 许可写地址与两个观察地址的实际比较；接受后生产所有 BODY
执行的观察保持，并填入 inner-prefix advance。30 端点审计及完整五次 source
stores／实际 scan fixture 通过。以下责任表按该消费者更新；原文的文档复核与
这项证明交付分开。Inner／outer 和 canonical 后继见下段与首段；新 compiler
仍未安装。

2026-10-07 后继 [inner 短路扫描](constant-joint-inner-scan.md)已证明实际 loop、
first refusal／empty execution，并从整行接受直接生产全 column preservation 和
outer-prefix advance。14 端点审计通过。下表已按这个消费者更新责任与剩余缺口；
该阶段的 outer／模型缺口已由后继关闭；原 AST／compiler 安装仍待完成。

后继 [outer scan／完整双缓存源](constant-joint-outer-scan.md)已落实下面要求：实际
outer 运行消费 row producer，整段接受生产所有 rows／columns preservation，再
填入旧 two-cache transport。14 端点审计通过，kernel／既有 compiler 保持。
下表及验收顺序按当前消费者更新，阅读记录不计作实现证明。Canonical 后继见首段；当前
下一项是实际输入 producer 和原 AST／candidate／whole-program 安装。

## 重新阅读后的执行决策

三方责任是代码与证明的归属；四个 `C_opt`／`C_derive`／`C_guard`／`C_host`
是逻辑环节，两者没有一一对应关系。比如一个安全比较会同时用语言的 pointer
definedness 定律和 domain 的 reached-write receipt。`C_host` 的 guarded-choice
分派也不等于 whole-program installation；后者还消费 region 与具体 site 证据。
不增加四个需要用户手写的 record 作为默认使用流程。

真实 outer scan 已由 domain producer 完成；整段接受已生产全部 `(row,column)`
观察保持并填入旧 `PRESERVE`。Canonical source transport 现也闭合。
当前 [capture／numeric producer](nested-constant-numeric.md)已由原 first leaf
生产参数定义性，执行有序 capture／双 gate，接受后提供逐点 DOMAIN／SOURCE_WORDS。
24 端点审计通过，没有要求调用者新增对应语义回调。Checked-entry 后继已经
生产 namespace／scope 和实际 observers／header／initial prefix。最新后继实际
执行 helper 准备并完整实例化 physical scan；接受导出 canonical／Loop source，
model entry framed 到 actual guard exit。下一项 candidate dependency/alias 检查、
cross-entry 候选和 guarded factory／host。继续复用已有语言服务，
不因这次澄清扩大 kernel。
不能以新增的 `ENCODE`／scope／freshness 语义字段代替这些实际 producer。

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
| 有序读取 | 原 site、runtime row gate、有序 capture、helper 初始化已接入完整 `ncs_physical_guard` | 接候选 factory；不是任意 dependent preload |
| 已到达子域的权限 | 完整 outer consumer 从 site 的 checked leaf／scope／freshness 和实际 prefix 许可所有 BODY comparisons | 保持此 source-definedness 顺序连接 candidate guard；权限不带回已改写数据，也不自行许可下一 column |
| 接受与推进 | 完整代码消费 DOMAIN／SOURCE_WORDS、observers/header 和 helper 后 prefix，接受后推进全部 rows／columns；template syntax 等式已证明 | 接受条件还要交付 candidate 所需 dependency/alias 事实，不能把 header stability 等同于任意重排合法 |
| 缓存模型与候选 | `ncs_original_physical_guard_execution` 的接受结果取得 canonical Clight；`ncs_physical_accepted_source_loop` 取得真实 Loop 以及 model entry→guard exit frame | Domain 沿此 frame 证明 candidate 的实际 context／pointer-cell 视图，再接 validator／lowering／public exits；cached execution 不能成为检查许可前提 |
| 整程序安装 | 原 root-offset compiler 的具体语言 host 已有；新 guard 安全域为原源 silent normal completion | Factory 核对新 original AST、typed pool 与 fallback；language host 连接 scope／progress-divergence／placement，随后提取并验收原 Figure 2 适配 C |

上述表格列的是已有服务和待实例化义务。`BODY_CHECK`／`PRESERVE`／`ENCODE`
有类型，不代表实际检查实现或其 producer 已完成。当前未发现必须扩充
最小 kernel 才能表达的责任；主要工作在 language/domain 库及实际接入。

## 已纳入活动目标的验收顺序

1. 实际 inner／outer scan、全部 rows preservation、接受后的完整双缓存源和
   canonical model 已完成；全部 numeric／DOMAIN／SOURCE_WORDS、helper 后入口和
   完整 guard 已连接。下一项 cross-entry candidate／factory；未到达 child 时
   消费独立 empty 服务，不为得到双观察 prefix 而读取第二 word。
2. 每个 BODY 的实际读写许可其内部全部比较；只有检查成功才能扫描下一
   BODY。Domain 另证跨 column/row 的完整覆盖和足够 scan fuel；入口的某个
   cell 有权限，不代表整个数学包络都可安全比较。
3. 在稳定性已成立后，用语言执行运输接到缓存源，再消费原 candidate
   certificate。可复用的
   [strict_active_loop_transport](../prototype/interface/ClightActiveLoopTransport.v)
   是有参数的语言定律；当前固定三层实例已由
   `nested_constant_closed_preinitialized_model` 生产 TEST／BODY／frame，无须用户
   再交 source/model 语义回调。它仍消费真实 helper 初始化和 checked leaf 数据。
4. 用真正原 AST 作 source key，保留原 loaded fallback；绑定 typed private
   pool、scope、公开出口、独立 source progress 和完整程序安装。之后才提取
   并验收真实 C 的接受、拒绝与上下文，包括 bound 被写后提前停的源。

各项分别记录新语言定律、domain 证据和复用的库；每个实际使用者列明数据
提案、checker 自动取得的证明和仍需手写的语义桥。Contract clause factoring
保留为实际受阻案例驱动的设计问题。功能链闭合后验收 compact sufficient
conditions、P4 计时和同例已有工作／作者责任比较；代码大小、运行检查成本、
有用接受域分别报告。完整目标保持 active。
