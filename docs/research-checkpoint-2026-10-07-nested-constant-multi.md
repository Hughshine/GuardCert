# 2026-10-07：nested guarded candidate／compiler checkpoint

前一 goal turn 的 `c420aaa` 是完整原源 header-stability guard。当前继续同一
完整目标，并重新 fetch narrative 到 `271f6fc`；main 正文一致。本轮把候选与
语言 host 的实际消费链连接起来，详见 [接口与责任](nested-constant-multi.md)。

## 本阶段产出

`MultiSite` 数据 checker 核对 canonical scope、两套 scan resources 和真实检查
AST。`MultiExecution` 沿 ports frame 将 canonical execution 运到 actual physical
guard exit，再许可现有多数组 alias-only guard；其 receipt 保存实际 original
SOURCE、public frame、defined Boolean 和 accepted model execution。

`MultiCertificate` 从接受 receipt 生产 private model anchor，quiet determinacy
将它推广到同入口所有 source completion。Accepted-entry relation 保存该 anchor
与 actual checked entry 的对应，没有假定 private snapshots 全不变。
`Candidate` 消费旧 bounded candidate certificate／实际 lowering 和使用的 frame；
`MultiPreservation` 包装 guard／preservation certificates，调用未改动的 kernel，
并交付现有 projected region contract。

`MultiFactory` 消费不受信任 source descriptor 和 candidate/evidence，检查 typed
pool/captures、实际 lowering 和既有 validator；`ClightGuardedNestedConstantMultiCompiler`
通过现有 signed-expression region host 和 CompCert backend 合成
`compile_ncs_multi_regions_correct` 的 Csem→Asm backward simulation。
端点以成功 `mayReturn ... (OK target)` 为前提，不提供 validator 的 totality 保证。

最小 kernel 止于局部 guarded correctness，没有修改。条件／temp／quiet 服务为
上层语言库，完整程序安装由语言 host 提供；三方责任与 `C_opt`／`C_derive`／
`C_guard`／dispatch `C_host` 四条逻辑链分别记录。Model correspondence 在本实例
由 producer 实现，未转成要求用户提交的 source/model 语义回调。

## 真实验证范围

Rocq closure audit：25 endpoints（15 domain／3 compiler／7 fixture）、597 required
dependencies、1,097 source digests。Domain 最大 14 项、fixtures 最大六项既有
globals；新 compiler 的 42 项与旧 loaded-offset compiler **集合完全相同**。
Kernel 闭合，没有新增 global axiom，父 physical 源与对象保持。

Proof report SHA-256：
`d569c7a3a85a05130a2fe9d31b1c8eb39993f9bd4554cccaf1fe0adb39779744`。

`nested-constant-multi-validate` 已通过。Fixtures 检查 Int.one／Int.zero source
offset 的实际 site 接受、缺第二 scan resources 的拒绝、原三层 AST 的 language
host progress 支持、private captures 不能作 candidate counters；另证明 actual
empty original source 的完整 multi-guard receipt，及三层 identity Loop candidate
确实产生实际 backend code。Identity backend fixture 不算非平凡调度被执行。

摘要、intro、case study、evaluation、conclusion 和 evidence map 同步当前端点，
不再把已完成的 candidate／host 连接列为待办。Offline Tectonic 构建 11 页，
无 undefined refs/citations 或 overfull boxes；第 1–2、6–11 页渲染并查看。
最终 paper report SHA-256：
`0020aab2dcdcfd97aef70aa58bc1fa907602aa1fac3c0310e63b54ce38b17837`。

## 剩余验收

当前没有新 nested extraction、实际 C descriptor、非 identity active array
运行、native matrix 或 timing。Figure 2 原 16-call `not-supported` report 不改；
新 Csem→Asm theorem 不能证明此例的实际 matcher／候选安装已经成功。
下一项提取新入口，给出从实际 C 获取 shape／proposal 的 descriptor，提出非
identity candidate，核对 original key、guards 和 installed code，再跑非空数组、
两种 header aliases、empty／nonzero-row／numeric refusal、公开 exits 和完整
程序 contexts。Functional chain 实际运行闭合后，继续 compact 条件、成本／
有用接受域与同例作者工作比较。完整目标保持 active。
