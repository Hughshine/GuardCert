# 原始嵌套循环的 guarded candidate 与完整程序接入

2026-10-07，接续 [完整 physical guard](nested-constant-physical.md)。本阶段连接
原 source、动态稳定性检查、多数组 alias 检查、候选 validator／lowering、局部
guarded preservation、typed private pool 和既有 Clight region host，得到新的
`compile_ncs_multi_regions_correct` Csem→Asm backward simulation。尚未提取或运行
新编译入口，非空数组上的真实候选接受仍待验收；不能把定理当成 Figure 2 已优化运行。

## 使用者提交什么

[ClightNestedConstantMultiFactory.v](../prototype/interface/ClightNestedConstantMultiFactory.v)
暴露 `check_ncs_multi_region live pool describe propose source`。`describe` 是不受信任
的片段识别器，返回 parameters、affine proposal、nested shape 数据；`propose` 返回
Loop candidate 及现有 index/site/split/tiling/domain/chain checker 支持的 evidence。
选择片段和提出变换的策略仍由使用者决定。

`check_ncs_multi_site` 重查实际原 AST、scope、缓存与 helper freshness、leaf effect、
numeric package、两套 scan namespace／allocation、canonical model scope，以及生成
检查代码的语言支持。Factory 核对 captures/helpers 在 typed pool 中，把受保护
输入从 candidate counter pairs 排除，生成实际 Clight candidate，并调用既有
`checked_affine_candidate`。只有成功返回候选的分支才加入 region table；拒绝项保留
原 source。Effectful validator 的 alarm/termination 行为不是本阶段新增的 totality
保证，最终编译定理以 `mayReturn ... (OK target)` 为前提。

此 profile 的用户没有 source/model execution、future header stability、alias 或
guard correctness 语义回调。数据 checker 及本实例的证明生产这些证书。新实例仍需
自己实现匹配、前提推导和 source/model 证明，不能从此例推断任意 rewrite 的自动证明。

## 实际检查与接受入口

检查先执行原有有序 capture、positive/numeric gates、helper 准备和完整 physical
stability scan。只有 stability 接受才运行既有多数组 alias-only guard。`ncs_multi_guard_execution`
消费原 source 的 silent normal execution，生产真实检查执行、same memory、public
frame、defined Boolean，以及检查后的原 source 执行。Numeric 或 physical refusal
不执行 alias scan；fallback 使用原 AST。

`ncs_multi_canonical_at_guard_exit` 先沿 ports frame 将已生产的 canonical execution
运输到实际 physical guard exit，再许可 alias guard。这里重用 checked source scope
和写集合，不要求任意位置映射或整个 private temp environment 相等。

[ClightNestedConstantMultiCertificate.v](../prototype/interface/ClightNestedConstantMultiCertificate.v)
定义 model anchor、presumption 和 accepted-entry relation。Anchor 含真实 model entry、
同一 ge/env/memory、alias acceptance，以及每次完成的原 source execution 对应的
canonical execution／公开出口。它由 check receipt 生产；quiet determinacy 将一份实际
source/model receipt 扩展到同入口所有完成执行。

Presumption 是 anchor 的存在性。Accepted-entry relation 额外携带**同一个** anchor
及其到实际 checked entry 的 ports frame，并保存原 public scope。这项状态运输证据
不能只由一个 Boolean 或 presumption 的存在性替代。Refused-entry relation 只要求
原 public scope frame，不给出前提不成立的反向结论。Kernel 的既有接口能够表达它们，
没有增加语言或 optimizer 专属字段。

## 候选、kernel 与全局 host

`ncs_candidate_reference_local` 消费现有 bounded candidate certificate、实际 lowering
结果、model execution 和 checked-entry frame，执行实际候选及原有 shadow exit
restoration，得到同 final memory 和 public exit。`ncs_multi_local_certificate` 将其
包装成 kernel 的 preservation certificate；`ncs_multi_guarded_preservation` 调用既有
`GuardInterface.guardify_preservation`。这证明 source→guarded source 行为保持，不把
这个 preservation endpoint 改称相反方向的任意 fragment equivalence。

`ncs_multi_region_contract` 交付既有 projected region contract。
[ClightGuardedNestedConstantMultiCompiler.v](../prototype/interface/ClightGuardedNestedConstantMultiCompiler.v)
收集已检查的 source/target 表，再调用 `apply_expression_region_table`。语言 host
核对原源 signed-expression progress、placement 和 private pool；其 forward simulation
与 SimplExpr、SimplLocals、CompCert backend 合成，最后转成 Csem→Asm backward simulation。
完整程序端点不是把 local normal-completion 定理直接套在任意 context 上。

| 归属 | 本阶段责任 |
| --- | --- |
| 最小 kernel | 消费 guard／preservation certificates，得到局部 guarded preservation；未改动 |
| 既有语言／条件库 | 实际 Clight checks／dispatch、quiet determinacy、temp transport、state frames、typed resources、progress／region installation／backend |
| 此优化实例 | 从 checked source 和实际 receipt 生产 canonical/alias facts、private anchor／entry transport，连接候选证明和 region contract |
| 不受信任使用者算法 | 发现片段，提出 source description、candidate 及可检查 evidence |

四个逻辑环节与三方归属分别记录：`C_opt` 复用候选 checker；`C_derive` 由当前
source/stability/alias 到 model anchor 的实例证明提供；`C_guard` 由真实检查执行和
语言 certificate producer 提供；dispatch 的 `C_host` 使用 materialized host。
完整程序 installation 另外由 region contract 和 language host 证明，不与 dispatch 混写。

## 验证与后续验收

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make nested-constant-multi-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make nested-constant-multi-validate
```

新 audit 绑定 physical parent 的源与对象，独立查询所有新 endpoints，要求 kernel
闭合、新 compiler 与旧 loaded-offset compiler 使用相同 global assumption 集合。
25 endpoints（15 domain／3 compiler／7 fixtures）、597 required dependencies、
1,097 源摘要通过；domain 最大 14 项、compiler 42 项、fixtures 最大六项既有
globals，均属于旧 compiler baseline。新旧 compiler 的 assumption 集合完全相同，
没有新增 global axiom，父 physical 源／对象保持。Report SHA-256：
`d569c7a3a85a05130a2fe9d31b1c8eb39993f9bd4554cccaf1fe0adb39779744`。

Fixtures 核对两种 offset 的实际 site 接受、缺第二 scan resources 的静态拒绝、原
三层 AST 的 host progress 支持、private captures 排除，以及 actual empty source 的
完整 multi-guard execution。三层原 Loop 本身作为 identity candidate 确实有后端代码；
这不是非平凡调度被 native 执行的证据。

下一项提取该入口，提供实际 C frontend descriptor 和非 identity candidate，核对
原 AST key／generated guard／候选安装；运行独立数组、两种 header alias、empty／
nonzero row／numeric refusal、完整数组及公开出口。随后比较 compact 条件、成本、
有用接受域和同例作者工作量。原 Figure 2 的 16-call `not-supported` report 保留，
仅新实验能改变该例的优化覆盖结论。完整目标 active。
