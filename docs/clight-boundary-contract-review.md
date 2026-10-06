# Clight boundary 契约：核对最新 context-lifting 评审

2026-10-06。本文回答 `topdown/research-positioning` 在 `8c098ed` 新增的
[context-lifting](topdown/context-lifting.md) 问题，依据当前源码。
它是接口核对及后续设计约束，不是已经实现的新 guarantee/requirement API。

当前结论是保留小的通用 kernel，明确语言 host 的安装责任，并先复用已有的
关系和运输定理。Finite 与 open host 的 progress 区别有实际语义原因；
没有证据支持把它们改成可任意组合的 clause record。

## 已经共用什么

| Clause | 当前复用 | 仍由具体实例／位置提供的证据 |
| --- | --- | --- |
| temp/state | [temp_agree](../theories/ClightTempFrame.v) 已有 reflexivity、transitivity、weaken；[structured transport](../theories/ClightProjectedExecution.v) 按作用域运输实际执行 | 本次源／候选的公开出口与 writes；protected 参数不被修改 |
| memory | [memory_equivalent](../theories/CompCertMemoryEquivalence.v) 与 [实际 memory-step transport](../theories/ClightMemorySteps.v) | 本次访问／store 的模型对应；本次足迹、权限与 bound 稳定性 |
| trace/effect | private region 与 guard realization 都使用实际 `E0` 执行 | 源／候选和条件本身满足 silent 路径；不能把有外部事件的候选直接交给此 host |
| control/placement | statement scope、label-free、private pool 与 whole-program transformer | 具体 source 通过 supported checker；target 没有内部 labels；source syntax 与证书匹配 |
| private resources | [fresh pool](../theories/ClightPrivatePool.v)、temp frame、[realization 的 fresh/frame/dispatch](../prototype/interface/ClightGuardRealization.v) | candidate lowerer 使用已分配 counter pairs；shared lowering 的 result 不被分支或 context 读取 |
| source representation | [flatten transport 与 quiet suffix](../prototype/interface/ClightSequenceContracts.v)、[source-prefix contract](../prototype/interface/ClightSourceObservation.v) | prefix 实际 producer、suffix quiet check、实际 source equality/flattening |

这些共享已有源码和消费者。例如 quiet suffix 定理先取得局部 target steps，
再分别运输 suffix 的 temp 和 memory 执行。它保留 suffix 的真实 stores，
不要求 suffix 没有内存 effect。Direct/shared realization 共用同一逻辑
condition，却用不同 private-entry 关系解释真实 guard 代码。

## 两种 progress 不能互换

[projected_region_contract](../theories/ClightPrivateRegion.v) 量化任意实际
program、entry、function 和 continuation。它以 source 的 silent normal
完成执行为前提，交付 target 的 silent small-step 到达、live temp agreement
和 memory equivalence。**仅这个 contract 没有保证 source 不会永远停留在片段内。**

[private host proof](../theories/ClightPrivateRegionProof.v) 还消费独立 source
progress 及合法 placement。新 [loaded host](../prototype/interface/ClightLoadedRegionHost.v)
只是选择已证明的 loaded/sequence progress classifier，复用该安装证明。
本次 signed loaded nested progress 用机器最大值作迭代距离，不假设 bound
load 稳定。因此 source 写 bound 的 fixture 可以通过语言 progress 检查，
同时被优化的稳定性 checker 拒绝；两项责任没有互相偷用假设。

[open_region_protocol](../theories/ClightOpenRegionContract.v) 直接匹配每一个
source step。只有零步匹配需要 index 下降；出口到达时才要求
`open_region_exit`，其中再次使用 temp agreement 和 memory equivalence。
它用于可能无限执行的完整 fallback，其 advance 字段比 completed-run
contract 实质更强。Exit 的 state/memory clause 可以共用基础关系，
有限完成与无限小步匹配的证据不能通过 record renaming 相互转换。

Guard 的 [realization_dispatch](../prototype/interface/ClightGuardRealization.v)
又有另一条 progress 边界：它只保证有限到达所选分支，完全不要求该分支
完成。`clight_normal_realization` 另外提供完成分支的 temp 运输。
这已经体现共享 clause 与依赖证据的区分，没有把 dispatch 和 whole-region
termination 混为一项。

## 谁承担 site evidence

Kernel 的 `context_certificate`／`rewrite_context` 消费语言提供的 lifting
定律。通用组合定理不自行证明 contextual closure。

语言库证明 scope、private resources、continuation、temp/memory 运输及
program simulation。优化实例交付实际 local contract；选择器再核对 source
支持域、target label-free、作用域及 pool freshness。这些都是源码中的
证明或 executable checker，而不是给每个候选新增未证明的 host 假设。

当前 `live` 保守使用整个源 program 的 temps。它不是按每个 rewrite site
推断最小 live-out，也没有自动推断 `ContextAccepts B C`。
`temp_agree_weaken` 可以削弱已经取得的 temp guarantee，但这不自动完成
一个较弱 guarantee 的安装：还必须证明外围 scope 和 continuation 只依赖
那部分状态。将 live 集合缩小会改变 proof obligations，不能只替换一个参数。

## 是否需要新契约代数

当前没有发现必须通过更弱 memory relation 或额外控制出口才能安装的
新 loaded 规则。它保持完整 memory、所有源 public temps、silent normal
出口，正好复用现有 private-region host。此次缺口来自 source reads、
稳定性与 loaded progress；它们已通过 producer 和协议解决。

因此先保留契约，记录下一项具体检验：private snapshot 插入后能否继续
复用现有 private-entry/frame 运输，依赖读取能否保持 original-entry facts。
若出现受阻实例，再判断 guarantee/requirement 加 entailment 是否减少重复
证明，或是否需要更广的控制／memory boundary。不能用相似字段数量声称
作者负担已经降低。

SSA/CFG 可继续采用 selected live-out、memory 和 trace 的角色，但须定义
phi／successor-edge 关系及多入口 placement；汇编另需 flags、scratch registers
和 PC 的实际关系。Clight 的 record 本身不作为跨 IR 的接口。第二 IR
当前仍是可选表达力验证，不计入已实现功能。

本次采纳的论文表述是：kernel 证明局部 guarded transformation；语言/IR
host 提供 reusable region contracts 和 installation theorems；优化和每个
rewrite site 提供相应 guarantee 与 placement evidence。
