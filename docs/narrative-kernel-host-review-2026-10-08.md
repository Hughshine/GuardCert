# Narrative 对照：kernel、条件服务与 host boundary

2026-10-08。当前 main 基线为 `2d1d08a`。本次 `git fetch origin` 后，
`origin/topdown/research-positioning` 仍为 `12419c1`；
`docs/topdown/paper-narrative.md` 和 `context-lifting.md` 与 main 无差异。
只有当前 checkout；未读取其他作者的未跟踪文件。以下吸收可见正文的澄清，
不声称观察到了新的已推送提交。

## 对实现的约束

核心问题是 verified guarded transformation 的可复用证明边界。主要实例
仍须完成实际 optimistic polyhedral compilation；局部条件定理、扫描或一个
手写候选不能单独作为完成。通用 kernel、语言实例、优化器/域库分工如下。

| 责任 | 当前可核对的接口/生产者 | 本轮处理方式 |
| --- | --- | --- |
| Kernel 组合局部证书 | `GuardInterface.v` 的 `guard_certificate`、`conditional_certificate`、`preservation_certificate` 与 `guardify_refinement`/`guardify_preservation` | 保持，不加入 Clight 或 polyhedral 语义 |
| Readonly frontend 与局部化 | `GuardedRewrite.v` 的 `readonly_condition`、`readonly_condition_entails`、`localized_conditional_equivalence` | 作为便利接口和库，不把局部桥接前提说成自动生产 |
| 语言/IR 执行和安全 | Clight expression/decision semantics、private/temp/memory transport、check-plan lowering | 重复 probe 服务消费这些已证明的语言规律 |
| 域库的前提与候选对应 | `ClightMultiTensorPackageExecution.v`、`ClightMultiTensorAffinePackageCandidates.v`、loaded-source/header 服务及实际候选 checker | 沿用原 setup 充分性和候选证明，不重证调度/分块 |
| 语言 host 的全局安装 | `ClightSelectedExpressionHost.v`、`ClightSelectedRegionProof.v`，再接 CompCert backend | 消费新的 region guarantee，检查原源 progress、scope、标注位置和 private pool |
| 具体 site 证据 | selected frontend、资源 checker 与 placement 分析 | 属于语言/域库接入责任；支持族的源码用户只给标注 C 和策略选项 |

`context_certificate.lift_refinement` 和 `rewrite_context.rewrite_lift` 是
host 提供的证明字段。Kernel 的 program theorem 组合该字段与局部正确性；
字段本身不解决 contextual closure。Refinement 与 preservation 的方向不同，
也不能统一称为任意语言的全局等价。

## 对 context-lifting 八个问题的代码回答

1. **已经共享和重复的 clauses。** `ClightPrivateRegion.v` 的
   `projected_region_contract` 与 `ClightOpenRegionContract.v` 的
   `open_region_exit` 都使用 `temp_agree live` 和 `memory_equivalent`，并
   在 `Sskip`/原 continuation 处交接。`ClightRegionBoundary.v` 将 trace、
   outcome、live-out 和 memory 单独表达为 `boundary_observe`；它的 write
   frame 是局部 effect 服务，不是新的 installation theorem。
2. **必要差异。** Finite projected contract 消费一次 `E0`、`Out_normal`
   source execution，构造 target 的有限 `star`。Open protocol 提供
   indexed `open_match` 和逐步 `open_advance`，零步匹配需降低 index；不
   消费 source termination。这不是 record 字段名称的差异。
3. **可以先复用什么。** 优先复用现有 temp/memory/trace transport 和出口
   relation；`ClightSequenceContracts.v.projected_region_quiet_suffix` 已
   分别运输 suffix 的 temps 和 memory。现在没有证据要求换 kernel API。
4. **一次证明与每次实例化。** Continuation simulation、globalenv 保持、
   private declarations 和 backend 由语言库证明；域库生产实际 source/model/
   candidate 对应；site 提供 scope、资源和支持入口。新的 guard 不能借用
   一个未证明的 cached-source 执行来许可其原源读取。
5. **当前边界是否阻塞。** 当前已安装的静默、正常出口 store-loop 族没有
   一个已完成局部对应却仅被 boundary 阻塞的案例。非静默 call 或额外控制
   出口会要求不同的 host，但尚不能把假想案例当作已有泛化证据。General
   affine source、紧凑 alias 条件等现有缺口需按其真实原因处理。
6. **Guarantee/requirement 的用途。** 在两个实际 host/site 上验证 entailment
   能否减少义务后，再决定是否提供新接口。`temp_agree_weaken` 可以削弱
   出口观察集，但不能仅凭这个 lemma 就宣布整个 region contract 单调：
   contract 也有入口 agreement 和 source scope，须另证执行运输。输入约束、
   输出保证和 fresh-resource 条件有不同方向。
7. **Finite/open 的共同与不同。** 可以共享条件化的出口关系，必须分别保留
   有限完成和逐步模拟的 progress 语义。Open 的“到达出口时满足 relation”
   不能替代 finite 的“存在完成执行”。Clauses 不是任意笛卡尔积。
8. **其他 IR。** Selected state agreement、memory/trace 与 private-resource
   结构可以启发 SSA/assembly host；phi/live-out、successor/PC、flags/scratch
   和具体 step law 仍须由该语言重新证明。本轮没有这些实例的实现证据。

## 条件处理的具体复用检验

[Readonly probe 后继](word-nested-store-probe-memo.md)消除同一决策路径上已
观察的相同 Clight expression。它只依赖表达式相等判定和固定 readonly
状态上的 Boolean determinacy；不检查 polyhedral schedules，不移动读取，不
跨 mutable scan/body 保存事实。已有 partial expression 语义仍保留。

该服务目前是 **Clight 的、与具体优化器无关的库**，不是另一个语言无关
kernel 或任意语义下的 memoizer。首次使用仍须由原条件证书许可；private
lowering 的 freshness/frame 仍由语言服务证明。精确 Boolean 结果运输允许
沿用原 `C_derive`/`C_opt`，新的 domain factory 生产同类 region guarantee，
语言 host 沿用原 installation theorem。检查次数的计数定理、真实 compiler
接入和实测计数分别提供证据，不把其中一个替代另外两个。

## 后续计划和验收

1. 完成本 readonly probe 服务的实际 compiler、接受/拒绝/context 矩阵与
   setup 工作计数；分别记录代码尺寸，禁止据此声称 CPU 收益。
2. 对已经闭合的 loaded 源族做完整配对成本，覆盖 source、前一 guard 和新
   guard，计入 capture、header/alias scan、候选/回退和公开出口。继续构造
   紧凑充分 entry condition；不能为速度放宽指针定义性或偷读 child/RHS。
3. 用 OLO 2017 的功能和使用方式验收 condition derivation、接受域与作者
   负担。当前 scan/cap 和源族限制有独立差距，验证本身不能解释这些差距。
4. General affine domains/source/scalars 仍在 active goal。扩大覆盖与闭合
   源族的成本/可用性验收并行推进，不无限延后后者。
5. Host clause factoring 是证据驱动的后续研究：比较至少两个现有 host，
   证明有实质的 transport/obligation 复用再修改 API；先保留有限/open
   的语义差异。第二具体 IR 实例不是本轮交付或主实例的前置条件。

本次不重新断言文献新颖性；`conditional equivalence + if` 本身不足以支撑
贡献。论文需要证实条件服务/语言安装的实际复用和完整 CompCert 案例的
能力、成本与使用体验。
