# 当前工作计划：评审吸收后的验收顺序

2026-10-06 更新。主目标仍是顺序 CompCert 中可运行的 verified guarded polyhedral transformation，PolCert 是功能与证明能力参照；片段选择和候选由用户提供，框架处理条件证据、局部 reasoning 和完整程序安装。完整目标没有因阶段结果而完成。

本计划吸收 [三个分支的评审](review-synthesis-2026-10-05.md)。既有研究路线保留在 [contribution-plan.md](contribution-plan.md)，当前执行优先级以下表为准。

活动目标补充（用户 2026-10-05）：持续按 `topdown/research-positioning` 的 [paper narrative](topdown/paper-narrative.md) 改进整体定位；以“小的语言无关框架＋实质 CompCert 循环实例”组织研究，明确框架、语言实例、优化／domain 实现者的验证责任。具体约束与最难验收见 [责任矩阵](framework-responsibilities.md)。这项补充与原完整实现目标同时有效，每个阶段检查，不将方向文档算作功能完成。

10 月 6 日阶段同步吸收 `f793629` 的 cross-IR 补充：保持核心不依赖 Clight 语法；SSA／汇编使用者须实例化自己的控制、live-out／phi、scratch／flags 定律。它们是接口讨论和同例 related-work 比较的方向，第二 IR 实现是可选证据，当前主实现／验收继续是 CompCert/Clight。

| 顺序 | 工作与状态 | 必须交付的验收 |
| --- | --- | --- |
| P0：本次交付 | 实现、实际 frontend 对应、提取与回归已通过；提交／push 以阶段记录为准 | 一个真正完整的 unsigned memory-bound 循环；guard 域来自有限源前缀；源／目标实际 alias 发散；540 次有限调用、六处新 loop 与两处混合旧 preload；401 端点／862 摘要、25 配置／40 报告绑定当前产物，39 份旧 C／Clight 摘要保持；准确文档并 push |
| P1：统一实际 realization | [公共设施](clight-guard-realization.md)与三个实际路径已接入；411 端点／863 摘要、25 配置／40 报告验证通过，相对 `26956a4` 的 40 份 C／Clight 摘要保持 | direct/shared 复用同一个 readonly condition 与 local rule，公共证书说明实际代码、私有资源／freshness、状态／观察运输、defined dispatch 和相应宿主模拟；两个 finite 安装路径和完整 unsigned 循环消费同一设施。分派前缀不要求分支完成；shared whole-loop 尚未安装，finite host 仍要求 source progress |
| P2：主多面体路线迁移 | [named rectangle 使用者](clight-polyhedral-preservation.md) 的证明、提取、40＋8 原生配置已通过；第二项 [参数化 affine 内层源／多类数组 body](clight-parametric-preservation.md) 通过 12 个证明端点、六份完整 C fixture／134 个原生配置，以及四个实际接受／回退顺序探针；主接口 415 端点／864 摘要保持；第三项实际参数化 pointer scan 已接入一般公共证书、kernel 保持、Csem→Asm 和提取，38 端点／15 个原生配置／四个执行顺序探针通过，另有 222 组完整上下文输入／三配置通过 | 不受信任的实际候选、源／候选对应、机器范围／alias 检查、private 观察、Csem→Asm 与提取接受／拒绝均通过公共接口；记录旧证书复用和专属义务。此次第二项仍不包含一般深度 affine polyhedron、指针切片或 stateful 足迹；单个新 helper 或脱离编译器的模型不计完成 |
| P3：一个符号化条件／足迹算法 | [盒状 affine 包络](affine-box-condition-derivation.md) 与实际宽度使用者通过 29 端点、完整证明／提取、134 配置和十个顺序探针，[证据](research-checkpoint-2026-10-06-envelope.md)。footprint 枚举替代仍待证 | 固定受限 affine 表达／域和允许观察；输出条件和可核对证书；证明实际源实例覆盖、Boolean／机器表示、安全与接受蕴含语义前提；实际编译一个候选，给出拒绝策略和非空接受域。不把逻辑 projection 定理描述成已有 QE 实现 |
| P4：机制性能与复用量化 | [测量方案](native-performance-plan.md)和[schema](native-performance-report.schema.json)已采纳，尚未测量 | 同版原 CompCert 对照，实际接受／回退／静态拒绝分开；tree/simplified 的同源对照；最终 kernel bytes、guard／完整运行成本、编译成本、原始批次和环境。测量期间没有并发证明／构建；负收益照实报告 |
| 持续：已有工作／主张校准 | 保留 [cf4d442 证据矩阵](evidence-to-claim-2026-10-05.md)；新增 [Chamois／Peek 一手接口补核](related-work-interface-check-2026-10-06.md)，阶段性读取新评审 | Chamois oracle 签名和 CFG 扩展证明已取得，不再保留这两个访问未知项；动态条件推导能力和同例作者负担仍需核对。比较 OLO、Chamois、Peek 的安全、覆盖、freshness 和宿主义务；不以端点数、C 层或 abstract if 单独主张 novelty |
| 持续：论文方向与验证责任 | 目标的组成部分，沿 topdown narrative 更新 | 每个阶段区分框架证明、语言定律和 optimizer／domain 证书；分别落实 `C_opt`、`C_derive`、`C_guard`、`C_host`。重点验收 B 覆盖全部 A、guard 自身安全、实际模型对应、有限／无限宿主行为及证明复用，不以责任表代替这些证明 |

P0 关闭的是一个明确语义缺口。P1 服务于 P2 的真正接入；P2 是主功能目标的一次迁移验收，之后仍需一般 affine 域、复杂读写 body、依赖 preload 和布局组合。P3 是 optimizer/domain library 的受限推导算法，核心不承担 universal assumption extraction。P2 的首个使用者已实际消费候选／依赖核对和条件正确性；新的保持接口沿用旧证书在实际 globalenv 上的方向，与双向规则共享安装证明，没有改称等价或只重做 guard 包装。后续优先迁移参数化源／访问及真实 pointer footprint；区分可直接复用的 readonly 证书和需要私有检查状态的路线。P3 必须说明 `B⇒A` 的入口推导，再交给 `guard accepts⇒B` 的编码与 host。P3 与 P4 用来检验算法和实际价值，不将测量结果预设为收益。新增 [paper narrative](topdown/paper-narrative.md) 已在 P0 后同步读取并吸收。

P2 第二项已经复用 `encoded_private_rule`，接入参数化 readonly 使用者、实际 schedule generation／rechecking 与不同数组 body。第三项 [private-scan compiler](clight-private-check-migration.md) 将真实参数化 pointer footprint 接入一般公共 host 和 guard／preservation 证书：覆盖归纳检查安全、实际检查后状态、result 初始化、原入口 P、全部完成检查 sound、任意完成分支的 exact dispatch、分支运输及 kernel 消费。scope、private pool、source progress 和完整 CompCert 安装均沿用已证明的语言设施。38 端点、465 项实际依赖、812 份摘要；15 个原生配置各覆盖同一组 637 次调用，另有四个实际 disjoint 接受／alias 回退的汇编顺序探针。完整研究目标仍未完成。

参数化 readonly 结果见 [阶段记录](research-checkpoint-2026-10-06-parametric.md)，private-scan 的前一事实阶段见 [历史记录](research-checkpoint-2026-10-06-private-scan.md)，公共 pointer compiler 的证据见 [新阶段记录](research-checkpoint-2026-10-06-private-scan-compiler.md)。当前 pointer 源是稳定寄存器矩形 bounds 下的参数化仿射访问，不与 `j<U(i,parameters)` 非矩形源混称；source-derived D、footprint coverage 与范围理论仍复用既有 domain 证明，没有新增一般 projection 算法。

下一项进入 P3：选定一个受限 affine 范围／足迹的符号化条件推导，明确允许观察和保守拒绝策略，输出可核对条件证书，并让实际候选消费。重点是 B 对全部局部 A 的覆盖、机器求值安全和非空接受域；不将原有枚举扫描或纯 implication 字段改称算法完成。P4 仍需同版原 CompCert 对照、实际 guard／运行成本，以及与已有接口的同例证明负担比较。一般深度 affine pointer 域和多个依赖 preload 继续作为功能差距维护。

P3 的 pointer 快捷检查计划已据实际语义修正：`p+k` 是合法源访问，不蕴含原始 `p` 是 weak-valid pointer。CompCert 对指针比较的定义性要求因此不能仅由当前访问足迹推出；“先比较 base，再按 offset 包络判分离”不能直接插入普通循环。只有源前缀或合法 placement 证书提供比较所需的实际地址有效性时才可接入，不将它偷偷加进 source-derived D。当前实现切口改为通用盒状 affine 包络及有符号参数范围编码，先替换参数化 readonly 源的宽度检查，让真实候选消费所有迭代点的覆盖证明；pointer scan 保留，尚未取得可替换它的安全符号化 alias 快捷检查。旧宽度检查本来也是一轴符号化 endpoint 检查，替换它不等于已消除 footprint 枚举或实现一般 projection。

## 每个阶段固定记录什么

1. 输入／候选／condition 的实际定义和选择器支持域；selector cap 与局部定理范围分别列出。
2. D 从哪里获得，P 在哪里建立，哪些后续访问需要已接受事实；不得在 D 偷放 P。
3. 局部有限等价或小步协议、公开出口／frame、宿主覆盖的发散和控制出口。
4. 完整程序端点、继承假设、源码／报告／编译器 stamp；native 回归与形式证明各自的边界。
5. 同一 source／D／P／candidate 下复用了什么，专属 obligations 和 proof code 有多少；新增模板不自动计作独立贡献。
6. 未完成项、评审意见处理状态、commit 与远端 push。原评审保存固定 SHA，新状态另记，不把历史判断默默改成当前事实。
7. 三方责任与难点：框架新增服务、语言实例新定律、优化方专属 proof／checker 各是什么；最难义务实际如何关闭，哪些仍由调用者承担。更新 [责任矩阵](framework-responsibilities.md) 和研究定位。

接口原则保持不变：现有 `select_exact` 与只读前台是固定核心；语言实例解释语义、观察、安全和控制，使用者决定寻找片段、rewrite 提案、遍历、优先级与资源预算。框架不能只要求一份任意等价定理，而要通过实际复用的检查、frame、表示和上下文设施降低规则作者工作。

## 阶段性读取评审

完成 P0、冻结 P1 接口、完成 P2 迁移，以及取得第一批 P4 样本时，重新同步评审分支，记录新增 SHA 和相对上次读取的变化。每条新增意见更新“采纳／已解决／仍待证／未采纳理由”及对应验收，不仅追加阅读链接。正文中历史能力按其固定提交解释，当前主张依最新实际产物更新；不因评审分支比 main 旧就整体忽略意见，也不把已被后续证明关闭的缺口继续列为当前缺口。
