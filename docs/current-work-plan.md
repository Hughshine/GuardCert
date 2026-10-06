# 当前工作计划：评审吸收后的验收顺序

2026-10-05 更新。主目标仍是顺序 CompCert 中可运行的 verified guarded polyhedral transformation，PolCert 是功能与证明能力参照；片段选择和候选由用户提供，框架处理条件证据、局部 reasoning 和完整程序安装。完整目标没有因阶段结果而完成。

本计划吸收 [三个分支的评审](review-synthesis-2026-10-05.md)。既有研究路线保留在 [contribution-plan.md](contribution-plan.md)，当前执行优先级以下表为准。

| 顺序 | 工作与状态 | 必须交付的验收 |
| --- | --- | --- |
| P0：本次交付 | 整段小步宿主、真实无限回退、Csem→Asm 已编译；实际 frontend 对应、提取和全套回归正在完成 | 一个真正完整的 unsigned memory-bound 循环；guard 域来自有限源前缀；源／目标实际 alias 发散；有限接受／空域／wrap／当前入口／混合 pass 的原生检查；新旧配置绑定同一审计；准确文档并 push |
| P1：统一实际 realization | 下一项架构任务，不另造 abstract select | direct/shared 复用同一个 readonly condition 与 local rule，公共证书说明实际代码、私有资源／freshness、状态／观察运输、defined dispatch 和相应宿主模拟；迁移至少两个当前实例并回归。新 open host 的能力差异显式记录，不能只填空 record |
| P2：主多面体路线迁移 | 在 P1 接口下选择一个真实旧 affine／tiling 使用者 | 不受信任的实际候选、源／候选对应、no-overflow／alias 检查、private 观察、Csem→Asm 与提取接受／拒绝均通过主接口；记录哪些旧证书可复用、哪些要新证。单个新 helper 或脱离编译器的模型不计完成 |
| P3：一个符号化条件／足迹算法 | 优先替换一个枚举路径，不继续堆同类模板 | 固定受限 affine 表达／域和允许观察；输出条件和可核对证书；证明实际源实例覆盖、Boolean／机器表示、安全与接受蕴含语义前提；实际编译一个候选，给出拒绝策略和非空接受域。不把逻辑 projection 定理描述成已有 QE 实现 |
| P4：机制性能与复用量化 | [测量方案](native-performance-plan.md)和[schema](native-performance-report.schema.json)已采纳，尚未测量 | 同版原 CompCert 对照，实际接受／回退／静态拒绝分开；tree/simplified 的同源对照；最终 kernel bytes、guard／完整运行成本、编译成本、原始批次和环境。测量期间没有并发证明／构建；负收益照实报告 |
| 持续：已有工作／主张校准 | 固定 [cf4d442 证据矩阵](evidence-to-claim-2026-10-05.md)，阶段性读取新评审 | 同例对照 OLO 源访问域／依赖 preload、安全检查与实际宿主义务；直接核对 Chamois／Peek 接口未知部分；记录复用与作者证明负担。不以端点数、C 层或 abstract if 单独主张 novelty |

P0 关闭的是一个明确语义缺口。P1 服务于 P2 的真正接入；P2 是主功能目标的一次迁移验收，之后仍需一般 affine 域、复杂读写 body、依赖 preload 和布局组合。P3 与 P4 用来检验算法和实际价值，不将测量结果预设为收益。

## 每个阶段固定记录什么

1. 输入／候选／condition 的实际定义和选择器支持域；selector cap 与局部定理范围分别列出。
2. D 从哪里获得，P 在哪里建立，哪些后续访问需要已接受事实；不得在 D 偷放 P。
3. 局部有限等价或小步协议、公开出口／frame、宿主覆盖的发散和控制出口。
4. 完整程序端点、继承假设、源码／报告／编译器 stamp；native 回归与形式证明各自的边界。
5. 同一 source／D／P／candidate 下复用了什么，专属 obligations 和 proof code 有多少；新增模板不自动计作独立贡献。
6. 未完成项、评审意见处理状态、commit 与远端 push。原评审保存固定 SHA，新状态另记，不把历史判断默默改成当前事实。

接口原则保持不变：现有 `select_exact` 与只读前台是固定核心；语言实例解释语义、观察、安全和控制，使用者决定寻找片段、rewrite 提案、遍历、优先级与资源预算。框架不能只要求一份任意等价定理，而要通过实际复用的检查、frame、表示和上下文设施降低规则作者工作。

## 阶段性读取评审

完成 P0、冻结 P1 接口、完成 P2 迁移，以及取得第一批 P4 样本时，重新同步评审分支，记录新增 SHA 和相对上次读取的变化。每条新增意见更新“采纳／已解决／仍待证／未采纳理由”及对应验收，不仅追加阅读链接。正文中历史能力按其固定提交解释，当前主张依最新实际产物更新；不因评审分支比 main 旧就整体忽略意见，也不把已被后续证明关闭的缺口继续列为当前缺口。
