# Narrative 复核：条件处理、证明责任与当前实施边界

2026-10-10 重新 fetch `topdown/research-positioning`，并用 `ls-remote --heads`
核对远端，当前可见提交仍为
`8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9`。
[paper-narrative.md](topdown/paper-narrative.md) 与 main 正文一致。
本次是结合当前实现重读已可见的澄清，不声称取得另一份新提交。

本页保留复核时的 proof／测量状态。此后的
[residual 交付](double-tree-residual.md)已闭合 Loop、factory 和 compiler，
[组合路线对照](double-tree-combined-residual.md)已完成 192 项，并记录实际中间
Clight 的顺序证明组合。下文的“尚未编译”和约 1.837 比值是前序状态；当前
责任边界与 OLO 单独验收要求仍适用。

## 固定的责任边界

| 层次 | 应交付的证明 | 不能由这个层次的接口本身代替的工作 |
| --- | --- | --- |
| 最小 framework kernel | 从 guard、conditional correctness、accepted/refused entry 证书推出局部 guarded refinement 或 preservation | 前提发现、机器读取许可、具体上下文闭包 |
| 可复用条件库 | Boolean/dependent composition、充分条件加强、在已认证事实下简化；各服务记录调用前提与接受事实 | 任意程序对的 weakest condition；优化器特有的义务推导 |
| 语言／IR host | 实际 check/choice 执行、安全读取与算术、private/public frame、控制与 progress、合法 site 安装及 backend 衔接 | 判断某个 schedule、footprint 或 alias 假设是否足以保证变换正确 |
| 优化／domain 实现者 | 实际 source/model 对应、候选正确性、局部义务到充分入口条件的推导、适用 region guarantee | 用抽象 host 字段或运行输出代替实际 lowering／当前程序证明 |

[GuardInterface.v](../prototype/interface/GuardInterface.v) 的
`guardify_refinement` 和 `guardify_preservation` 分别证明对应方向。
`context_certificate.lift_refinement` 是 host 提供的证明，不是 kernel 从任意
局部关系自动生成的上下文定理。[Context lifting](topdown/context-lifting.md)
的 contract clauses／guarantee-requirement 设计仍是待实际 blocker 检验的提案。

新增语言／优化族的作者需要交付适用证明；已支持族的 C 使用者提交标注源码和
策略数据。`C_opt`、`C_derive`、`C_guard`、`C_host` 描述证据来源，不要求每个
rewrite site 的使用者手填四个语义 record。Factory 和 site check 必须生产、
组合并 discharge 适用的动态与全程序前提。

## 当前条件简化能做什么

[已交付的 body pruning](double-tree-pruned.md)先验证 affine reference，再证明
裁去 quiet suffix，并由实际 machine lowering、factory 和当前程序 compiler
消费。它减少候选的无效迭代，没有新增入口条件推导算法。

正在实现的 residualization 从 loop bounds、已进入的 branch 和参数 intervals
取得事实，用这些事实消去候选体内恒真的 membership tests，再合并适用的相邻
guards。这条服务按以下责任验收：

1. 通用 residualization 定理要求已知原子有证据，在 invariant 下保持 formula
   的语义性质。它属于最小 kernel 之上的可复用库。
2. Loop/domain 实例负责 binder 下的事实运输、区间推理、Boolean 求值对应及
   实际 statement 执行保持。当前 Loop predicates 在数学环境中求值；不能把
   这个结果直接推广为任意带读取或拒绝行为的 runtime check 等价。
3. Clight lowering 仍须证明实际机器求值安全、private/public frame 与公开出口。
   新 factory 和当前程序 Csem→Asm 端点必须消费改过的实际候选。

[ResidualGuard.v](../theories/ResidualGuard.v) 的本地后继 `ResidualGuardCurrent.v`
是逐字节副本，重编译以适配当前依赖；它没有增加条件表达力。
该 generic library 后继已编译成功，但 Loop 实例的第二次编译在
`test_formula_property` 的 iff 方向上失败，日志和源快照已保存。新 residual
candidate／factory／compiler 尚未编译，不能记为已安装能力或性能结果。

## OLO 条件推导单独验收

消除候选内部冗余检查，与 OLO 的入口条件构造是两项不同的交付。后者需要把
所有实际到达点的局部义务 `A` 推成可检查的充分入口条件 `B`，再证明安全执行的
`G` 接受推出 `B`，并运输接受和拒绝后的入口状态。

`B -> A` 可以来自已验证的 projection、range／footprint 服务，或经过已验证
checker 的不受信任充分条件提案。Arithmetic representation、address validity、
alias/stability 与 dependent reads 的证明要接在数学推导两侧。某个 guard 更强、
接受域更小是允许的，但必须记录有用输入的接受情况与实际成本。

已有服务仍按 [verified guard library](verified-guard-library.md) 的五类组织：
算术与表示、范围与 footprint、内存分离、值与观察保持、控制与条件观察。
组合契约要区分 requires、accepted facts、reads/private writes、public frame
和 refusal transport。稳定性不许可首次读取；拒绝也不证明前提为假。

## 对后续实施的约束

先关闭当前同源测量暴露的冗余 membership 成本：完成事实与执行证明，接入实际
lowering 和当前程序 compiler，再与原 source 及前序 pruned 实现比较完整成本。
保留当前约 1.837 的 full-domain pruned/source 比值作为前序结果；本次复核没有
新计时，也不把消除检查当成已经获得 speedup。

继续处理 general piece／ISS 的 forward/progress、真实 tiling／域变换以及紧凑
入口条件、重复检查消除。每个扩展同时交付 whole-program 接入。PolCert 62 例的
顺序配置、CGO17 原计算与上下文及较大 input tiers 继续是验收目标；诊断、identity、
safe refusal 或简化计算不能替代相应功能支持。

Source Clight → source Loop → candidate Loop → 实际 Clight 的每个桥要写明方向、
适用范围和前提来源。Static checks、runtime accepted facts、证明中的原 source
execution 分开记录。重复 rewrite 消费当前 intermediate program 的 site 证据，
再组合有限序列。原 source execution 是证明起点，不是 runtime 先运行 source。

本次只吸收和细化验收约束，未扩大实现／论文能力声明。长期 goal 保持 active。
