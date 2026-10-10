# 参数特化与常量参数事实的精度

本阶段按 [narrative](topdown/paper-narrative.md) 的责任边界处理整体候选的
floor-bound 适配障碍。2026-10-10 重新 fetch 后，远端可见提交为 `8ce9c8b`，
正文与 main 相同。Kernel、语言 host 定律和动态 loaded-bound 契约不变。

## 可复用数学服务

[PolCertParameterSpecialization](../theories/PolCertParameterSpecialization.v) 以
已建立的参数 intervals 为输入，只有两端相等才把相应变量替换为常量。它递归
处理 Loop 的 Sum、Mult、Div、Mod、Min、Max；每进入一个 loop binder 都在事实
表前加入 unknown，防止把迭代变量误认成参数。Tests 保留原 LE/EQ/Boolean
语法，以满足后续 affine extraction 的表达范围。

接口要求 `facts_hold facts env`。`singleton_facts_hold` 从实际区间覆盖推出此
要求；`expression_correct`、`test_correct` 保持数学求值；`statement_correct`
建立有限正常 Loop 执行 iff，前后 memory 相同。这些定理不提供机器运算的
安全性、首次读取许可或任意程序前提发现。

[原生适配后继](../adapters/compcert-memory/native/GuardSelectedDoubleTreeSpecializedBounds.ml)
在编译器中调用提取的函数，并分别保留 original/specialized codegen receipts，再进入原
source-aware adapter。实际候选仍由 final affine/dependence/tiling checker
授权。数学服务的 correctness 与 compiler 正确性的信任边界要分开：现有
compiler 接受不受信任的 adapter；新服务没有取代该 checker。

例如 facts 对应 `[100,4]` 时，参数表达式 `32 * floor(100/32)` 被化为
`96`；进入两个循环后，facts 成为 `[unknown,unknown,100,4]`，两个新迭代变量
仍保留。它在编译时处理已知数学 facts，不是在目标程序中发射一个新的 runtime
check。动态参数的未知值不会被替换。

## 为什么常量输入仍可能无法特化

第一次 native 接线在 `fusion10`、`fusion2`、`nodep` 上完整输出匹配，但收到的
全部 intervals 都不是 singleton。原 `double_tree_parameter_intervals` 使用
`[min(0,lower),max(0,upper)]`，容纳条件 capture 尚未到达的 loaded 参数所保持
的初始零值。常量 source 路线复用此服务，使 `100` 被描述成 `[0,100]`。

常量参数的 private cache code 会无条件初始化所有参数，因此可以使用更精确
的 `[100,100]`。新的
[execution 后继](../adapters/compcert-memory/GuardMemoryExactLiteralDoubleTreeExecution.v)
证明 exact interval 覆盖实际已初始化的参数，再用于同一 candidate 检查和
source Loop 到 candidate Loop 的执行证明。它继续复用实际 Clight 常量编码、
source/model 对应、machine lowering、private frame 和公开出口恢复。

[新 factory](../prototype/interface/ExactLiteralDoubleTreeFactory.v) 将 exact
intervals 传给实际 pipeline；[完整程序入口](../prototype/interface/ExactLiteralCombinedDoubleCompiler.v)
先安装常量路径，再让旧组合 passes 消费实际变换后的程序，接 Csem 到 Asm 的
backward simulation。动态 loaded source 的 intervals 与 conditional capture
规则保持原契约。C 源使用者提交标注源码和策略，不补语义 callbacks。

## 验证责任

| 层次 | 本阶段交付 |
| --- | --- |
| 最小 kernel | 复用局部 guarded correctness 和证书组合 |
| Domain 库／优化实例 | singleton facts、数学特化、实际候选最终验证与 exact 参数事实的消费 |
| Language／host | 复用无条件常量 cache 的实际值、source/model、safe lowering、frame/control/progress 与 current-program 安装 |
| 普通 C 使用者 | 输入标注源码与 phase 配置 |

本阶段是静态事实精度与 candidate adaptation 的改进。OLO 的 local obligations
到 compact entry condition、safe machine guard 与 accepted/refused state
transport，以及实际优化效果和完整成本继续分别验收。

## 适配顺序也是候选契约的一部分

第一次 exact-interval native 接线在 `fusion2` 解除整体 tiled adaptation 拒绝，
但在 `fusion10` 暴露实际 transformation 回退：先特化再运行旧 singleton 清理，
使 size-32 tile 的 `[0,1)` binder 消失；现有 final checker 的 witness 仍要求
这些坐标。完整输出匹配并不意味着目标变换被保留。

[坐标保留后继](../adapters/compcert-memory/native/GuardSelectedDoubleTreeSpecializedCoordinates.ml)
先对原 raw Loop 做既有 singleton 清理，再执行已证明的参数特化，保留新变为
singleton 的 tile binders，然后恢复 point 坐标、适配 bounds。它仍是同一个
完整程序 theorem 的不受信任 adapter 参数；最终验证和 machine lowering 没有
被绕过。这个顺序改动不要求新增 kernel、host law 或 C 使用者证明。

整体 `fusion2` 的 source 有两个 instructions，candidate extraction 有七个
pieces。现有 `double_attach_tiling_instructions` 的定义按 source、candidate、
witness 三个列表一一连接，仅同时为空才成功；normalization/reindex/shift 都
是保留长度的 map。因此该候选不能通过现有 positional attachment。此结论
来自已绑定源定义和 extraction receipts，不是另外的 runtime final-check
trace。要接受它，domain 需要新的分片覆盖、互斥、执行对应和次序证明，以及
相应 progress；语言 host 的安装证明继续复用。

## 验证结果和继续开放的范围

[数学服务审计](parameter-specialization.json)：两模块140行／四端点，三closed、
最多四既有globals。[完整安装审计](exact-literal-parameters.json)：四模块453行／
十端点，一closed、最多42既有globals。均无新增globals，失败proof snapshots
与成功来源绑定；行数包含重复接线，不是作者负担收益。

[完整结果摘要](exact-literal-parameter-results.json)绑定73,106项inputs，包括
三次native构建、三个重点replays、两个exact构建的完整192配置replays及前序。
最终186个完整输出匹配：原例180/186、两disclosed adaptations6/6。六个既有
frontend拒绝保持，没有compiler timeout、native mismatch或link failure；所有
input hashes与status对照保持。前序宽区间无特化、首个exact构建的tile坐标丢失
和最终恢复均保留。

重点最终Clight的tiled conditions为 fusion10／fusion2／nodep 的12／16／13，
前序28／22／17；fusion10／fusion2各两个四层nests，nodep一个四层nest。这些
条件包含控制与出口，不是OLO entry checks；只有candidate内部简化证据，未做
新的未改assembly观察、动态guard拒绝或controlled runtime cost比较。

整体fusion2仍受两源／七piece的positional契约阻挡，fusion10整体仍有iterator
floor/Mod适配拒绝。[下一piece接口](polyhedral-piece-contract.md)明确待交付的数据、
覆盖／唯一性／动作／次序／progress证书及已有基础复用。Kernel与host保持原边界。
OLO compact entry推导、safe checks/state transport、原contexts/tiers和完整成本
继续在active goal中。
