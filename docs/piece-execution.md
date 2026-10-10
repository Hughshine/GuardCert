# 已检查的一源多片：模型执行接口

本页继续落实 [narrative](topdown/paper-narrative.md) 的责任划分。它补上
[piece 接口设计](polyhedral-piece-contract.md)中的完整 point isomorphism 和模型
执行组合，并连接实际候选 Loop 的有限执行。独立 Clight progress 和整体 fusion
安装继续开放。

## 谁提交什么

普通 C 使用者仍提交标注源码和优化策略。优化实现者／adapter 提交模型及数据
提案；以下数据不是用户需要填写的语义公理：

| 输入 | 含义与检查 |
| --- | --- |
| 实际 source 和 candidate polyhedral models | 来自已检查 phase 和真实 Loop 提取；保留 typed instructions、accesses、domains、arguments 和 schedules |
| 参数约束 `guards` | 已建立的入口模型事实，以有限整数仿射不等式表达；按 instruction 深度补零 |
| 每个 source instruction 的 piece group | 每项包含 candidate instruction 与 domain、embed、project；组长度可不同，piece 深度可不同 |
| 每组有限 coverage tree | 不受信任的 inclusion／split／empty 提案；检查覆盖、互斥和双向坐标恢复 |

[总检查器](../adapters/compcert-memory/GuardMemoryDoublePieceModel.v)
`check_double_piece_model guards source candidate groups witnesses`返回可报警的
布尔结果。Alarm 或拒绝不提供 accepted certificate。它先检查 source／candidate
参数数量，加入参数域约束，检查各 group，再对 retimed groups 与实际 candidate
运行已有依赖 validator。Typed instruction／arguments、参数前缀、候选域绑定
和 identity point-witness 形状也由检查器确认。

此实现的分组保持静态 instruction 列表按 source ordinal 拼接。运行时的执行
可以交错：实际 candidate schedule 的改变由依赖验证承担。接口目前没有声称
支持任意静态 group permutation，也不通过具体 iteration trace 枚举证明覆盖。

## 库生成什么证明

[Single execution](../theories/PolCertPieceSingleExecution.v)从接受的单组检查结果
构造完整 `memory_point_isomorphism`：双向有效点、两方向逆、timestamp 与逐动作
执行保持。Source-to-piece 使用有限 image 选择器；piece-to-source 使用 embed。
Piece domain 必须等于所检查 candidate instruction 的实际 domain。

[Ordinal append](../theories/PolCertPointSequenceAppend.v)证明静态列表拼接时的
ordinal 平移、恢复以及完整 point isomorphism 组合。它不要求前一组的动态动作
全部先于后一组。

[Sequence execution](../theories/PolCertPieceSequenceExecution.v)检查 source、groups
和 witnesses 的对应长度，从各组证书组合多 instruction 的完整对应，得到实际
polyhedral instance-list 执行 iff。Retiming 保持源 timestamp；实际重排继续独立
由依赖 validator 证明。

总定理 `checked_double_piece_model_equivalence_at`组合参数域 restriction、上述
对应和实际次序验证。在相同初末内存下，它给出：

```
accepted check + established parameter facts + applicable NonAlias
  => source model execution <=> actual candidate model execution
```

适用前提还包括参数向量与 source context 等长、参数约束的系数宽度不超过参数
维度。这些前提的来源必须具体交付，而不是转成 C 使用者的 semantic callbacks。
双向模型定理的语义端点是真实 double instruction 的读写与 IEEE 运算；它没有
自动建立候选 Loop progress 或全部机器中间运算的安全性。

[Actual Loop bridge](../adapters/compcert-memory/GuardMemoryDoublePieceLoops.v)
复用既有实际 extractor 的双向执行定理。第一个端点建立 checked model 与
实际候选 Loop 有限执行的 iff；第二个端点连接实际 source Loop、retained
checked phase、piece model 与 actual candidate Loop，得到 source-to-candidate
有限执行保持。它不重新发明 extractor，不从 raw-codegen backward 定理推断
forward，也不把有限执行保持称为独立 Clight progress。整体 phase 的反向证明
仍须在同一 captured parameters 上连接，才能给出 actual source/candidate Loop
的完整 iff。

## 与条件框架、语言和完整程序的分工

这个库提供模型层 `C_opt`，消费适用事实 A；它不从任意程序对推断 A，也不生产
safe machine guard。参数约束只是条件表达能力的一部分。若这些事实需动态获得，
优化／条件库仍应证明 `B => A`，语言条件服务应证明 safe `G accepts => B` 与
accepted/refused entry transport。已有 alias、范围及 source-read 许可服务分别
交付相应维度，不能由数学坐标对应替代。

静态 checker 负责语法、形状和资源事实。Source execution 是源到目标正确性
证明的起点，不是选择版本前运行原循环。语言实例仍负责 actual guard/if、实际
Clight 与 Loop 语义桥、frame/control、progress、合法 site 和 backend；kernel
消费最终证书，证明局部 guarded correctness。多次改写继续复用已有当前程序
site 证据与有限序列组合定理。

## 当前验证与下一验收

[独立审计](piece-execution.json)覆盖五模块642行／八端点，无新增 globals，
每端点最多十二项既有 globals；25次编译保留20次失败。行数包括实例化与接线，
不作为作者负担减少的度量。历史动作／参数审计与诊断继续保留原 scope。

Actual Loop 的[独立审计](piece-loop-bridge.json)覆盖59行／两端点、最多十二项
既有 globals、无新增，一次编译通过。它在模型定理之上复用语言已有执行桥。

[原 fusion2 的运行结果](piece-execution-results.json)绑定实际输入、phase、
六／七片候选及完整提取检查器。两个总模型检查通过，两配置各拒绝遗漏分片、
重复分片、改坏实际 instruction、逆转实际依赖顺序，合计八次拒绝。三配置完整
输出匹配，selected Clight 与前序相同，仍是两个单独 nests。Native 诊断检查
models；编译过的语言桥连接其 accepted 证据到有限 Loop 执行，旧 final checker
仍授权完整程序安装。它不是新安装路径，也没有 controlled cost 结果。

下一验收要让新 factory 消费 untrusted piece groups／coverage 数据和实际
检查结果，接上同一参数下 phase 的反向执行、独立 Clight progress、machine
lowering、公开出口与当前程序安装。必须观察整体 fusion 候选通过并安装；模型
iff、完整输出匹配或两个 nests 的分别分块都不能代替这个验收。OLO compact
entry 推导、安全检查、状态传递、原 contexts／tiers／完整成本和其他 PolCert
顺序能力继续独立验收。
