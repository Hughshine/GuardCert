# 分片动作、参数条件与执行连接

本页落实 [narrative](topdown/paper-narrative.md) 的责任划分，并继续处理原
`fusion2` 的整体候选。已完成的 [域服务](piece-domain-services.md)给出有效点的
覆盖、互斥和坐标恢复。本次增加动作、参数及 retained phase 的执行证明；完整
候选的 Loop 桥和安装仍在推进。输出匹配与候选检查不能代替安装验收。

## 证明链与责任

最小 kernel 仍消费条件正确性、guard 和 accepted/refused entry 证书，证明局部
guarded correctness。Piece 服务属于 optimizer/domain 层，消费适用的模型事实。
语言实例继续证明安全机器求值、读取许可、private/public frame、控制、progress、
合法 site 与 backend。已支持族的 C 使用者提交标注源码和策略数据，不填写语义
callbacks。

条件正确性内部的方向继续明确分开：实际源 Clight → 源 Loop → checked phase
model → 实际候选 Loop → lowered Clight 与公开出口。静态 checker 提供语法、
形状和资源事实；runtime guard、capture 和 entry transport 提供动态模型事实；
源执行是证明起点，不是运行时先执行原循环。不存在“每个 theorem premise
必须生成一个 runtime test”的要求。

## 当前已证明的服务

[动作检查](../theories/PolCertPieceActions.v)消费实际 source instruction、candidate
instruction 和坐标提案。它检查 identity point witness、完整 typed instruction、
source/candidate 维度、参数前缀与仿射 arguments。接受后，相应点执行具有相同
的实际 instruction 语义、内存初末状态及读写位置；匹配数组名不够。

它还产生 retimed instruction：保留 candidate 的域、动作和 accesses，把 schedule
替换为 source schedule 与 embed 的复合。时间戳对应有证明。Retiming 的表示
正确性与 retimed model 到实际 candidate 的重排正确性是两个步骤；后者仍由已有
依赖 validator 承担。

[有限选择器](../theories/PolCertPieceSelection.v)通过 piece image 域查找唯一
分片，证明有效源点能被选择、有效候选能恢复原 piece id。它操作符号整数点，
不用具体 iteration trace 枚举。

[Retained phase](../adapters/compcert-memory/GuardMemoryDoubleRetainedPhase.v)
保留真实 scheduler/tile 输出和 witnesses，检查 affine 和 tiling 的所需方向，
得到源 polyhedral instance-list 执行到返回的 current-view tiled model 的 forward
定理。已有 raw-codegen backward 定理单独保留。Forward 结果的语义端点是
polyhedral instance-list，尚不是实际多 piece candidate Loop。

[参数域服务](../theories/PolCertPieceParameterDomains.v)证明：给定已成立的参数
事实，把它们加入每条 instruction 的域，保持当前参数下的实际 polyhedral
instance-list 执行。它构造 identity point isomorphism；参数条件作用于前缀，
按各语句深度补零。这个证明连接有条件的域检查与原模型，不生产机器 guard，
也不从任意程序对提取 assumptions。

动作、选择和 phase 的[审计](piece-actions.json)覆盖四模块348行／十端点，
两 closed、最多十二项既有 globals、无新增；八次编译保留四次失败。
参数域的[独立审计](piece-parameter-domains.json)覆盖两模块103行／六端点，
四 closed、最多四项既有 globals、无新增；五次编译保留三次失败。
这些行数包括接线，不度量作者负担减少。

## 真实候选检查与未完成的连接

[原 fusion2 结果](piece-action-results.json)绑定 unchanged input、实际 source /
candidate 提取、phase 输出及各 piece 的 domain、embed/project、arguments 和
actual/retimed/source schedules。Untiled 六 pieces、tiled 七 pieces 的13项动作与
参数检查通过，两个 retained phase 检查和两次 retimed-to-actual 依赖验证通过。
两配置各拒绝错误 instruction、错误 argument、改坏 parameter prefix 和逆转
依赖顺序，合计八项拒绝。

完整 unmarked、untiled、tiled 输出均匹配原 GCC reference；selected Clight
与前序相同，仍保留两个分别优化的 nests。新的检查在不受信任 adapter 中诊断，
旧 final checker 仍决定安装。参数域执行定理已证明，但尚未被新的多 piece
安装路径消费。Summary 首次因 receipt 字段名错误拒绝，原 script 和拒绝记录
保留；修正后的结果来自同一次已完成 replay，没有重跑候选。

接下来先构造 checked family 到完整 point isomorphism 的生产证明，再组合各
source instructions 的分片对应。静态 instruction ordinals 的组合必须有证明；
源到目标执行次序的改变仍须过依赖验证。随后接 actual Loop、独立 progress、
machine lowering、出口和当前程序 host。整体 fusion 安装通过才完成这项验收。

OLO 的 compact `B ⇒ A`、safe `G accepts ⇒ B`、accepted/refused transport、
共享检查与原 CGO17 contexts/tiers/成本，以及其他 PolCert 顺序变换能力继续
分别验收；本次不关闭完整 goal。
