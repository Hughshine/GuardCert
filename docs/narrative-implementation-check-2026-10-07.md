# Narrative 澄清与当前实现的核对

2026-10-07，核对对象是 `topdown/research-positioning` 的
[`paper-narrative.md`](topdown/paper-narrative.md) 与
[`context-lifting.md`](topdown/context-lifting.md)。本轮重新 fetch 的远端为
`271f6fc941910456da43a76e9f0eed38e8a5e200`，这两个文件与 main 一致。
本文记录如何吸纳其中的澄清，不声称远端出现了 main 尚未收录的新提交。

## 接口与证明归属

最小 kernel 止于局部 guarded correctness。条件组合、扫描、规范化和充分条件
推导属于核上的库；具体语言负责 guard 的实际执行与程序安装。四条逻辑链
`C_opt / C_derive / C_guard / C_host` 不要求使用者填写四份独立证明 record。
领域实现可以用数据描述器和已验证 checker 生产其中的多个环节。

当前 tensor 接入遵循这一边界：

| 责任方 | 提供什么 | 本轮具体消费／生产位置 |
| --- | --- | --- |
| Framework kernel | 从 condition 和 conditional preservation 得到 local guarded preservation | `GuardInterface.guardify_preservation`，由新的 `ClightReadonlyPreservationKernel` 调用 |
| Clight 语言库 | 检查语义、readonly frame、实际 direct/shared choice、私有资源、progress／scope／continuation 安装与后端 | 既有 readonly guard realization、`PrivateRegion` 和 CompCert pipeline；新 `ClightLoopAdministrative` 证明原 AST 的行政 skip 运输 |
| Tensor domain | 实际源与 Loop 模型对应，affine 坐标范围到地址／依赖前提，安全 guard 和候选执行、公开出口恢复 | 既有 tensor source／box／candidate services，新 package 将它们组合为局部规则 |
| 优化策略与具体 site | 选择原片段，提出 metadata／候选／profile，取得符合 host 要求的实际位置证据 | 不受信任 native proposer；Rocq factory 核对实际 AST、参数使用和 namespace；host 继续检查原源 progress 和 private pool |

对这套受限 tensor factory，使用者提出 dimensions、scalar identifiers、pointer、
affine read/write coordinates、value expression、profile 和 candidate。
这些是数据提案。使用者无须另填源执行到模型、BOX、pointer binding 或候选出口
的语义 callback。支持另一种 source/transformation 时，其 domain 实现仍须证明
那些对应和充分条件；factory 的成功不能替代尚未实现的领域证明。

## 已连接的链与最难的证明位置

`C_opt` 消费既有 mapped／tiled domain 与依赖 checker，连接实际 candidate。
`C_derive` 从真实原源的有限正常执行取得使用过的参数和访问许可，再把入口
profile、layout 和全部 read/write 的 affine extrema 接到模型义务。
`C_guard` 证明真实短路机器检查的安全、可用性、接受 soundness。
`C_host` 解释实际 choice 和 checked-state 运输；随后的 region 安装另行消费
语言 host 的 scope、progress、private allocation 与 continuation 定理。

这里的安全域 `D` 是源完成提供的局部事实。完整程序证明仍需要 host 的进展
协议，不能把“存在一次源完成执行”直接当作所有程序入口的终止性。
同样，数学 BOX 或 `G accepts ⇒ B` 单独都没有证明 condition 可以安全读取。

最困难的连接仍是：安全地获得原路径许可的值；证明条件覆盖模型所需的全部
动态访问；运输检查后的实际状态；保持上下文会观察的出口与 memory；匹配
尚未完成的原源进展。这些工作归属于语言和 domain 的具体 producer。
不能把它们隐藏成未实现的接口字段，再把 kernel 的组合定理当作整项交付。

本轮真实 C 检查还暴露了一个具体语言问题：前端在 leaf 赋值周围插入
`Sskip` sequence。数据 recognizer 原先只接受直接赋值，结果全数回退。
新增语言 normalizer 保持 terminating trace、outcome、temps 和 memory，
在 recognized loop 中保留原 header／increment，只规范化 body 的行政包装。
Factory 核对规范化源，candidate 证明通过该语言定理消费实际原源执行。
Fallback 和 host progress 检查继续使用实际原 AST。这说明语法规范化也是
语言服务的证明责任，无须扩张 kernel 或修改候选条件正确性。

## Context lifting 的设计结论

当前 finite projected host 复用 live-temp agreement、memory equivalence、静默
正常完成和私有资源；direct/shared 实现主要区别在检查状态与 choice realization。
Open host 的逐步进展／可能不退出协议与 finite host 有实质区别，不能只把
record 字段改名就当作两者统一了。

本轮维持已有 host。一个真实 rewrite 若被现有边界阻止，应先记录被阻止的
control／effect／progress 需求，再考虑 guarantee／requirement 的拆分及 entailment。
目前不引入任意 clause 组合的 contract algebra，也不把 generic lifting 字段
本身称为完成了 contextual closure。第二 IR 仍是可选表达力证据。

## 吸纳到后续验收的顺序

1. 先闭合约定子集的真实输入到安装、后端、运行链。Tensor 当前子集是正的
   rectangular temp-bound nests、单 Horner-address RMW leaf、一个 tensor。
   证明通过和编译成功分别记录；实际接受、拒绝、重复 sites 与上下文另验收。
2. 该子集闭合后立即做同例 OLO 对照，分别记录 guard code size、运行工作、
   接受域、完整程序成本和三方作者负担。不要等待所有 roadmap 扩展，也不要
   把 compact 数学条件或更小代码当作已有净收益。
3. 扩展 literal-bound transport、更多 body／affine domains、跨 tensor alias、
   loaded-bound stability 与更完整 BT 场景。每项说明 source adaptation 和缺口
   是 frontend、条件算法、证明还是具体机器语义造成的。
4. 随已验收阶段同步论文正文与证据。Related work 的结构可先写；novelty、
   功能覆盖、自动化和收益声明受实际比较结果约束。

本轮原 kernel、旧 tensor source／box services 和已有 native 报告均保持。
完整目标继续 active；当前结果不等于完整 OLO 功能／usability 验收。
