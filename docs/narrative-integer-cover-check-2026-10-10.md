# Narrative 澄清的复核与本轮验证边界

本轮后继结果见[绑定汇总](dynamic-piece-integer-results.json)：新组合入口的
动态 contexts 全部通过，最终语料 status／source hashes 保持，完整成本已测量。
接受且有实际工作量的两个输入没有加速，不能宣称性能验收完成。下文保留本轮
接线与责任分析；后续以当前工作计划首节和绑定报告为准。

2026-10-10 重新 `git fetch origin topdown/research-positioning`。可见最新提交仍为
`8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9`；本次比较的
`docs/topdown/paper-narrative.md` 与 main 无正文差异。本页记录实施如何响应已可见
的澄清，不声称远端出现另一份新修改。

## 三方交付物

| 提供者 | 必须交付 | 本实例如何使用 |
| --- | --- | --- |
| Framework kernel | 消费既有 host/guard/conditional-preservation 证书，组合单次局部 guarded correctness。 | 不解析 affine domains，不判断 alias，不自己实现目标语言的 `if`。 |
| Language/host 作者 | 检查实际安全执行、接受与拒绝状态运输、private/public frame、控制出口、独立 progress 和当前程序安装；再连接 backend。 | 复用 Clight loaded-bound capture、未到达 child 的零初始化、原源 fallback、公开 iterator 恢复和 Csem→Asm。 |
| Domain/优化族作者 | 实际源、模型和 candidate 对应；假设下的局部正确性；适用的 `B⇒A` 推导，以及必要的数据提案或 checker。 | scheduler/codegen、piece 坐标和 coverage tree 都是数据；实际 total checker 消费 typed actions、覆盖、互斥和实际调度。 |

支持族的普通 C 使用者提供标注、选项和策略数据。新增语言、优化族或 guard 服务
需要证明其接口义务；这些不转嫁为每个 C 输入的人工作业。原源的一次正确执行
在证明里提供起点，不是 runtime guard 要预先执行的程序。

## 本轮最难的位置

独立 `N/M` 的动态 fusion2 产生八个 tiled pieces。此前 coverage 搜索只处理有理
polyhedra，未能表达整数 tile 边界排除的分数点。本轮的数据提案加入整数切分，
继续使用已有 `CoverSplit/CoverEmpty/CoverPiece` 检查：它不会凭 proposer 的 bool
授权安装，也不引入新的 kernel 或 host 定律。

逐阶段诊断确认两个 parent 的 actions、coordinates、cover、disjoint 检查通过。
随后在既有 `DoublePieceTreeCompiler` 的 standalone 全程序入口上，实际总检查、
machine lowering 和整体安装均通过：untiled 六片、tiled 八片的 A/B stores 共享
循环；三配置各编译一次，41 组输入的 123 次完整输出和公开出口全部匹配。
[运行报告](dynamic-piece-runtime.json)保留原数组和 IEEE 计算，独立 `N/M` 是
明确披露的源码 adaptation，不能计作全部原始语料的功能覆盖。

[机器观察](dynamic-piece-integer-observation.json)另外完成九次两位置写观察及
十二次 child `M` 读观察。接受输入交错写两个数组，profile 外输入保留源次序；
未进入 child 的输入读取为零，正 outer 的两个目标配置各读两次。21 次完整输出
匹配。这没有观察全部动态 stores、private flag 或任意非法指针。

原组合编译的长 trace 进入后续旧 pass，最终 stack overflow；失败保留。新增
current-program selection 仅决定后续 pass 的位置数据，跳过已安装完整 guarded
tree 的标注；每个剩余位置仍由既有 checker/host 证明负责。新组合入口的三个
定理已重新编译和审计，87 行、最多 42 项既有 globals、无新增。
[证明报告](dynamic-piece-selective-proof.json)与 native 验收分别记录。
[标准提取后的组合入口](dynamic-piece-selective-runtime.json)已通过同源 123 次
完整运行；两个目标配置都报告 `chosen=1 protected=1 remaining=0`，并保留实际
整体候选。[组合入口机器观察](dynamic-piece-selective-observation.json)也完成
九次写／十二次读取及 21 次完整输出匹配。第一次观察因沙箱不允许 ptrace 被
拒绝，保留原失败；后继只对已生成 binary 进行本地调试观察。多位置/caller
contexts、最终语料和成本仍单独验收。该策略不是新 kernel/host law。

本轮将上述问题与 runtime 条件推导分开。Coverage 的整数证书是编译时 domain
义务；它不是对运行时 no-overflow/alias 前提的 guard synthesis。现有 profile
和条件式 capture 已提供安全入口条件，但通用 compact condition 推导、共享检查
及有用接受范围/完整成本仍需验收。整数 checker 的工程性能也是 domain 实例的
实际可用性要求。

## 后续验收顺序

1. 保留 standalone 已通过的真实安装及组合入口的超时/失败。验收新 selective
   组合入口的提取后行为，不把数据策略的可用性当作候选正确性的证明。
2. 最终 compiler 路径上核对接受/回退、条件式 child 读取、caller/多位置 contexts
   和完整调用成本；未产出目标程序的配置不能计 native matches。
3. 保持 PolCert 顺序功能与 CGO17 原源/contexts/tiers 的目标。逐例修复 source/
   candidate/phase/checker/lowering 缺口；不能以本例或安全拒绝缩减总体验收。
4. 继续从局部义务得到 compact sufficient condition，再证明安全求值和入口运输。
   五类 guard 服务按调用前提、接受事实、读取/private effects、public frame 和拒绝
   行为组织；允许 ordered checks、conditional capture 和多种充分条件。

框架的通用性是证书边界与可复用服务的通用性。新示例必须记录哪些义务由 kernel
组合、哪些由语言库建立、哪些仍由 domain 实例承担；论文贡献不能只归结为
conditional equivalence 加一个 `if`。
