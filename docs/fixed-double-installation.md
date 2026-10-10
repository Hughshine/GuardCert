# 常量上界的 factory 与完整程序证明

这一步把[常量源树的局部证明](fixed-double-source-trees.md)接到 actual candidate、
projected region contract 和当前程序 Csem→Asm。它闭合了证明接线，但第一次运行
原 `nodep` 没有安装新候选；后续的[实际 I32 上界支持](typed-literal-double.md)
处理了该次运行暴露的源类型缺口。不能把第一次的输出匹配计作优化支持。

## 实际接线与责任

`fixed_double_tree_public_globals` 只枚举源树布局中的实际数组 globals。数学常量的
parameter names 不进入 C global 或 `locals_avoid` obligations。Static decoder、
layout/span、footprint 与 resource checks 建立模型与私有资源所需的事实。

`checked_fixed_double_tree_candidate_execution` 从真实 source execution 得到 source
Loop execution，消费 source-aware pipeline 的实际最终 checker，再消费 residual
candidate lowering。目标先在私有 temps 中 materialize 常量参数，执行候选，最后
恢复原 source 的公开 iterator exits；最终 memory 和 live temps 保持。这里的
source execution 是证明起点，不是运行时预先执行源程序。

`FixedDoubleTreeFactory` 从这些服务证明 projected region contract。既有 scoped
host 提供合法 site 的安装；`FixedDoubleTreeCompiler` 接完整 backend。
`LiteralCombinedDoubleCompiler` 顺序执行 selected literal normalization、新常量
pass 和旧 combined passes，每次处理真正的 intermediate program，并证明最终
Csem→Asm backward simulation。C 用户不提供语义 callbacks。

常量前提由静态证据建立，因此这条路径直接安装 private prelude、candidate 与
exit code；静态拒绝保留源程序。它不要求额外 header loads，也不增加 OLO 的动态
紧凑入口条件推导能力。Kernel 和 host laws 未改变。

## 验证与第一次实际拒绝

[证明摘要](fixed-double-installation.json)覆盖五模块、508 行和 12 个端点：一个
closed，最多 42 个继承的 globals，没有新增 globals。11 次编译尝试中五成功、
六失败，日志与源快照均保留。审计绑定 618 个 reachable sources／10,843 个文件。

提取编译器的记录为
`build/double-tree-model/compiler-attempts/native-literal-combined-v1/report.json`。
原 `nodep` 的 unmarked、untiled 和 requested-tiled 三个配置均编译并匹配原完整
输出，记录为
`build/benchmark-alignment/current-literal-combined-attempts/nodep-v1/report.json`。
但实际旧 tree diagnostics 为零安装，phase 提案为空域拒绝；没有新常量路径安装。

导出并检查原 Clight AST 后，两个上界分别是 signed I32 的 `Econst_int 100` 和
`Econst_int 4`，counter 是 I64。旧常量 decoder 只支持 I64 expression，拒绝了
该实际 source。证据在
`build/fixed-double-installation/source-attempts/nodep-v1/report.json`；两个失败
probe 和成功的 AST probe 均保留。修复必须证明实际 implicit conversion 和
control/progress，再走完整 factory/compiler 链，不能仅给输入添加 cast。
