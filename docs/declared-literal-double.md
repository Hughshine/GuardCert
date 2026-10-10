# 数学参数声明与 actual-global scope 分离

这是[实际 I32／I64 常量路线](typed-literal-double.md)第一次 native fallback 后
的修复。语言类型与 static factory checks 已通过，模型 extractor 却拒绝两个
参数／一个数组声明的 request。修复只在 PolyLang 数学变量 declarations 中
加入参数；C host 的 scope 继续只包括真实数组 globals，没有新增 C globals、
header loads 或 source adaptations。

## 接口与证明责任

`declared_literal_double_tree_pipeline_request` 的 context 是共享数学常量参数，
variables 声明这些参数和实际数组。Domain 实例负责生产这个 well-formed request，
而不是要求 language scope 替这些数学名字寻找 C globals。Language 原有的 actual
source/Loop iff、I64/I32 comparison、private constant caches、scope、IEEE／Mem
lowering、准确公开 exits 和独立 progress 直接复用。

`checked_declared_literal_double_tree_candidate_execution` 消费同一 source-aware
phase、最终 candidate checker 和 actual residual lowering，保持最终 memory 与
live temps。新 `DeclaredLiteralDoubleTreeFactory` discharge 相应检查；
`DeclaredLiteralDoubleTreeCompiler` 和 `DeclaredLiteralCombinedDoubleCompiler`
消费真正 intermediate program，复用 scoped host 和 CompCert backend，证明
原 Csem→Asm backward simulation。Kernel、host laws 和 C 用户接口保持。

常量实例使用静态事实，拒绝时保留原 source；它不构造新的动态 guard，也不
完成 OLO 的紧凑入口条件算法。数学参数 declarations 不能替代 machine safety，
输出匹配也不能替代实际 candidate installation 或 transformation evidence。

## 已验收的证明与模型提取

[证明摘要](declared-literal-double.json)覆盖四模块、449 行和九个端点。四次
编译均通过；最多 42 个继承的 globals，无新增 globals。审计绑定 10,980 个
文件；旧证明、失败 compiler/replay 与成功源快照均保留。

对原 `nodep` 的 source probe 已对照旧／新 request：旧 extractor 拒绝，后继
提取一个真实 instruction、两个 context 参数、三个数学 declarations。证据为
`build/typed-literal-double/source-attempts/nodep-gates-v1/GatesV4.v` 及其成功日志。
这只验收模型提取；native phase、最终 candidate、标注边界、公开出口、实际
执行与完整输出还要由真实 compiler run 验收。

## 原 nodep 已进入真实候选并执行

`native-declared-literal-combined-v1` 已构建，提取记录绑定 11,432 个文件。原
`nodep` 的三个配置均与原完整输出匹配；数学 source params 是原常量 100／4，
数组仍是原 404 个 doubles，实际 instruction 保留 `2*A+2`。Untiled phase
产生非 identity schedule，tiled phase 增加两个 tile dimensions，size 为 32。
最终安装的 private prelude 和准确 `i`／`j` exits 在 actual Clight 中可见。
Unmarked 配置保留原循环；旧 guard-shape diagnostic 的零计数不描述新常量路线。

[完整执行摘要](declared-literal-nodep-execution.json)观察未修改 assembly：source、
untiled 和 tiled 各执行 400 次实际更新，原 indices 2–401 每个恰好一次。Tiled
的每次更新的 actual tile registers 与 witness 的
`((4*i+j)/32, i/32)` 整数坐标一致，共 13 个有更新的 tile groups；三次调试器
运行均匹配完整原输出。一次 observer 错选 initializer store 的失败单独保留，
没有把其 404 次初始化当成 candidate updates。

这关闭原 `nodep` 的常量上界支持缺口；不完成完整 62 例回放、动态 guard/refusal、
OLO compact conditions 或成本验收。实际 tiled candidate 含较多 membership
conditions，不能仅凭安装和 output match 宣称收益。完整语料后继已开始运行，
该阶段的最终结果见下节；实际候选与成本仍分开验收。

本输入三配置的 actual update order 相同；untiled 的 schedule 表达变化不是
重排序效果或性能收益。Tiled Loop 有四层，实际 Clight 的 conditions 为 72，
source 为二、untiled 为十。这个 code-size 观察也不等于 runtime cost 测量。

完整语料中已有两个 terminal tiled failures：`fusion10` 原为成功编译，现于
实际 phase 后 stack overflow；`fusion2` 在相同区间超过 180 秒。64 MiB stack
重试未解决前者。[失败摘要](literal-tiled-codegen-blockers.json)保留相同输入与
旧 baseline 三配置匹配、当前两个配置匹配及实际失败日志。它们不是 successful
fallback；该摘要只绑定这两项 terminal failures，具体算法内的增长位置仍需定位。

## 完整语料结果

[最终对照](declared-literal-double-corpus.json)重跑 62 原例与两份 disclosed
initializer adaptations，共 192 配置。184 个完整输出匹配：原例 178/186，
adaptations 6/6。没有 native mismatch 或 link failure；六项已知 initializer
frontend 拒绝保持，只有 `fusion10`／`fusion2` 的 tiled status 相对 quiet baseline
从成功变为 compiler failure。输入 hashes 逐项保持。

旧 shape diagnostics 的 untiled tree 八例／typed 十五例、并集 23；它们不统计
新 literal path，不表示 actual transformations 的逐配置验收。`nodep` 的单独
AST、witness 与 400-store 观察是新 literal installation 的直接证据。广泛成本、
两项 operational regressions、其余 source／target 结构和 OLO 条件算法仍开放。
