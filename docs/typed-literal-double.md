# 实际 I32／I64 常量上界与当前程序接入

本阶段处理原 `nodep` 实际 Clight 的类型组合：I64 counter 与 signed I32 literal
上界比较。它是[第一次常量路线](fixed-double-installation.md)拒绝后的后继，
保留之前成功的源证明、compiler 和失败运行，不修改原 C 计算或补上界 cast。

## 语言、domain 与 host 各提供什么

语言的 `signed_long_bound_condition_active` 处理原 I64/I64 和 I64/I32 comparison。
后一种使用 Clight 的实际 signed arithmetic conversion，即将 `Int.signed` 值
转换成 `Int64.repr` 后比较；不是假定 AST 原来就有一个 I64 expression。它也
为 loaded、raw 和 from-initializer progress protocols 提供 actual active-condition
事实。独立 progress 与有限正常 execution correspondence 分开证明。

Domain 的 `decode_literal_double_bound` 接受实际 signed I32 literal，或复用旧
I64 affine constant decoder。每个 range 保存原 bound expression。Checked AST、
数学常量参数、shared layouts 和 static footprint-to-point facts 由实例建立。
`literal_double_bound_test_execution` 连接数学 comparison 与实际机器求值；
source/Loop iff 保留 IEEE scalar operations、真实 `Mem` 和准确公开 exits。
Initializer、strict comparison、unit increment 和 freshness 的原要求保持。

`LiteralDoubleTreeFactory` 实际调用 source-aware phase、最终 candidate checker 和
residual lowering，组合 private constant cache、candidate 与 source exit。实际
数组 globals 建立 scope 和 layout，数学参数名字不成为 C globals。Factory
自动 discharge 局部证明前提；C 用户只提供标注和策略数据。

`LiteralDoubleTreeCompiler` 复用 scoped host 的 legal-site、frame、progress 和
current-program 安装。`TypedLiteralCombinedDoubleCompiler` 从原 Csyntax 依次
执行 frontend normalization、selected double-literal normalization、新 literal
pass、旧 combined passes 和 backend，给出 Csem→Asm backward simulation。
Repeated passes 每次消费实际 intermediate program 的证据。

这是 kernel 之上的语言与 domain 扩展，没有新 kernel/host law。常量前提静态
建立；没有新 speculative read，也不是 OLO 动态 compact-entry construction。
`k=j` initializer、混合 loaded/fixed 端点和 general piece／ISS 继续未完成。

## 证明验收

[证明摘要](typed-literal-double.json)覆盖 16 模块、1,974 行、51 个端点：十个
closed，最多 42 个继承的 globals，无新增 globals。17 次编译尝试中 16 成功、
一次失败，均保留快照和日志。Audit 绑定 623 个 reachable sources／10,943 个文件。

原 source AST 的成功 decoder probe 记录为
`build/fixed-double-installation/source-attempts/nodep-v1/typed-report.json`。
整个外层 range 检查通过；把内层单独取出会失去其外层控制环境，仍保守拒绝。
这个 probe 只证明实际 decoder 的结果；native candidate、最终安装、实际变换和
完整输出必须另行验收。旧 guard-shape counter 不统计新静态常量路径。

## 第一次 native 运行仍走 fallback

`build/double-tree-model/compiler-attempts/native-typed-literal-combined-v1/report.json`
绑定提取编译器和 11,395 个文件。原 `nodep` 三配置均输出匹配，记录为
`build/benchmark-alignment/current-typed-literal-combined-attempts/nodep-v1/report.json`；
实际 Clight 仍保留原两层循环，没有 literal candidate 安装。

逐 gate probe 显示原外层 source 的 active、instructions、footprint、layout span、
progress、counter pool 和 freshness 全通过。但 extractor 要求数学 context 的
参数也出现在模型变量声明中；旧 request 有两个数学参数、只有一个数组声明，
在模型 well-formedness 检查处拒绝。这里要区分 mathematical declarations 和
语言 host 的 actual-global scope。[模型声明后继](declared-literal-double.md)
补前者，保留只含真实数组的 C scope，并重新证明完整 compiler。

`build/typed-literal-double/source-attempts/nodep-gates-v1/` 保留一次缺失 import 的
失败及三次成功 probe；`GatesV4` 直接对照原 request 的拒绝与后继 request 的
成功提取：一个 instruction、两个参数、三个数学 declarations。它不增加内存
读取、不修改 source、不需要额外 host law；native 效果仍由后继运行验收。
