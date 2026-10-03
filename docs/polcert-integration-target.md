# 多面体能力接入目标：以 PolCert 为功能参照

2026-10-02 用户澄清：PolCert 是功能与证明架构的参照。允许为 CompCert 必要地重实现状态、IR、算法与证明，要求基本多面体功能达成一致，并通过统一的 guarded transformation 框架获得完整程序保证。调用现有 PolCert 源码不是验收条件。当前动态矩形交换与保持顺序的循环分块已进入完整程序路径；实际依赖检查、矩形纯写二维 tiling 和完整程序定理也已接通；静态仿射叶子条件的非矩形域也已接通完整 C 分块入口；更一般仿射域、多语句与任意外部候选仍未达到完整目标。

## 所需链路

```text
完整 C 程序
  → 识别参数化仿射循环与内存访问
  → 构造多面体表示，证明在入口前提下与源片段对应
  → 人或工具提出调度、分块等候选
  → 验证域对应、依赖保持及候选可执行性
  → 将算术、内存与出口前提编码为安全的运行时检查
  → 重建真实 Clight 候选，检查失败执行原片段
  → CompCert 后端与完整 Csem→Asm 正确性
```

候选生成可以复用 PolCert、Pluto，也可以由自建算法或人工提供。语言实例负责证明真实机器算术、内存、访问和交换性质；框架组合条件与证明。支持的前提表达子集必须明确。从给定前提生成检查，与从源／候选自动发现前提，分别报告。

## 功能与证明能力对齐

| 能力 | 当前证据 | 尚需完成 |
| --- | --- | --- |
| 参数化循环提取与源对应 | 动态矩形与静态仿射 cut 的完整 AST、真实源执行解码与循环出口；另有参数化 Loop lowering 证明 | 一般嵌套仿射域与多个语句的提取 |
| 仿射调度及依赖验证 | 实际 Mem 的一般 validator 已提取执行，验证参数化域、多语句、重排与实际二维 tiling；三种矩形循环的 C 编译器已消费真实依赖检查 | 多语句及一般域的完整 C 源提取与候选接入 |
| 循环生成与出口对应 | 实际动态矩形候选、精确 iterator 出口与完整程序宿主；另有嵌套 Loop lowering；private temporary 完整程序宿主已闭合 | 一般域和外部调度驱动的循环生成 |
| 分块与域变换 | 任意正块大小的 strip-mining、尾块对应、辅助边界无溢出检查、private temporary 宿主与实际候选执行 | 更一般 tiling 与域变换；矩形纯写二维 tiling 已消费实际域与依赖证书 |
| 前提编码与检查 | 从源布局生成的矩形边界检查、条件读取安全证明；可组合性质接口与动态仿射检查 | 一般候选所需前提的发现与编码；扩展 alias/layout 前提 |
| 完整程序接入 | 实际 Clight 区域宿主与 Csem→Asm 定理；真实依赖检查的矩形路径已提取运行，故障 oracle 安全拒绝 | 继续闭合一般调度、多语句与更一般分块规则 |

这张表比较的是能力和语义保证，不要求复制 PolCert 的表示或逐个函数。先闭合顺序的参数化仿射调度与分块路径，再按同一标准对照 ISS、更多 tiling 路线及其他已验证能力，明确支持与未支持项。并行扩展需要额外执行语义和后端证明，生成注释不能代替这一保证。

## 已有 PolCert 适配的用途

`PolCertOptimizer.optimize_version` 在 Loop 层调用实际 `Core.Opt_prepared`。`PolCertOptimizerRegion.compile_optimizer_result_correct` 提供参数化完整程序端点。这些组件可以复用；它们尚未提供具体源解码、候选进展和候选编码的完整实例。

锁定 CInstr 的旧 `CState.valid` 在非空声明下不可满足，已有审计与新的真实执行见证。这一问题只约束复用该状态模型的路线；自建 CompCert 状态与 IR 可以避开它。自建路线仍必须证明入口非空、机器运算与内存访问正确、公共状态与候选辅助状态的出口对应。

## 第一阶段验收

1. 输入是含参数化数组循环及周围代码的实际 C 程序；支持一类明确的循环结构和多组动态边界。
2. 候选从调度或域变换描述机械生成；包含实际非恒等仿射调度，随后加入分块。固定四点排列仅作为回归样例。
3. 对给定前提生成检查并证明编码正确和求值安全；检查成立运行候选，检查不成立执行原片段。不支持或验证失败的候选安全拒绝。
4. 源对应、依赖保持、候选进展、机器算术与出口修复均有具体证明，完整程序定理不把核心义务留作未实例化字段。
5. 实际提取的编译器生成可运行汇编，验证快路、回退及外围可观察结果，报告支持范围与假设。与 PolCert 的功能差距逐项更新。

`compile_scheduled_regions` 和 CInstr 双写交换保留为验证条件与程序组合的回归实例。它们已证明的部分可以复用；动态矩形规则的实现与验证见 [dynamic-rectangles.md](dynamic-rectangles.md)；顺序分块与辅助变量接口见 [private-stripmine.md](private-stripmine.md)，一般仿射域和多语句源桥接仍需实现，矩形纯写二维 tiling 见 [memory-two-dimensional-tiling.md](memory-two-dimensional-tiling.md)。

## 一般 validator 的具体内存路线

[GuardMemoryInstr](../adapters/compcert-memory/README.md) 已提供完全证明的实际 INSTR 实例，直接消费 CompCert Mem.load/计算/Mem.store，并具体实例化一般仿射和 tiling validator。它不使用旧 CState.valid；平面数组的物理 nonalias 是闭合证明。二十二个模块已将三种完整矩形 Clight 交换、矩形和仿射条件域纯写二维 tiling 接到 Loop、PolyLang、依赖验证和候选执行；环境索引的端点保留实际入口参数值。`GuardMemoryCompiler.compile_memory_regions_correct` 是这条路径的完整 Csem→Asm 定理。

原生检查器已有 29 组提案及 1001 组独立执行比较，包含二维 tiling；完整 C 编译器已有 795 个正矩形及外围上下文、回退和故障 oracle 验证。这些模块仍不等于一般完整程序接入：任意嵌套仿射域、多语句、一般候选的 C 源／候选 bridge 尚未完成。二维 tiling 的矩形及静态仿射条件域纯写 C bridge 和完整程序定理已通过编译；条件域入口还有五组块大小、4800 个正动态域的真实快路、完整数组、计数器及拒绝验证，见 [memory-affine-conditional-domains.md](memory-affine-conditional-domains.md)。专用审计的完整编译器继承 CompCert 与 VPL validator 的并集 42 项假设，没有新增公理；默认动态矩形／分块编译器的 35 项基线不受这条可选路线影响。
