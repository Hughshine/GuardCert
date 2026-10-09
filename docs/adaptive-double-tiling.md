# 默认资源提议、完整原语料与 codegen 诊断

2026-10-09。本次按用户提示重新 fetch 并读完 narrative。最新可见远端仍是
`topdown/research-positioning@8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9`，
[paper-narrative.md](topdown/paper-narrative.md) 和 context-lifting 的正文与 main
一致；这里不声称看到另一个尚未推送的澄清版本。

## 对接口及责任的落实

最小 kernel 止于局部 guarded correctness。语言实例提供检查安全、choice、
private frame、公开出口、progress 和完整程序安装；domain factory 建立支持族
的 source/model、充分入口条件及实际候选对应。`C_opt`、`C_derive`、`C_guard`、
`C_host` 标明证据来源，不是四份要求源码用户逐 site 手填的 record。
每次 pass 消费当前 intermediate program 的证据，有限次安装再组合。

此次修改属于不受信任的资源／见证提议和编译诊断。支持族用户仍提供 marked C
与 phase/tile 选项。新策略从实际 Csyntax 提议 budgets，既有 factory 核对资源
和每个见证，复用同一个
`InitializedDoubleTiledStableCompiler.compile_selected_initialized_tiled_stable_program_correct`
Csem→Asm 端点。没有新增语义 compiler theorem、runtime condition、guard family、
kernel 或 host 定律。实际 guarded-execution 证明仍直接构造 Clight branches，
不能把 kernel 未改或 import 当成直接调用 generic composition theorem 的证据。

## 默认策略及实际完整运行

[GuardSelectedDoubleAdaptiveTiledCandidate.ml](../adapters/compcert-memory/native/GuardSelectedDoubleAdaptiveTiledCandidate.ml)
扫描所有函数的实际 loop depth。开启 tiling 时，暂以两倍源 depth 提议 candidate
depth；private count 为 `max(16, 2*depth+2)`，witness axes 为 `max(6, depth)`。
有限 choices 包括 identity 和每个相邻交换。显式覆盖仍可用于诊断。
这是保守提议，不是证明过的最小资源、通用充分预算或一般 affine witness 搜索。

新默认 compiler 完整尝试 pinned 62 原例及两份已披露 initializer adaptations。
使用 tile 32、600 秒 compiler budget，无 private-count 或 witness-axes 覆盖；
实际 Pluto 同时启用 affine scheduling、tiling 和 intra-tile scheduling。

| 结果 | 此次单一 build 的范围 |
| --- | --- |
| 原始输入 native 输出匹配 | 59/62 |
| 披露适配的输出匹配 | 2/2，单独计数 |
| 原始 frontend 拒绝 | corcol3、pca |
| Compiler 超时 | polynomial，600.016 秒；没有 raw candidate |
| 安装 guarded transformations | 13/62 原例、29 sites |
| 已编译原例没有 tiling phase call | 45 |
| 调用 phase、未安装的已编译原例 | tricky3；raw candidate 没有生成 |

安装案例为 dct、fusion6、fusion7、gemver、matmul-init、matmul-seq、matmul-seq3、
multi-loop-param、mvt、mxv、mxv-seq、mxv-seq3、tce。前一 reindexed build 的
9/62、22 sites 保留独立版本范围，不合并成当前结果。
Initialized route 在本次完整运行中接受原 dct、mxv 和 matmul-init，各一处。
Tce 的源 depth 为 5，自动提议 22 private temps、十轴见证，四个实际候选全部
安装并匹配原输出；241.999 秒编译时间仅为诊断。此前手动十轴的后继不是
默认策略修复证据；此次完整运行才建立该证据。

额外七项 public/legacy 回归通过：正、零、负 bound 的公开 I64 iterator 值
与 GCC 一致，legacy affine matmul 继续安装。此 batch 的原 assembly 未做
debugger branch 观测，因此不将输出匹配描述为新增实际 branch-count 证据。
13 个安装案例也不自动等于 speedups、所有输入运行时接受或完整非恒等效果计数。

## Polynomial：缩小瓶颈及保留未成功的补救

第一份 120 秒诊断中，affine validation 和 tiling validation 合计约 0.4 秒，
进入 prepared codegen 后超时。最后一个 emptiness query 已完成，596 条约束、
约 0.0002 秒；不能将整个超时归因于一次慢 oracle query。

新增三个模块共 172 行、六个 equality endpoints，1 closed；其余 endpoint 合计
引用 11 个既有 globals，均包含在原 42-global baseline 中，没有新增公理。
[GuardMemoryDoubleTiledPhaseTrace.v](../adapters/compcert-memory/GuardMemoryDoubleTiledPhaseTrace.v)
用已有逻辑 identity trace 包装阶段；
[GuardMemoryDoubleCodegenTrace.v](../adapters/compcert-memory/GuardMemoryDoubleCodegenTrace.v)
和 [GuardMemoryDoubleTiledCodegenTrace.v](../adapters/compcert-memory/GuardMemoryDoubleTiledCodegenTrace.v)
进一步区分 schedule elimination、AST generation、simplification、Loop lowering
和 cleanup。Rocq 已证明包装计算与原计算 definitionally equal。日志只来自编译器，
目标 guard 和 assembly 没有插入 instrumentation。

独立后继还尝试不受信任的 exact-duplicate add policy：
[GuardMemoryCompactOracle.ml](../adapters/compcert-memory/native/GuardMemoryCompactOracle.ml)
仅返回已有 input certificates 的子集，原 emptiness search、限制与 LCF 检查保留。
既有 VPL `CstrD.assume_correct` 是 overapproximation 契约；此 native proposer
没有新增精确 conjunction 等价性或最小化证明。后续 verified checks 仍负责接受。

该尝试没有修复 polynomial。120 秒内记录到更多 completed queries，最后一批
约束也更少，但仍未生成 raw Loop。第二个 codegen trace 后继明确停在
`codegen-ast`；没有进入 simplifier、Loop lowering 或 cleanup。三份 focused
diagnostics 均保留 mvt 的两处安装及原输出。不能根据这些受 instrumentation、
并行任务影响的小批次时间宣称 compile-time speedup 或目标程序收益。

完整 corpus 使用默认原 oracle；compact/trace builds 只尝试 mvt 与 polynomial，
不将这三份 focused diagnostics 冒充完整重跑。初始 build 遗漏 Reindexed native
module、错误要求 equality endpoints 全部 closed，以及两次 proof 拼写/名字解析
错误的记录均保留；成功 sources、objects 和 native attempts 不原位重写。

## 下一步与验收范围

1. 对实际 polynomial 的 AST generation 追踪投影与 canonization 的约束增长，
   实施可检查的 compaction／projection 补救。Raw candidate 完成后，再处理
   实际 `(i+j,i)` schedule 及 skew coordinates 的最终表示证明与安装；扩大
   swap 列表或改成 identity scheduling 不能替代这个支持目标。
2. 定位 tricky3 和其余 45 个没有 tiling phase 的 source/factory checker 缺口，
   扩实际 nonzero/inclusive starts、multiple bounds、statement sequences 等结构。
   每条扩展同步 actual source、充分条件、安全 guard、candidate progress、公开
   出口和 Csem→Asm，不将有限 source/model theorem 留作源码用户的假设。
3. 继续 ISS、diamond/two-level、unroll/jam 等 sequential configurations，保留
   原 BT、LLVM/SPEC、larger tiers。条件 code size、checking work、有用接受域和
   完整调用成本分别验收；服务封装不替代紧凑条件推导或实际优化效果。

[固定摘要](adaptive-double-tiling.json)绑定 12 份 reports、14,618 文件，含上述
失败、完整运行、focused diagnostics、证明和公开出口检查。复核命令：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/summarize_adaptive_double_tiling.py --validate
```

完整 goal 保持 active；此次只关闭默认资源策略／单配置重跑，并缩小一个 blocker。
