# 动态整体分块：整数覆盖与组合入口

本页是 2026-10-10 的实现 checkpoint；完整 PolCert 顺序功能和 CGO17 对齐仍未完成。
[Narrative 复核](narrative-integer-cover-check-2026-10-10.md)记录三方责任与验收顺序。
[绑定汇总](dynamic-piece-integer-results.json)保存证明、成功运行、contexts、语料、
成本和本轮失败。以下接线事实继续适用；后继验收结果见末节。

## 实际编译路径

普通 C 使用者标注 `#pragma scop`／`#pragma endscop`，提供 phase、profile 等选项，
不手写目标循环或提交语义 callbacks。支持的源族经实际 Clight decoder 得到
source Loop/model；外部 Pluto 调度、已检查的阶段及 prepared codegen 产生候选。
Quotient adapter 保留候选结构并提出可提取的 affine membership 表示；整数
coverage proposer 提出 split/empty/piece 数据。最终 typed action、坐标、覆盖、
互斥和依赖 checker 消费实际源／候选，不能用提案的诊断 bool 授权安装。

`GuardSelectedDoublePieceIntegerCoverageV5.ml` 是本轮使用的 coverage 提案实现。
它尝试单位系数等式消元、正系数 Fourier–Motzkin 配对及 GCD 整数舍入，提出
既有 `CoverSplit/CoverEmpty/CoverPiece` 树。任意 split 的两分支都必须覆盖；
empty leaf 仍需通过既有 checker。算法不受信任，失败或未知返回 None。
编译时 coverage 解决源点／tile 点对应，不是 runtime overflow/alias 条件合成。

## 证书及职责

| 交付者 | 本轮复用／增加的能力 |
| --- | --- |
| Kernel | 组合既有局部 guard 与 conditional-preservation 证书；没有新增语义定律。 |
| Language/host | 原源许可的 conditional capture、typed private caches、accepted/refused entry transport、private/public frame、公开 iterator exits、独立 progress、当前程序安装和 CompCert backend。 |
| Domain 实现者 | 实际 source/model/candidate 对应、typed actions、整数覆盖／坐标和实际调度验证；数据提案服务。 |
| 普通 C 使用者 | 标注和选项；不提供本表的语义证明。 |

源码的一次正确执行是局部对应证明的起点，没有 runtime source pre-execution。
静态 syntax/layout/resource facts、动态 capture/guard facts 和源执行分别供给
适用前提。源／候选有限 Loop iff 不单独证明任意 Clight divergence 等价；全程序
安装继续消费独立 progress 和实际 host 契约。

## 已通过的功能与观察

[Standalone 运行](dynamic-piece-runtime.json)通过既有
`DoublePieceTreeCompiler.compile_selected_piece_double_tree_program_correct`。
独立运行参数 N/M 是明确披露的 fusion2 adaptation，保留原数组和 IEEE 计算。
三个配置各编译一次，41 组输入产生 123 个匹配的完整输出与公开控制出口。
Untiled 六片、tiled 八片都在最终 Clight 中整体安装，A/B stores 共享循环。
Standalone tiled 编译约 177 秒；不是受控编译期比较。

旧 combined 路径继续优化已 versioned 的候选和 fallback，最终 stack overflow。
新 `SelectivePieceCombinedDoubleCompilerV3` 在第一次 piece pass 的实际输出上
调用任意 `remaining_proposal chosen current`，选择后续标注。Native 策略仅跳过
完整匹配既有 capture/guard/source-tree/restore 形状的标注；不因为其中一个子片段
被优化就跳过整个标注。策略影响搜索，所有接受的后续 rewrite 保留旧契约。
新 root 的 Clight/Cstrategy/Csem 三个端点已审计：87 行，最多 42 项既有 globals，
无新增。[组合入口运行](dynamic-piece-selective-runtime.json)再次通过相同 123 次
完整输出／出口和两个整体候选；两个目标报告 `chosen=1 protected=1 remaining=0`。

[Standalone 观察](dynamic-piece-integer-observation.json)和[组合入口观察](dynamic-piece-selective-observation.json)
各有九次 hardware writes 和十二次 child reads，21 次完整输出均匹配。接受输入
交错写两个采样位置；profile 外输入恢复源次序；未到达 child 时读 M 为零；
(2,3) 源读 M 十六次、每个目标读两次。Assembly/binary 未修改，只观察两个写
位置；没有直接采样 private flag、全部动态 stores 或任意非法指针。

## 保存失败与后续验收

本轮各 coverage/projection/oracle 变体、失败 Rocq 接线及 fresh build/probe
脚本保留供复核。`SelectivePieceCombinedDoubleCompiler.v` 和 `V2.v` 是失败接线
的原始输入；生产入口与审计只使用 `V3.v`。IntegerCoverage 的 V1–V4、V6–V11、
vector oracle、pruning 和阶段诊断变体不作为本页已验收的默认路径。

旧 standalone contexts 使用 180 秒 compiler budget，12 配置中四个 tiled timeout；
实际 native 调用为 56，原报告的名义 84 不可用于结果计数。新组合 contexts
单独使用 600 秒 budget，继续验收多标注、caller/stack exits、continuation 和
资源拒绝。最终 62 原例／两 adaptations 回归及完整进程成本另行完成；成本源
是带重复区域和单独编译 opaque boundary 的披露 variant。先编译目标，所有本轮
其他 goal 命令结束后才采样；boundary、guard、candidate/fallback、公开出口、
初始化及 digest 成本均包含。不能由两个源位置的正确观察推断盈利。

OLO 的紧凑充分入口条件 `B⇒A`、safe `G accepts⇒B`、状态运输、共享检查、有用
接受范围和完整成本仍分别验收。条件库按调用前提、成功事实、读取/private
effects、public frame 和拒绝契约组织；本例没有增加 guard 原子表达能力。

## 后继完整验收结果

[动态 contexts](dynamic-piece-selective-contexts.json)的六类／12 配置、84 次完整
运行均通过，包含多标注与未标注排除、caller 栈上输出和 live temporary、halo／
continuation、外层条件及 private pool 不足的拒绝。Compiler budget 是 600 秒；
两标注的 tiled 编译约 375 秒，不能据此说编译期成本已实用。
[完整语料](dynamic-piece-selective-corpus.json)核对 62 原例、两份披露 adaptations、
192 配置：180 原输出和六 adaptation 输出匹配，六个既有 frontend 拒绝保留。
输入／配置 hashes 和 status 没有变化；原 fusion2 整体融合及 fusion10/nodep
tiled 形状保留。这些计数不等于支持 62 例的全部请求变换。

[完整进程成本](dynamic-piece-selective-cost.json)先编译重复区域 variant，再等
本轮其他 goal 命令结束后采样；固定单 CPU、轮换顺序，每组两个 warmups 和七次
正式采样。六组输入的 162 次完整输出都匹配。Source baseline 与两个目标使用
同一 CompCert compiler/flags；GCC reference 用于核对输出。独立编译的 opaque
boundary 阻止跨重复调用删除 stores，其开销与初始化、startup、digest、guard、
candidate-or-fallback 和公开出口全部包含。外部 host load 未控制，不隔离 guard。

| N | M | Untiled/source 墙钟比 | Tiled/source 墙钟比 |
| ---: | ---: | ---: | ---: |
| 100 | 100 | 1.480 | 1.457 |
| 33 | 31 | 1.185 | 1.187 |
| 101 | 100 | 1.035 | 1.026 |
| 100 | 101 | 1.032 | 1.033 |
| 0 | I64_MAX | 1.271 | 1.785 |
| 2 | 0 | 0.915 | 1.331 |

正工作量输入各重复 1,000 次，空输入重复 1,000,000 次；这些是完整进程中位数
之比。大于一表示目标较慢。本例已通过正确安装／行为验收，**没有通过有用加速
验收**。下一步定位 compiler checking、body membership、机器转换及 capture/check
工作，保留原正确路径并用 fresh attempts 改进；不把总 slowdown 直接归因于 guard。
