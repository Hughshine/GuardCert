# 初始化与 reduction 的真实分块：责任、安装及后继资源修复

2026-10-09。再次 fetch `topdown/research-positioning` 后，最新可见为
`8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9`；main 的
[paper narrative](topdown/paper-narrative.md) 与该分支正文一致。
本文记录其责任边界在一个实际扩展中的应用，不更改 topdown 的验收范围。

原 `mxv`、`matmul-init` 现在可以经自动 affine scheduling、tiling 和
intra-tile scheduling 产生实际候选，再安装到完整程序。两例各安装一处。
初始化与 reduction 的 statement depths 不同，复用已有 uniform exporter、
prepared codegen 与最终 reindexed tiling checker；C 使用者不手写目标循环。
原 IEEE double 表达式、I64 controls、全局数组和驱动保持。

## 使用者与三方责任

支持族的 C 使用者提供 `#pragma scop` / `#pragma endscop` 与普通策略。
标注只选择尝试位置，不提供语义假设。当前数据接口包括 phase proposer、
最终 Loop adapter、有限 coordinate choices 和 checked private-count 参数。
这些 proposer 不提供受信任的语义 callbacks；实际 factory 检查其结果。
新语言或新 transformation 的库作者仍须生产各自的 host 或局部证明。

| 责任 | 实际消费的证明／实现 | 此扩展提供或复用的内容 |
| --- | --- | --- |
| Kernel：局部证书组合 | 既有 `guardify_refinement` / `guardify_preservation` | 定律不改。本路线直接构造 Clight branch execution，没有直接调用这两个 generic 定理；import 和 endpoint 数不是复用证据。 |
| Domain：`C_derive` 与 source/model | 既有 `checked_double_initialized_capture_model`、checked footprint bounds | 原 finite normal execution 许可读取；安全 capture 的接受事实生产实际 count、model 与 point bounds。Source execution 是证明起点，不是 runtime 预执行。 |
| Domain：`C_opt` 与实际候选进展 | `checked_double_reindexed_tiled_prepared_loop_progress_at` | 新 lowering 直接消费最终实际 body 在相同 captured parameters 的 forward execution；raw codegen backward correspondence 不替代它。 |
| Language：实际执行、frame 与出口 | `compiled_double_initialized_candidate_execution`、`double_initialized_exit_code_execution` | 复用 typed lowering、private frame 和公开 I64 control 恢复；不重证每个 tiling 规则的 Clight continuation。 |
| Domain factory：region guarantee | `initialized_double_tiled_region_contract`、`check_initialized_double_tiled_region_sound` | 内部闭合 metadata、source/model、condition、candidate、frame、scope 与 public exit 的适用前提。 |
| Language/site：整程序安装 | 既有 `apply_selected_initialized_double_table_correct`、`apply_selected_tiled_double_table_correct` | 复用 annotation-sensitive scoped host、source progress、actual program scope 与 freshness。 |
| Compiler：多 pass 组合与后端 | `compile_selected_initialized_tiled_stable_program_correct` | 每步检查当前 intermediate program；组合到原 `Csyntax.program` 的 Csem→Asm backward simulation。 |

这里的 region guarantee 和 context requirement 不自动相同：既有 host 要求
公开 temps agreement、memory equivalence、silent normal region execution 和
适用 source progress。Factory 生产该保证，site checks 生产 placement／scope／
资源；没有通用 boundary clause algebra，也没有由有限 exit theorem 自动得到
任意 divergent replacement。新 source 的这些义务不能移交 marked C 用户。

## 条件库的实际契约

这条路线沿用 common global I64 bound 的充分范围条件。源两例接受
`0 <= N <= 98`，extent 104 变体接受到 102。32 步二分只提议 limit，verified
footprint checker 决定充分性；不宣称 weakest condition 或最佳 cap。

| Narrative check family | 本路线使用方式与边界 |
| --- | --- |
| Arithmetic / representation | 实际 signed I64 comparisons 后才捕获到 I32；接受给精确 count 对应。不是任意 no-overflow condition synthesizer。 |
| Ranges / footprints | Checked affine footprints 与当前 count 建立 reached-point address resolution。Bounds 不单独证明 load/store permission。 |
| Memory separation | 实际 globals 的 block separation 生产 nonalias；本族没有新增 runtime alias test。 |
| Value / observation preservation | 既有 stores 的 frame 定律保持该 global header；没有运行 zero-RMW 或一般 overlap 检查。 |
| Control / conditional observation | 原 source test 许可 header read，range refusal 执行 literal fallback；公开空出口只改到达的 controls。 |

检查从 actual entry 读取 header，只写 fresh private cache/flag，保持 memory、
公开 temps 和 trace。接受运输 source/model 到 checked entry；拒绝运输原
fallback。这是有 private effects 的条件，不能当成完整 state 不变的 readonly
predicate，也不能只将两个 predicates 用 AND／OR 拼接。
继续用 [guard library](verified-guard-library.md) 的 requires、accepted、refused、
effects、producer 和 scope 格式；此扩展不增加 universal assumption extractor。

## 拒绝也会影响后续 pass 的资源

第一次 compiler 成功安装两例，但 legacy affine `matmul` 回归没有安装。
首轮测试同时请求 tiling；将 legacy 配置切为 tiling disabled 后仍失败。
代码核对发现，两个新 tiling passes 对空 candidate table 仍调用旧 table
installation，后者向函数追加 private temps。这会与旧 matmul route 的固定
private pool 冲突；后续 checker 正确拒绝，但所需优化丢失。

保留两轮失败，新增
[InitializedDoubleTiledStableCompiler.v](../prototype/interface/InitializedDoubleTiledStableCompiler.v)。
它对空表返回原 program；非空表消费已有 soundness 与 installation 定理。
两类 tiling 后再运行既有 affine routes，仍在每步重算 actual scope/resources。
这项改动属于 language/compiler 的安装组织，不是 kernel、host 定律或新的
source/candidate 语义假设。旧成功 sources、proof objects 与 native build 保留。

证明链共四模块 427 行、11 个审计端点、1 closed、502 reachable sources；
最多使用原有 42 globals，没有新增公理。前三模块的初始 317 行／7 端点
checkpoint 也保留。最终入口为
`InitializedDoubleTiledStableCompiler.compile_selected_initialized_tiled_stable_program`。

## 验收与尚未完成的目标

[摘要](initialized-double-tiling.json)绑定 proof、两个 native builds、原配置、
contexts、public exits、实际 assembly branch observations 和失败记录。
摘要共18份reports、16,767 bindings。最终 build 的验收包括两原例十配置、20 context、7 public／legacy、旧
`mvt`／`matmul-seq` 十配置与六次未改汇编的 branch 观测。
正值／零值进入候选，负值进入原 fallback；公开控制值与 GCC 一致。
多个 marked 独立安装，identical unmarked 排除，改名／改维度接受，类型／
资源不符拒绝。Debugger sandbox 的 ptrace 拒绝和两轮 mode-list 参数错误也保留，
后者将逗号分隔列表误传成一个 mode；正确的空格分隔后继通过同一原输入检查。

前一 reindexed build 的完整 62 原例＋2 adaptations 则是另一份明确范围的
证据：59 raw 与2 adapted native matches，原 corcol3／pca frontend refusals，
polynomial 编译 600.102 秒超时，9/62 原例安装22处。48 个已编译 raw inputs
未调用 tiling phase；tce／tricky3 调用但没有安装。Polynomial 的 Pluto 输出与
witness 已保存，但 raw Loop 未生成；具体慢阶段仍待定位。它不算安全回退或
成功编译。单一配置或 native match 不算完整 sequential 功能支持。

Tce 的定向后继在初始 initialized native build 上使用32 private temps、
十轴 witness search，四处候选安装并匹配原 GCC；编译236.467秒，仅为诊断。
六轴默认策略仍未修复，最终资源修复 build 尚未完整重跑 corpus；不同 builds
的安装数不合并成一份最新完整结果。测试部分并行运行，没有 controlled cost、
profitability 或单独 guard cost 结论。

下一顺序是 automatic resource/witness proposal、polynomial 的逐阶段定位、
实际非零／inclusive／多 bound source structures，以及 ISS／其余 sequential
phases。每条扩展同步 actual source、condition、candidate、出口和 Csem→Asm。
完整原 corpus、BT、LLVM／SPEC、larger tiers、条件接受域与完整调用成本仍是
必需验收；本阶段不完成整个 goal。
