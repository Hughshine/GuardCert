# 整树参数、footprint 与当前程序安装

整树路径现在有一个实际消费检查结果的 region factory，以及对应的
`Csem → Asm` backward simulation。它把前序 source/Loop 定理的动态前提
闭合在编译器内部：C 使用者不再提供 header words、point resolution、参数
编码或局部执行对应证明。原始 C 的选择方式仍是 `#pragma scop` 标记。

这份记录描述 [proof-v1](../build/double-tree-model/proof-v1/report.json)
的证明 checkpoint。它不把源码识别、导出成功或泛化编译器 theorem 计作
原 benchmark 的优化安装。提取与 native 接受结果须另绑定实际 build 和 run。

## 实际接口与责任

| 交接 | 生产者及本次消费 |
| --- | --- |
| 原 Clight → tree | Domain decoder 核对完整 source 重建、叶 assignments、shared layouts、header declarations、ancestor counters 与 header write exclusions。 |
| source-defined execution → 可调用 capture | Language 使用实际到达的首次 comparison 和 raw effects；后部 header 的许可运输不依赖 accepted point facts。前序 capture receipt 已被本次 preparation theorem 消费。 |
| capture → 缓存参数 | Language 证明所有槽初始化为 I32 zero、private frame、同 header 的 recapture 同值；domain 证明 accepted active values 与原 header valuation 相同。 |
| profile/footprint → 模型事实 | Domain 的 signed affine box checker 使用原 starts、`upper(header)-offset` 及每个 leaf 的真实控制深度，推出 declared dimensions 内的数学下标；实际 language location theorem 推出 leaf resolution。 |
| source Loop → candidate Loop | 实际 extractor、OpenScop phase、affine/tiling validators 和 prepared codegen 生产提议。最后的 reindexed checker 验证将被安装的 adapted candidate，并在 capture 给出的 signed intervals 下提供 forward execution。 |
| candidate Loop → Clight | 既有 machine lowerer消费 typed cached parameters 和区间，实际检查表达式范围及 private counter资源；不要求用户断言候选无回绕。 |
| Clight candidate → region guarantee | 新执行证明串联 preparation、候选、准确 public-exit restore 与原 source fallback，保留 final memory 与 public temporaries。 |
| region guarantee → whole program | 既有 Clight host 消费独立 source progress、no-shadow globals、当前程序 scope 与 private pool；新完整 compiler 串联原 Csyntax 的 SimplExpr/SimplLocals 和 CompCert backend。 |

最小 language-independent kernel 与 host 定律保持原样。新增代码属于
CompCert language/domain library 与 optimizer instance，不是 kernel 新增的
通用 assumption extractor。`C_opt`、`C_derive`、`C_guard`、`C_host` 的划分
与 [narrative](topdown/paper-narrative.md) 一致；相应证明由具体服务消费，
不是给 C 用户增加四个 callback。

Factory `check_double_tree_region` 的策略输入是 phase、candidate adaptation、
tiling choices 和每个 header 的 lower/upper profiles。这些都是 untrusted
proposal data。Factory 自己从 typed private pool 分配 flag/caches，执行
profile、footprint、layout-span、resource 和最终 candidate 检查；任何静态
拒绝返回 `None`。运行时检查拒绝执行原片段。Profile 是充分条件，可以保守。

## 参数与条件的表达力

支持的 source tree 包含 skip、IEEE assignments、sequence 和 strict signed
ranges。Start 是 signed I32 literal；bound 是 global I64 header，可减去
signed I32 literal offset。Header 可以共享；叶节点可以位于不同深度。
当前 bounds 不依赖 ancestor iterator。原数据访问仍用 checked global tensor
layouts；pointer 参数及动态 alias 的既有实例不因此自动进入本次 tree factory。

最终参数向量按 deduplicated 原 header 顺序编码。接受只要求 reached paths
上的 header 精确对应，不要求读取未到达 child。候选 lowerer 仍需要全部
parameter slots 的类型和区间，因此未读取槽初始化为零，区间扩为
`[min(0,lower), max(0,upper)]`。这不会把不活动路径上的零解释成原 header 值。
静态 resource checker 排除 cache collision、flag collision 和 public-counter
写入冲突；重复读取同一个 header 则证明得到相同的缓存值。

Footprint checker 遍历 source shape，在非空 envelope 中传播半开区间；signed
coefficient 的正负决定极值端点。它证明数学下标落在声明的 tensor dimensions，
再消费实际地址解析定理。它不单独证明 `Mem` allocation/permission，也不
授权提前读取 child header。I64-to-I32 capture 在截断前检查原值；公共 bound
运算和 I32 candidate arithmetic 的保证分别来自不同证明。

## 一个实际流程

原 `fusion1` 的 marked region 有两个循环：从 `1` 到 `N-2`，再从 `2` 到
`N-3`，包含原 `0.33` 浮点表达式。Decoder保留两段 source、各自控制范围和
真实 IEEE assignments，抽出一个共享 `N` 参数。

Preparation 初始化一个 cache 与 flag，读取 first comparison 许可的 `N`；
接受 profile 后用 widened cache 运算决定 child。第二段仍按原 sequence
到达并 recapture 同一 `N`。Global header exclusions 与原 raw effects保证
原 source stores 不改变它，cache frame 保证最终参数还是同一个原值。
Footprint checker 分别检查两段的真实 start/offset，而不是把它们改成从零
开始的同一个 rectangular nest。

如果实际 scheduling/codegen 与最终 candidate 检查返回成功，执行候选并
恢复原 source 的公开 counter exits；否则保留或执行原片段。`double_tree_region_contract`
把这个执行结论交给既有 selected host；`compile_selected_double_tree_program_correct`
给出完整 Csem-to-Asm backward simulation。两个 theorem 均已编译；某个具体
source 能否优化还要实际运行 phase、codegen、最后的 validator 和 machine lowerer。

## 已验证的范围

十五个新 Rocq modules 共 1,382 行，查询 50 个 endpoints，24 个 closed。
完整 compiler endpoint 最多使用原 baseline 的 42 个 globals，没有新增全局
假设。Audit 追踪 556 个 reachable sources，绑定 10,311 个文件，保存 36 次
module 编译尝试：15 成功、21 失败。成功源码与对象、父 checkpoint、每次
失败的输入和日志保持冻结。

`fusion1`、`multi-stmt-stencil-seq`、`tricky3` 复用原冻结 Clight，分别实例化
`[0,16]` 下的非空 footprint 检查和 preparation/source-model theorem。首
probe 因漏直接 import 失败，后继三例均通过；不改计算或 IEEE types。
另一独立 probe 在 `[0,4096]` 下实际计算 profile、footprint、layout span、
progress root、Loop extraction 和 OpenScop export，三例六项全部通过。
该 probe 未运行 external phase 或 candidate codegen。

机器可读摘要是 [double-tree-model.json](double-tree-model.json)。详细证据见
[model instances](../build/double-tree-model/source-attempts/source-v2/report.json)
和 [pipeline request probes](../build/double-tree-model/pipeline-attempts/request-v1/report.json)。

## 剩余验收

下一项是关闭以下 native attempts 暴露的整段拒绝，在原 marked sources 上
保留完整 candidate、各阶段验证结果、guard/fallback 和 native 输出。已证明的
factory 与 whole-program endpoint 不能替代整段优化验收。之后对照完整 PolCert
sequential configurations 和 CGO17/OLO 原程序、输入 tiers、接受域和完整成本。

Profiles 仍由策略提出；没有通用 projection/minimal condition 算法。
Shared header 仍逐 reached range recapture。压缩检查成本、作者证明负担、
更多 source/target domains、ISS、diamond/two-level tiling、unroll/jam 等目标
继续开放；本 proof checkpoint 不增加 native source coverage 或 speedup 结论。

## 独立 native 后续结果与拒绝边界

已提取并构建 `native-v2`，Driver 实际调用新的
`DoubleTreeSelectedCompiler.compile_selected_double_tree_program`；原编译器 root
仅为共享 native helper 提供 extraction dependencies。首 `native-v1` 因漏
这个 dependency root 构建失败，输入、日志与 rejection 保留。新 ML policy
只提出 profiles、affine enclosing bounds、membership 和坐标调整；实际
extracted factory仍检查最后的完整候选。

[独立 native 摘要](double-tree-native.json)绑定 build、失败记录和
[original-v1](../build/double-tree-model/native-attempts/original-v1/report.json)。
三个原始程序分别在 unmarked、请求 untiled、请求 tiled 下编译并完整执行，
9/9 输出匹配同源 GCC 参考；原 IEEE types 与计算不改。Unmarked 全部零安装、
零 phase calls。Marked 两个配置各报告 fusion1 的2、multi-stmt-stencil-seq
的5、tricky3的2个 sites。

**这些不是三个完整 marked trees 的优化成功。** 检查 emitted Clight 后，
前两例仍分别安装原兄弟 ranges；tricky3保留原 outer，改写内部两个 child
ranges。Whole fusion1 的 fused proposal与whole tricky3的不同深度proposal
均达到 adaptation并保存真实生成Loop，未安装该whole candidate；目前缺少
最终checker与machine-lowerer的独立拒绝receipt。Whole stencil在phase output
后、adaptation前拒绝，需要区分affine validation、tiling import/validation与
prepared codegen。当前trace不足以把这些进一步归因，不能猜测其原因。

因此本次交付的是实际整树compiler路径及其子region安装，整段fusion/优化
验收仍未完成。请求 tiled也不自动证明实际tiling；现有生成产物中的零tile
links与仅改变schedule常数的结果不计作有用变换。没有重新跑完整62例计算
aggregate coverage，没有观察actualguard分支，也没有新speedup或成本结论。
