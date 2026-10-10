# 动态 loaded-bound 的 piece factory 与完整程序接线

本页面向实现新的优化族或 guard 服务的作者。框架消费局部证书；本实例由
domain factory 和语言 host 自动生产、组合适用证据。支持族的 C 使用者提交
`#pragma scop` 标注、phase／tile 选项及 profile，不填写语义 callbacks。

## 新证明的接口与责任

新 producer 继续使用[分片 factory](piece-factory.md)的 data-only `adapt/propose`。
它提取实际 source，保留 checked phase 模型，提取实际 adapted candidate，
消费覆盖、互斥、坐标、typed actions 和实际依赖 checker。适配器或提案拒绝则
不安装；提案的诊断输出不能授权安装。没有新增 kernel 或语言 host law。

| 责任 | 本次实际消费的证据 |
| --- | --- |
| Domain `C_opt` | `checked_double_piece_prepared_loop_at`：实际 source Loop 在同 captured parameters 下经 phase、piece checker 到实际 candidate Loop；另复用已证明的有限 Loop iff。 |
| Domain／language 的 `C_derive` 接线 | 已接受参数区间、checked source shape、静态 footprint／layout 和原源到模型的对应。数学模型参数与 Loop 环境的逆序由已有 guard/extractor 证明处理。 |
| Language `C_guard` | 既有 path-sensitive source-licensed capture、安全 signed-I64 读取／I32 cache、接受 facts、未到达 cache 的 zero 初始化、private/public frame 和拒绝后原源 replay。 |
| Language／factory 的具体 choice | `checked_double_piece_guarded_execution` 从原 Clight 的 silent normal completion 构造实际 preparation、candidate 或 fallback、公开出口执行，保持最终 memory 与选定 live temps。 |
| Site／whole-program host | 实际 AST、scope、typed private pool、独立原源 progress 和 projected region contract，接当前 intermediate program，再经 CompCert backend。 |

这些标签记录证据来源，不要求作者手填四份 record。首次实例化语言的作者证明
host 定律；增加优化族的作者交付其源／模型、前提和候选证明或适用 checker。
每个 rewrite site 的 factory 负责 discharge 实例前提。

四个新模块413行、九个审计端点，最多42项既有 globals，无新增 globals。
[证明摘要](dynamic-piece-factory.json)记录所有端点及实际编译尝试。
`DoublePieceTreeFactory.check_double_piece_tree_region_sound` 交付 projected region
contract；`PieceCombinedDoubleCompiler.compile_selected_piece_combined_double_program_correct`
交付 Csem→Asm backward simulation。独立的 local Loop iff 不推广为任意 Clight
divergence 的双向等价。

新 combined pass 首先执行 selected literal normalization，再尝试动态 piece
安装，随后对实际当前输出调用已有 literal piece 和 typed passes。每一项安装
消费其当前程序的证据，已有全程序定理组合正确性；不能复用过期 site 证据。

## 动态 guard 能表达什么

这里的原 source bounds 是实际 global signed-long-long 表达式，私有缓存和 flag
由已证明 preparation 写入。公共状态不变并不意味着整个 guard 没有 private
effects。首次读取许可来自原源到达的比较及已证明 observation transport；
某个成功 stability／range test 不反向许可更早的 speculative load。

空 outer 不读取 child header，未到达槽保持 zero；接受的参数 facts 因而描述
实际 cache valuation，不能被误写成关于所有原 globals 的无条件范围断言。
拒绝只表示这个充分条件未接受，不证明语义前提为假。它必须能从 guard 出口
执行原 source，并恢复其公开控制出口。

没有为每个模型 premise 发射一个独立 test。Profile、footprint 和条件式 capture
合起来建立适用前提。现有 preparation 的工作随 source tree 语法增长，没有
新增逐点 runtime scan；共享 headers 的重复 capture 尚未消除。

## 首次 native 回放与仍开放的分块缺口

首次 native 编译器消费上述真实 root、guard 和 checker。fusion2 的披露 adaptation
保留原 A[105][105]／B[104][104] 及 IEEE kernel，以独立 argv `N/M` 替换两个
nests 的 bounds，公开 iterators 初始为17／23。三个配置各编译一次，再运行41组
输入，包括 tile 边界、outside-profile、负数／空域和 inactive-child 的 I64 极值。
123个完整输出及公开控制出口均匹配该 variant 的 GCC reference。

Untiled 的六片整体候选安装。Tiled 整体候选被 floor-membership adapter 拒绝，
后续既有路径保持正确输出。这次回放的整体状态为 **rejected**，保存在
`build/dynamic-piece-factory/runtime-attempts/symbolic-v1/rejection.json`；不得用输出
匹配或后续单 nest 分块代替请求的整体 tiled 变换。

第二次尝试在不受信任 adapter 中将 modulo-zero 边界分片改为有限 quotient 坐标，
已使 floor／Mod 条件进入已有 affine extractor，得到八个实际 candidate pieces。
Coverage proposer 随后报告 `uncovered path` 并返回 None，所以总 piece-model
checker 尚未运行，整体 tiled 候选仍未安装。三配置的123个完整输出及公开出口
再次匹配，同一 variant／runtime inputs 均保持。两次 build 和 replay 使用独立
attempt，拒绝记录均保留；此适配算法没有增加语义假设或授权安装。

同首次 dynamic/literal compiler 的[完整语料摘要](dynamic-piece-factory-corpus.json)
另记录62原例、两披露 adaptations、192配置的回归及 focused Clight shapes。
回归输出匹配不是全语料请求变换的支持率，也不关闭动态 tiled 的上述缺口。

当前具体缺口转为八片候选的覆盖证书：需要诊断 source point／tile 坐标及覆盖
搜索，再交给实际 total checker；抽样点覆盖也不是 coverage 的证明。

## Untiled 的实际接受／回退和条件式读取

[运行观察](dynamic-piece-runtime-observation.json)使用第一份 compiler 生成的
未改 assembly/binary。六次硬件写观察采样最后一个 A 点和第一个 B 点：
(100,100) 时 untiled target 先写 B、后写 A；(101,100) 和 (100,101) 超出 profile
时，target 恢复原 source 的 A、B 次序。每次同时核对完整 variant 输出。
这只采样两个 store 位置，不直接读取 private guard flag。

另外八次 hardware read 观察从实际 argv-to-M store 后开始。Source 与 target
在 (0,I64_MAX)、(0,I64_MIN)、(-1,I64_MAX) 都不读取 child M；(2,3) 的 source
读取16次、target 两次。14次完整输出全部匹配。无调试类型时 M 符号解析失败的
首 observer 保留；后继从实际 store 指令取得地址，没有修改目标程序。
Globals 均有效分配，所以这不是 invalid-child-pointer 测试，也不提供受控成本。
[阶段摘要](dynamic-piece-results.json)绑定全部证明、运行、失败及语料报告。

本例的数组／header 分离由支持的 global layout 和 scope 证据建立，不代表任意
pointer alias 的动态检查已经覆盖。后续验收仍需同一个 independent `N/M` 源的
实际 tiled 安装及完整调用成本。
这不是 CGO17 的通用 compact 条件推导完成：有用的 `B⇒A`、safe `G accepts⇒B`、
entry transport、alias／overflow 和原程序 contexts／tiers 仍分别验收。
