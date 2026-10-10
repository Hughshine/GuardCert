# 非零 strict 区间、实际 bound capture 与共享参数模型

本 checkpoint 为原 `fusion1`／`multi-stmt-stencil-seq` 的共同 source blocker
补语言和 domain 服务：非零 I32 literal 起点、实际 I64 `N-c` 上界、空区间、
真实浮点 assignment，以及保留原始共享参数的 Loop 模型。九个新模块已经
编译并审计，固定数字及路径见[摘要](signed-range-source.json)。

**尚未安装这些源例的优化。** 新 tree／decoder、region factory、实际 phase／
candidate、entry/refusal transport 和完整 compiler 接线仍需完成。现有 native
compiler、22 原例／39 sites 的覆盖和成本记录保持；本轮没有重标这些证据。

## 源接口与严格区间

[GuardMemoryLongRangeSource.v](../adapters/compcert-memory/GuardMemoryLongRangeSource.v)
的 `memory_long_from_range_equivalence` 使用实际 initializer 和 condition。
在 header、body/model、frame 与 invariant 证据下，有限源执行对应
`Z.to_nat (upper-lower)` 次 body 执行，并保留真实 temporaries／memory。
`upper<lower` 的区间为空，原 initializer 仍执行。起点也可为负数。

[GuardMemoryDoubleRangeModel.v](../adapters/compcert-memory/GuardMemoryDoubleRangeModel.v)
把这一遍历连到实际 Loop semantics；对不写临时变量的 assignment，公开
iterator 出口为 `max(lower,upper)`，不是无条件 `upper` 或零。

Strict `<` 控制复用既有 `long_raw_loaded_framed_progress`：body 的独立 framed
progress 保持 iterator，真比较保证 increment 不越过 I64 最大值。新 arbitrary
initializer 的 raw progress 不借用 guard 接受或稳定上界的前提。该协议仍可
表示 stuck execution；它不是对任意输入的正常终止承诺。Inclusive 控制没有
借用此结果，回绕及相应 host 责任继续单独处理。

## Safe invocation 与接受后的事实

[GuardMemoryLongRangeHeader.v](../adapters/compcert-memory/GuardMemoryLongRangeHeader.v)
从有限正常源执行的首次比较得到实际 bound 的 `eval_expr` receipt，包括空域。
receipt 位于 initializer 之后；绑定或稳定性本身不提供首次读取许可。

[GuardMemoryLongRangeCaptureSource.v](../adapters/compcert-memory/GuardMemoryLongRangeCaptureSource.v)
检查 bound 不读取当前 iterator，并用 expression read footprint 将 receipt
运输回检查入口。`memory_long_offset_source_capture` 对实际 `N-c` 代码把这条
源许可、真实 header load、检查执行和接受事实连接起来。代码不在运行时先
执行原 source。

[GuardMemoryLongExpressionCapture.v](../adapters/compcert-memory/GuardMemoryLongExpressionCapture.v)
提供 `memory_long_expression_capture code cache flag lower upper`。它操作实际
readonly I64 expression，检查有符号闭区间，接受时写准确的 I32 cache，拒绝时
只写 false flag。入口必须提供 type 和安全求值许可。检查保持 memory，私有
cache／flag 的写入需由 site frame 排除在公开观察之外。它不是完整 state readonly。

`memory_long_expression_accept_spec` 给出接受的区间事实；
`memory_long_expression_accepted_i32` 证明负值也能准确转换，而不是沿用仅
适用于非负值的 unsigned/signed 相等推理。拒绝不表示所有语义前提的否定。

`long_sub_i32_accepted_no_wrap` 是一个具体 `C_derive` 服务：若实际
`result = Int64.sub input (Int64.repr (Int.signed c))` 且 result 在 signed I32 内，
则 `signed(input)-signed(c)=signed(result)`，这次数学减法没有 I64 回绕。
它不推断任意仿射表达式的中间值安全。已证明反例：`(I64.min+1)*2` 回绕到
I32 可接受的 `2`；仅检查乘法结果不能得到对应的数学无回绕事实。

## 真实 assignment 与共享 N

[GuardMemoryDoubleSignedRangeSource.v](../adapters/compcert-memory/GuardMemoryDoubleSignedRangeSource.v)
的 `checked_double_signed_offset_source_model` 使用实际 assignment decoder 和
既有 IEEE／Mem bridge。它还要求 globals/scope、header load、counter freshness、
有符号控制范围与点位置 resolution。body 的 write symbol 与 header 不同，
实际 global-block/store 定理保持 header load；不是用数学 footprint 推断 `Mem` 权限。

[GuardMemoryDoubleAffineRangeModel.v](../adapters/compcert-memory/GuardMemoryDoubleAffineRangeModel.v)
与[共享 source theorem](../adapters/compcert-memory/GuardMemoryDoubleSharedHeaderRangeSource.v)
保留原参数 `N`，模型边界写为 `N-2`／`N-3`。不把二者变成独立自由参数，
为后续 sequence／fusion 保留相关性。证明也运输实际 frontend 的 skip prefixes。

模型参数目前是数学 signed I64 值；这不意味着任意原 `N` 可由 I32 backend
编码。接受 `N-c` 的 I32 结果，也不自动证明 `N` 自身在 I32 内。后续 factory
必须闭合原参数或重建参数的编码／区间、实际 candidate 与 continuation 证据。
本轮 source/model theorem 的 no-wrap 和点 resolution 仍是明确前提；没有把
“可由库提供”记为“已被新 factory 消费”。

| 责任方 | 已证明服务 | 仍需实际消费 |
| --- | --- | --- |
| Framework | 原证书组合和 repeated rewrite 边界保持 | 不负责推断 source arithmetic、构造 source tree 或 phase |
| Language | 初始化、首次比较许可、read-footprint transport、实际 capture、I32 cache、raw skip transport、strict progress、公开出口 | 新资源／scope checker、entry/refusal transport、机器 lowering 与 current-program host 接线 |
| Domain／优化实现者 | `N-c` 接受后的无回绕服务、真实浮点 point/model、共享参数 Loop 对应 | 保留原源树和共享 registry，闭合点范围及模型前提，运行 actual phase，验证最终 candidate |

这些是 language/domain 作者的接口；尚未让 C 用户使用新 source 族，也不要求
他们替代 factory 提供逐 site 语义 callbacks。此处没有新增 kernel／host 定律。

## 本 checkpoint 的证据与下一步

九模块共 919 行；42 queried endpoints 中 19 closed，最大继承六个既有 globals，
零新增全局假设。审计追踪 252 reachable sources，绑定 9,650 项，保留 20 次
proof attempts。首 audit wrapper 错误生成空 namespace import，失败目录及
修正后 `proof-v2` 分开保留。

十项 Rocq examples／lemmas 覆盖原 fusion1 两个区间、非零空域、负起点、负
cache、常见 offset、I64 subtraction overflow／underflow 拒绝、乘法反例，
以及矛盾 interval 的 false guard 和实际检查执行。没有 native 新优化、完整
Csem→Asm 新端点或新成本证据，不能据此声称原 fusion1 已覆盖。

下一项是完整 marked source tree，而不是只单独优化两个 loops 来替代 fusion：
递归处理 sequence 与不同深度 nodes，合并实际 instruction registries／effects，
保留共享 header parameters，闭合 path-sensitive capture 的安全读序和公开 exits。
随后同一 factory 消费 source/model、condition、实际 phase/final candidate、机器
lowering 与当前程序 host，接受／fallback 都进入完整 Csem→Asm。其余 OLO compact
条件、inclusive／更一般 affine 控制、sequential phases 和原 benchmark tiers 仍 active。
