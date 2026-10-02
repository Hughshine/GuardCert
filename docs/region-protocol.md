# 由语言实例提供片段内部进展

`SilentRegionProtocol.v` 为片段替换增加了一个不依赖 Clight 的内部执行接口。核心只看不透明的状态、事件、出口和小步关系；语言提供 cursor，说明当前停在哪个内部步骤。它与性质维度／条件合成接口互补：性质接口证明候选在什么条件下可用，这个接口证明宿主可以等待原片段完成，而不会丢失源程序的无限执行。

## 语言提供什么

| 字段 | 证明义务 |
| --- | --- |
| `cursor_state`、`cursor_step_sound` | cursor 的每一步对应真实源语言小步，并且无事件。 |
| `cursor_step_closed` | 未完成 cursor 上的每个实际源小步都能恢复成下一个 cursor；不能只挑选有利的执行。 |
| `cursor_rank`、`cursor_step_decreases` | 每个内部小步严格降低自然数度量。度量可以依赖运行时状态。 |
| `cursor_done`、`cursor_done_state` | 完成时得到语言自己的出口数据和实际退出状态。 |
| `cursor_completion`、`cursor_completion_prepend` | 语言定义剩余执行的含义，并证明一次内部推进能向入口重建这个执行。 |
| `protocol_entry` | 实际入口对应初始 cursor；初始 cursor 的完成性质能还原为作者接口消费的源执行。 |

核心证明 `cursor_path_bound`、`cursor_cannot_diverge` 和 `completed_entry`。它们均闭合于全局上下文，没有内置整数、内存、AST 或循环规则，也没有承诺未发生卡住的执行一定存在。语言实例仍须证明上述义务。

## 两个已编译的 Clight 实例

`ClightRegionProtocol.v` 覆盖 skip、assign、set、sequence 和 if。cursor 保存当前语句、片段内部 continuation、temps 和 memory；度量来自语法工作量。现有 `ClightRegionRewriteProof.advance_region` 已通过通用字段消费其小步覆盖和下降性质，继续获得完整 Clight 程序模拟。因此这个实例实际用于现有 C→Asm 路径。

`ClightCountedProtocol.v` 覆盖 `counted_loop iterator bound body`：signed32 的 `iterator < bound`，每轮增加 1，body 由 skip、普通赋值、sequence 和 if 构成，不写 temporaries。所有实际小步，包括条件选择、body 内部步骤、递增、回到循环头和 break，都被覆盖。

循环度量结合剩余迭代数与 body 的语法工作量。`counter_increment_distance` 证明进入 body 后递增不会回绕：当前计数器小于 signed32 上界，增加 1 仍可由机器整数精确表示。输入并不要求预先全部是 Vint；有定义的真条件建立本轮类型与范围证据，无定义条件无法产生继续执行的小步。

`counted_region_completed` 将完成的 cursor 路径还原为真实 `exec_stmt`，并给出源小步数量上界。`ClightCountedProtocolExamples.v` 证明零次迭代时无需执行或验证 body 的访存，源循环保持入口 temps 和 memory；另核对跨零的计数距离与 signed32 最大值边界。

这些 Clight 定理继承上游语义假设。`scripts/audit_region_protocol.py` 将它们连同当前宿主定理的假设与完整 CompCert 基线比较，并记录源码哈希。

## 完整程序宿主已经消费循环协议

`region_progress source` 是 Clight 提供的语言接口。除通用协议外，它给出真实入口、正常出口、状态形状、无 label 以及在符号／复合类型布局保持时的执行运输。`ClightAdaptiveRegionProof.transform_program_correct2` 使用显式自然数模拟索引，在入口选择运行时度量，并在外围继续覆盖调用、外部事件、循环、switch 和 goto。有限片段和严格计数循环无需更改同一宿主证明。

`ClightProgressClassifier.v` 的语法提议只决定尝试什么模型。完整 AST 相等性检查核对有符号类型、计数器、上界、递增、属性和 body 限制；证明 `progress_supported_sound` 提供真正的语言协议。

`ClightZeroTrip.v` 的 `zero_trip_rule` 将“入口比较为假”编码为性质原子，通过共享条件合成生成 `if (iterator < bound) original_loop else skip`。原子检查的正、负证据、lowering 和局部结果均连接真实 Clight。它只读取计数器和上界；检查域由有定义的源循环入口条件建立，因此不要求预先访问 body 数据。

`AdaptiveRegionCompiler.compile_progress_regions_correct` 给出实际 Csem→Asm backward simulation；默认提取入口已经切换到该函数。可选 `PolCertStoreNative.compile` 也复用新宿主，已有 CInstr 调度规则的局部契约不变。

## 仍待连接的边界

当前整个循环规则接受精确的 `counted_loop` AST。CompCert 的真实 C 前端为 `for` 添加 `Ssequence`／`Sskip` 包装；尚未机械化这些包装的执行协议与识别，因此目前没有声称原生 C 的整个循环已实际命中。

这个进展接口也不承担 guard 的安全性证明。源循环零次迭代时，body 没有读取的数据不能被 guard 无条件提前读取；语言适配器必须证明检查域，或通过短路与检查位置避免新增非法访问。可能因回绕而无限运行的原循环还需要回退锁步模拟等机制；它们不属于这个首个严格计数实例。

private temporary/live frame、循环出口修复和实际 PolOpt 的候选进展仍是独立义务。严格计数循环的整程序区域替换已有完整 C→Asm 定理；实际 PolOpt 的多面体循环优化还没有获得这条完整链。
