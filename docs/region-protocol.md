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

## 仍待连接的边界

循环实例还没有进入整程序区域选择器。当前整程序宿主仍只选择自身不含循环的有限片段。其模拟使用源状态的语法度量；数据相关循环需要改为显式模拟索引，才能在进入区域时选择运行时度量，而在外围正常执行时继续处理任意调用、循环和 goto。

这个进展接口也不承担 guard 的安全性证明。源循环零次迭代时，body 没有读取的数据不能被 guard 无条件提前读取；语言适配器必须证明检查域，或通过短路与检查位置避免新增非法访问。可能因回绕而无限运行的原循环还需要回退锁步模拟等机制；它们不属于这个首个严格计数实例。

private temporary/live frame、循环出口修复和实际 PolOpt 的候选进展仍是独立义务。此处没有声称内部循环替换或多面体优化已经获得完整 C→Asm 定理。
