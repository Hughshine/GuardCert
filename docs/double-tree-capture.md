# 按路径生成的整树 capture：源许可、接受事实与 fallback

本后继消费 [整树对应服务](double-tree-correspondence.md) 的 raw observer frame，
从 checked source tree **生成实际 Clight preparation statement**，证明读取许可、
检查执行、memory/private frame、接受后活动 header words 与 I64 bound ranges。
原 fusion1、multi-stmt-stencil-seq、tricky3 的冻结 Clight 已实例化 preparation
及原 source replay 定理。这个阶段尚未把整树优化安装进完整 compiler。

## 生成什么代码

`double_tree_capture_prepare tree cache flag lower upper` 先把 deduplicated header
对应的 private caches 设为 I32 零，再把 flag 设为真，随后遍历原树一次：

- Skip／真实 IEEE assignment 不生成检查；原计算留在 fallback／candidate 中。
- Sequence 按原先后顺序检查两个 subtree；flag 为假时 range 不再读取 header。
- Range 读取原 I64 global header，用所配置 signed I32 interval 检查并缓存。
  只有 flag 仍为真且 `start < (long)cache - offset` 时，才检查 child。
- 检查不执行原 assignments／循环，不写原 iterator 或 memory，只写 caches／flag。

例如 `for (i=0; i<N; ++i) for (j=1; j<M; ++j) ...`：先检查／缓存 N；
N=0 时不读 M。原路径中的某个 header 被拒绝后，child 及后续 sibling
header 都不再读取。所有 private cache slots 已初始化；未到达 header 的
零值不代表其实际值，也不自动建立该 header 的 load receipt。

当前实现每遇到一个 reached range 都重新 capture 其 header。共享 N 的
siblings 保留同一个 cache 名，但有重复读取；尚未实现 OLO compact condition
推导或 guard 公共子式消除。这里接受 raw N 在 I32 内，因此 I32 offset 的
`N-c` 在 I64 中无回绕；`N-c` 本身仍可能超出 I32，candidate machine-domain
检查必须单独处理。

## 证明接口和责任

| 服务 | Requires／实际生产者 | 已证明的 Ensures |
| --- | --- | --- |
| `double_tree_range_first_load` | Checked child、实际 global binding、原 range 有限正常执行；language 从原首次比较取得许可 | 实际 Mint64 input load；实际比较为真才提供 first child execution。既不要求接受，也不要求数学 point resolution。 |
| `double_tree_header_loads_after_source` | Checked subtree、globals／scope、enclosing write exclusions 和原 completed execution | Observer loads 从 source prefix 之后运输到 guard memory；observer 不必是该 prefix 自身使用的 header。 |
| `double_tree_capture_source_licensed` | 上述语言／静态证据、源与 guard 的 observer-load equality、profile limits、入口 flag | 递归构造整个 emitted check 的 receipt。Source execution 只在证明中使用，runtime 不预执行 source。 |
| `double_tree_capture_receipt_execution` | Receipt；flag 不与任何 cache 重合 | 实际 generated Clight 有限正常执行，trace E0，memory 不变；只写 private caches／flag。 |
| `double_tree_capture_accepted_headers` | Receipt 且最终 flag 为真 | 原模型活动路径上的实际 header words，以及活动 ranges 的 I64 上界范围；无须预读未到达 header。 |
| `checked_double_tree_capture_prepare` | Checked original source、language/site globals／scope、配置区间、private freshness、源 execution | 完整初始化＋capture 的实际执行；public temp frame；从 prepared entry 重放原 source，final memory 与 public exit 相同。Decoder 自动闭合 enclosing header-write exclusions。 |

Framework kernel／host laws 没有变化。Language 负责真实 Clight 求值、源读取
许可、raw Mem effects、private/public state 运输；domain 负责 tree／profiles
及 accepted arithmetic facts；site／allocator 必须实际生产 scope、interval
有效性和私有标识 freshness。C 使用者不提供逐 leaf 执行等价 callback。

接受事实使用一个 total proof valuation：实际已定义的 header load 取其 signed
值，其余 slots 取零。这个逻辑函数不在 emitted code 求值；定理只为活动
header 提供实际 load receipt。最终 caches 与共享 parameter vector 的对应
尚未证明；这需要 allocator injectivity 与重复 capture 的同值保持。

## 证据和限制

八个新模块均按冻结 attempt 编译；[portable audit](double-tree-capture.json)
记录端点、继承 globals、依赖和全部成功／失败编译。新 original-source
probe 复用三个例子的原 Original.v／Probe.v；不重新 frontend export、不修改
IEEE arithmetic，也不把这些 proof instances 计为 native optimization coverage。

Boundary proofs 检查 negative start、negative/offset empty interval、I64 widened
bound、空 outer 的实际 capture 不要求 child load，以及一次 refusal 后任意
later subtree 不读取 header。安全及 replay 定理依赖原有限正常 execution；
它们不另证任意入口可终止、divergence preservation 或 source 的无 UB。
原独立 strict progress 服务仍需在安装时另行消费。

当前 bound 家族是 global N 或 N-c，literal signed I32 start；不覆盖 arbitrary
ancestor-dependent bounds、一般 affine multiplication 或 inclusive comparisons。
它们仍是完整目标中的功能差距，不是缩小后的验收范围。

## 紧接着需要实际消费的义务

1. 将 accepted receipts、初始化及 cache allocator 接成准确的 shared parameter
   vector；闭合 actual leaf point resolution 和候选所需机器范围，不能将调用
   前读取许可建立在接受后的事实之上。
2. 在同一个 whole-region factory 消费 source/Loop bridge、实际 phases、最终
   candidate validation 与 lowering，恢复 public exits。
3. 安装到当前 intermediate program 的 host，再接同一原 Csyntax 输入的
   Csem→Asm backward simulation；新原例要观察有用接受及正确 fallback。
4. 继续 OLO compact condition 推导、其余原 source／sequential configurations，
   并分别报告 guard work／code size、接受域与 complete-call costs。
