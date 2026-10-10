# 下一项 domain 接口：一源多 piece 的执行对应

后继[动作／参数／执行服务](piece-actions-and-execution.md)已证明 typed action、
参数前缀、retimed timestamp、有限 piece 选择，以及 retained phase 的模型 forward
执行和已成立参数事实下的域 restriction iff。实际原 fusion2 的13项动作／参数
和两次 retimed-to-actual 依赖检查通过，但完整 point isomorphism／actual Loop／
progress／安装仍在推进；下文是接口设计与剩余验收，不是完成声明。

这是基于原 `fusion2` scheduler/codegen receipts 的实施设计。新的
[域／坐标服务](piece-domain-services.md)已实现覆盖、互斥和唯一 instance 对应，
尚未接动作、参数前缀、次序及真实执行桥。它位于 [narrative](topdown/paper-narrative.md) 的 optimizer/domain 层，
不改变语言无关 kernel，也不把数学 domain 事实作为 C 使用者的 callbacks。
当前证据与接线见 [参数特化](parameter-specialization.md)。

## 实际输入要求什么

Source Loop 有两个 instructions：写 A，以及读取 A 后写 B。新的整体 tiled
candidate 成功提取七个 pieces，既包含普通点域，也包含边界／单点片段；各片段
深度和表达的坐标不同。七个静态 pieces 并不意味着每个 source instance 应
执行七次。

当前 [positional attachment](../adapters/compcert-memory/GuardMemoryDoubleExtractedTiling.v)
按三个列表逐项连接，在 source、candidate、witness 同时为空时才成功。
[最终 checker](../adapters/compcert-memory/GuardMemoryDoubleShiftedTiling.v) 的
normalization、reindex 和 shift 都保持 instruction 列表长度。因此两源语句与
七候选 pieces 无法通过该接口。单纯放宽长度要求没有执行正确性依据。

## 提案的数据边界

不受信任的 optimizer／adapter 应提出以下数据，而不是直接提出一个语义公理：

| 数据 | 用途 |
| --- | --- |
| 每个 candidate piece 的 source statement id | 多个 pieces 可以对应同一源语句 |
| Piece domain 与适用 parameter 条件 | 描述该片段真正到达的整数 instances，包括可证明为空的片段 |
| 从 candidate 坐标到 source point 的映射 | 连接 point、tile、偏移或 peeled 边界坐标 |
| 反向选择／覆盖见证 | 给每个 source instance 找到唯一实际 candidate instance |
| Instruction／argument 对应 | 证明同一 source 动作在映射点执行，不能只匹配数组名 |
| 实际 schedule 与 transformation witness | 连接已检查的调度／分块 phase，保证所提案的数据描述真实候选 |

不能把每个 piece 都塞进一对一 tiling witness 后忽略其他 piece。一个被证明
为空的 piece 可以不贡献执行，但“提出一个空域”必须被验证。Tiling/link 域中
整数 floor 的唯一性也需要证明；rational scaled projection 并不自动给出它。

## 必须产出的条件执行证书

在已认证的 model／entry facts A 下，domain checker／库需要建立：

1. **有效点对应与精确覆盖。** 每个实际 candidate instance 映射到一个有效
   source instance；每个 source instance 有唯一 candidate instance。覆盖与
   互斥共同排除漏执行、额外执行和重复写入，包括不同静态 pieces 之间的重叠。
2. **动作对应。** 相应实际 instructions 的参数、读写位置和值语义一致；point
   对应不能改变 IEEE 运算、内存权限或可见 effects 的含义。
3. **次序正确。** 表示变换若保持已验证 schedule，可复用 timestamp 保持的
   point isomorphism。原始 schedule 到新 schedule 的重排另由实际依赖验证及
   可交换性证明承担，不能要求 source 与优化后 candidate 的 timestamps 原样相等。
4. **实际 Loop 执行及适用 progress。** 将 instance 结论接到 extracted source
   和 generated candidate 的实际有限执行。Backward codegen correctness 不能
   直接称为 source 到 candidate 的 forward 执行 theorem；仅有集合覆盖也不能
   自动排除目标执行卡住。现有 Clight host 需要的独立 progress 继续交付。

这里需要复用并扩展已有基础：
[PolCertExtractorCoverage](../theories/PolCertExtractorCoverage.v) 的实际 trace
coverage，
[PolCertCandidateRepresentation](../theories/PolCertCandidateRepresentation.v) 的
`memory_point_isomorphism`／execution，以及已有调度、tiling 和 ISS 语义。
Point isomorphism 已包含有效点、双向逆、timestamp 与逐动作 execution；新的
piece witness 要有可检查的生产过程，不能要求普通源用户填入这份语义 record。
ISS 的 parent mapping 可以提供复用参照，但其既有 cut/payload/shape 前提不能
未经证明套到任意 peeled、不同深度的 codegen pieces。

## 接回 GuardCert 的位置

```
actual checked source Clight -> source Loop
  -> checked polyhedral phases and scheduled model
  -> checked piece/coordinate correspondence -> actual candidate Loop
  -> existing safe machine lowering and public-exit restoration
  -> existing region/site contract and actual-current-program installation
  -> CompCert backend
```

Piece 库负责中间的 C_opt 证据。它消费 A，而 A 的来源继续逐项记录为 static
check、runtime accepted facts 或语义证明中的 source execution。若需要新增动态
前提，domain 必须提供 `B => A`，语言条件服务提供 safe `G accepts => B` 及
accepted/refused entry transport；source execution 不是运行时先执行原循环。

语言／host 仍负责 actual guard/choice semantics、安全读取与算术、private/public
frame、控制／progress、合法安装和 backend。即使 source/candidate 的数学
addresses 对应，candidate 为计算 tile bounds 或 guards 而引入的机器中间运算
也必须有安全证明。数学 piece checker 不代替这条义务。

Kernel 只消费最终 conditional／guard／entry certificates，推出局部 guarded
correctness；既有 host 把它安装到完整程序。Repeated passes 继续使用实际当前
程序的 site evidence，再组合有限序列。

## 第一项验收

使用原 `fusion2` 的整体 tiled 提案，保留七 pieces、源数值类型与数组计算及
实际 phase receipts，连接到同一 Csem-to-Asm 路径。必须看到整体候选通过最终
checker 并实际安装；两个 nests 的独立分块或完整输出匹配都不完成此项。
随后对实际 source／candidate／guard 接受路径和成本分别评估，再拓展 general
pieces／ISS。这个验收不收缩 PolCert 顺序能力与 CGO17 的整体目标。
