# 本轮研究结论与实际证明边界

2026-10-02 用户澄清：PolCert 是功能与证明架构的参照，允许为 CompCert 必要地重实现表示、算法和接口。目标是基本多面体能力对齐，并通过统一的前提检查框架获得完整程序保证。本轮已进一步闭合动态矩形交换，以及 private temporary 宿主和保持顺序的分块路径，但一般仿射域、保序依赖验证与多维 tiling 仍不足以完成目标；后续按 [多面体接入验收](polcert-integration-target.md) 推进。此前把验收限定为必须调用现有 PolCert，是对要求的过度收窄。

框架可以不解释整数或内存，但不能省去语义契约。通用核使用语言实例提供的性质：检查证据、条件选择、执行运输、可交换性、frame、内部进展与出口对应。语言负责证明这些性质在自己的真实执行关系下成立。`if` 构造器是其中一项；它本身不足以把任意片段变换接到完整程序。

## 已运行的分工

| 接口 | 负责的内容 | 实际证据 |
| --- | --- | --- |
| `property_dimension` / `check_primitives` | 前提的语义解释、正负或 unknown 证据、可执行原语 | 算术、同地址读取、矩阵入口条件等 Clight 实例 |
| `compile_condition` | 真／假／unknown 控制流、短路与否定 | 语义无关定理闭合；Clight 降低到实际 if |
| `scheduling_model` / `check_schedule` | 不受信任点顺序、重数保持、每次交换的证据 | 提取 OCaml 测试 120 个排列；实际 CompCert store 实例 |
| 源解码／候选编码 | 点执行与真实语言片段之间的对应 | 源循环行序、候选列序或任意接受顺序的 Clight 展开 |
| `encoded_region_rule` | 检查域、安全条件、条件局部执行与出口关系 | 矩阵规则保存完整内存及所有 temporaries |
| `silent_protocol` / 区域宿主 | 所有源内部步骤、下降、完成重建、外围 continuation | 实际严格嵌套 Clight 循环、外围 goto／调用／循环 |
| 完整编译器定理 | 从完整 Csem 到 Asm 的行为保证 | 默认、参数化点顺序和动态矩形入口；假设与 CompCert 基线相同 |

用户或工具可以提交点序列，甚至故意提交错误序列。编译器先核对完整源 AST 与控制变量限制，再核对点顺序，最后生成候选与动态 guard。调度提案无需受信任；语言性质库与宿主适配需要证明。该点调度入口仍限定为固定 2×2 模板。另一个 [动态矩形入口](dynamic-rectangles.md) 已支持运行时边界及不同数组布局的内置循环交换，使用符号化域证明，不枚举运行时点。

## 条件需要从实际执行中获得可检查性

矩阵条件不是只把数学式 `i=0 ∧ n=2 ∧ m=2` 印成 C。外层零次执行可能根本不读 `m`；因此 guard 先检查 `i=0` 和 `n=2`，只有接受后才读 `m`。源执行恰好提供后一次读取的定义性。这一证明支持未初始化但不会被读取的内层边界例子。反过来，不能把 CompCert 的抽象 block、permission 或对象 extent 当作 C 程序能够查询的值。

overflow 前提也应绑定计算树及中间值。现有 widened checks 不要求 C 能读取硬件 overflow flag；引入 flag 或 checked instruction 可以是另一个语言实例。已有动态仿射合成把选择的无溢出前提编成检查，但一般“给定任意候选，自动发现前提”的算法尚未实现。

## 对多面体方向的判断

直接 CompCert 路线已闭合两个候选族：运行时维度检查后的实际循环交换，以及外部有限点顺序的调度与完全展开。两者都使用真实 `Mem.store`；动态矩形还支持实际 `Mem.load` 的同格子读改写，并具有 Bernstein 三项条件的内存实例。它们提供、候选执行构造与精确出口修复，最终进入提取的完整程序编译器。它们不依赖旧 CInstr 状态表示，也不把 `Loop.t` 的端点定理直接叫作完整 C 程序定理。

锁定 PolCert 的旧非空 wrapped 入口存在不可满足的 `CState.valid`，已由 Rocq 定理及新的非空执行见证分别审计，见 [入口审计](polcert-context-audit.md)。其实际优化器端点已有参数化适配，但具体完整循环证书尚未实例化。复用这一实现是可选路线；自建实例同样需要源解码、候选重建、真实执行与完整程序证明。

下面的直接 Clight 扩展路线符合允许重实现的要求。推进时需要对照 PolCert 的提取、调度验证、循环生成及 tiling/ISS 等能力逐项记录差距；优先闭合一般参数化循环、条件检查与完整程序链：

1. 矩形域、body 接口、任意次数循环编解码以及同格子读改写的真实 load/store 交换已完成；继续扩展保序依赖和多语句循环体。`ScheduleInterleave.rectangular_row_order_certificate` 已证明行列交换保留每行内部顺序，`RectangularRowSchedule` 已将其接到真实内存；该有依赖规则尚待实际 Clight 实例。
2. 加入动态 affine 域对应与依赖证书，让不受信任优化器提交 schedule；源／目标操作一一对应、依赖保持和机器边界算术必须分别核对。
3. 将足以建立这些证书的入口前提编成可安全执行的检查，包括范围、无溢出与可观察的布局事实；再处理 tiling 的新维度和 private scratch 出口。
4. 扩展检查控制流的共享，记录 guard 成本、代码增长和实际收益。[Clight 共享回退](shared-fallback.md) 已让外部点顺序路径只有一份原循环，不引入临时变量或标签；`matrix_dynamic` 从 353 降至 221 字节。其他路径及多个接受叶子的共享仍需处理，没有运行时间或 speedup 结论。

## 已有工作与研究主张

[CompCert-loop](compcert-loop-comparison.md) 已有抽象行为接口及结构循环变换的完整程序接入；[guard synthesis 及契约推断先例](contribution-plan.md) 已考虑可执行检查与不可观察信息。因此语义参数化、局部到全局、或者“能插入 guard”单独都不是可靠的新颖性主张。CoreJIT、Peek、COVE/cSTOKE、Chamois 等应按候选验证、动态假设、前提发现和宿主边界分别比较，不能统称为同一个问题。

本轮建立的是可运行且可审计的基础：同一性质／条件核与完整程序宿主，已服务算术、内存和真实循环调度。更强的候选贡献是受可执行性约束的前提推导与验证、动态域证书、以及跨这些实例的证明复用和收益；这些还需要具体算法及实验，而不是更多空接口。

复现、日志和准确假设见 [validation.md](validation.md)、[原生矩阵交换](native-matrix-interchange.md) 与[不受信任点顺序入口](untrusted-point-schedules.md)。

## 辅助变量与实际顺序分块

`PrivateRegion` 的出口关系投影到源 temporary 集合，函数入口与调用 continuation 的证明允许候选声明并修改自己的 helper。具体 `StripmineCompiler` 用它重建真实分块循环、截断尾块，并对辅助加法生成无溢出检查。保持迭代顺序使真实普通内存读取、多条语句、条件和别名都可进入这个实例；这没有代替带重排候选的依赖验证。定理、使用方式和边界见 [private-stripmine.md](private-stripmine.md)。完整顺序多面体目标仍继续推进，不能把这个实例当作全部验收完成。
