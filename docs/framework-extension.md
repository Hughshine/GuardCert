# 框架扩展设计：证据、状态与组合

后续将入口回退接口具体化为[四份核心契约与分类](language-independent-interface.md)，并新增不依赖 CompCert 的机械化原型。本文保留原扩展提案；新的接口设计区分已实现的入口协议与仍需专用判断／协议的场景。

2026-10-02 的设计提案。它来自 [跨领域 survey](survey-general.md) 和 [已有工作对比](research-position.md)。**本文是接口方向，不是新增的 Rocq 定理。** 已证明的接口仍以 [现有框架](framework.md)、[CompCert 接入](compcert-integration.md) 和源码为准。

本文后面的“当前”保留最初设计快照，不能作为最新实现清单。随后已实现共享的条件树 lowering、signed32 widened checks、真实内存／嵌套循环宿主、[guarded 矩阵交换](native-matrix-interchange.md) 和[外部点顺序生成](untrusted-point-schedules.md)。通用核与实例的最新边界见 [abstract-kernel.md](abstract-kernel.md) 和 README；任意候选条件推断、一般 affine 域和其他 judgment family 仍属设计。

## 分开研究总范围与第一条实现主线

总范围是：在明确前提及可用证据下，将程序片段换成满足指定正确性判断的候选，并把局部判断组合到宿主程序。

第一条主线是顺序 CompCert 中的行为精化：可执行检查成功时运行候选，否则运行原片段。外部轨迹、返回与控制流仍通过 CompCert 的仿真定理组合。重构、检查消除、快速路径和优化都可以是这种主线的实例。

候选来源应与后续证据链解耦：既支持规则作者提供前提和局部证书，也保留人工/工具提供 source/candidate 后，由受限推断器提议并验证条件的入口。第三种入口允许工具提交自己的条件或 guard 供核对。三者在 ConditionalRule 证书之后共享编码、检查生成与 Host 组合；详见 [候选条件化设计](candidate-conditioning.md)。这不是当前已实现的任意候选验证器。

修复与软件更新必须指定哪些行为允许变化；数值近似必须指定误差如何被上下文使用；constant-time 必须考虑执行间的观测。应提供各自的 judgment family 及其组合定理，而非承诺一条普通 backward simulation 定理适用于所有目标。

## 建议暴露的接口

| 接口 | 使用者提供 | 框架需要实现或证明 |
| --- | --- | --- |
| Host | source/target 语义、允许的片段入口/出口、可用上下文 | 局部到宿主的组合，外部调用、控制出口与进展；优先复用已有仿真/验证器 |
| ConditionalRule | 原片段、候选、入口语义义务、条件局部证明 | 将规则与实际代码绑定；不凭 profile 假定正确性 |
| CandidateConditioning | 原片段、独立候选、片段接口、条件域与可选 witness | 提议并验证充分条件及局部证书；不支持时拒绝；与规则入口共享后续链 |
| PremiseEncoding | 可表达子语言中的 AST、语义 view | 编码与语义义务的对应；未知构造不能静默当作 true |
| EntryDerivation | 内部义务、循环域、依赖关系或可验证 witness | 入口条件足以建立局部证明的假设；不混同后续 Bool 编译 |
| Evidence | 静态证明、可信 checker 证书、运行时检查或混合证据 | 证据消费时的可靠性；验证静态简化/残留条件 |
| CheckCompiler | 类型化检查原语与目标 IR lowering | 接受可靠、检查安全、短路及允许的效果；支持范围内的接受能力 |
| Protocol | 不应用、入口回退、检查点恢复等协议实例 | 候选与失败路径各自满足选择的正确性判断 |
| StateRelation | entry/live-out/frame、内存对应、私有状态 | 执行与出口的关系保持；不能只比较结果变量 |

这不是要求每个用户重新实现所有模块。第一版应内置 CompCert Host、入口 fallback、checked arithmetic 和固定的 frame relation；规则插件交代码模式、前提 AST 和条件局部证书。候选入口则由库中的验证流程承担证书构造，但可以拒绝，且首版限制其支持语法。只有新语义种类才需要新增库级证明。

也不应把所有接口都设为任意 `Prop` 后称为统一框架。可运行检查必须有有限 syntax 和已实现 lowering；一种 Protocol 只有在 Host 与 judgment 上有组合定理时才算支持。

## 前提语言的表达边界

需要区分语义义务语言与可执行检查语言。前者可以使用不变量、量词或关系；后者只能使用可得到且安全求值的信息。通过带证明的入口推导连接两者。

| 前提库 | 语义关注点 | 可执行依据 |
| --- | --- | --- |
| 整数/位向量 | 位宽、符号、无回绕、除法定义性、移位范围 | 已验证的机器原语或 checked arithmetic |
| 内存 | block/provenance、字节区间、chunk、权限、生命周期 | 语言可表达的指针操作、静态证据或显式 runtime metadata；不可直接读取抽象 Mem |
| 不变值 | 读 footprint、写影响、调用影响、快照时点 | 静态 frame 证书、已证明依赖或有语义的版本协议 |
| 代码与表示 | globalenv、函数身份、closure、对象布局、代码版本 | 符号/类型证据和可实现的身份检查 |
| 浮点 | NaN、无穷、signed zero、舍入、允许的误差 | 明确的浮点语义及匹配的原语库 |
| 域约束 | schema keys、NULL、ownership、执行历史等 | 相应 Host 的 checker/逻辑；不能直接套用 C 算术库 |

`NoOverflow` 不应是一枚笼统的全程序 flag。它应绑定某个类型化计算及其所有必要中间值。checked expression 的 validity 不能作为普通 false 参与否定：求值失败后 `not false = true` 可能误接收。当前 `Synthesis.execute` 的 `None` 已与 `Some false` 区分；生成真实代码时也必须保持这个区别。

当前数学 DSL 使用统一 unsigned modulus，snapshot 包含 env/temp_env/mem，缺少 genv；这些实现不能被文档里的更宽分类当成已经支持 signed、floating-point 或函数身份。新库宜先增加明确的类型和 adapter，再扩大 syntax。

还存在一个具体的桥接限制：当前 `encoded_expression_rule.expression_lowering` 要求抽象执行得到 `Some b`。一般检查可能得到 `None`，虽然独立核的 `accepts` 已把它解释为回退，现有真实表达式证书不能直接容纳这种情况。统一 Clight compiler 应实现 `accepts` 的语义：先在条件程序内部保留 validity，最后才把 `None` 映射成不接受；不能先在否定的子表达式中把失败改成 false。扩展 lowering 契约并证明其接入，是第一阶段的一项实质工作。

## 证据与协议

一个可检查的概念模型是：证据产生器返回 `Accept witness` 或 `Reject reason`，witness 在 Rocq 中有解释，并能推出规则要求的事实。提取后证据可以擦除；不要求运行时构造 proof term。

拒绝可能表示条件确实为假，也可能表示算术检查失败、缺少 metadata、超时或证据已失效。一般接口只承诺 Accept 可靠；`Reject` 不等于 `¬Q`。当前纯检查语言在成功返回 `Some false` 时有精确的假值对应，是一个更强的特例。

静态事实 F 可把前提 A 化简为 H，但必须证明 `F ∧ H ⇒ A`，且 F 在使用处可靠。静态证明可以直接消去检查；静态信息不足则生成 H 的检查。要比较的先例包括 Gradual Program Verification 和 StaRVOOrS，不能将这一分层本身作为新颖性。

一个入口谓词可以支撑整个片段的条件仿真，未必需要保持其自身始终为真。若 guard 提前求值、读入参数，或证据跨调用/写操作复用，则额外说明哪些依赖允许改变。若由 monitor 发现中途失败，恢复必须映射当前状态；已有输出或外部调用不能通过重新运行原入口撤销。

## 第一版组合定理应长什么样

以下是设计义务的概要，不是可以直接执行的 Rocq 声明：

```text
1. 本位置的证书绑定实际 source 和 candidate；类型/入口/出口接口匹配。
2. 在宿主证明要求的安全状态上，check 可终止且不引入不允许的效果。
3. check 接受所产生的事实足以应用条件局部仿真。
4. check 拒绝后的状态与原片段入口通过 frame relation 对应。
5. candidate、fallback 的局部仿真都有控制出口和进展保证。
6. Host 的上下文定理将选择后的片段提升为完整程序仿真。
7. 与已有 backend 定理组合得到 source-to-assembly 正确性。
```

第 2 条的适用状态需要精确定义。当前 Clight 纯表达式证书从“source 表达式可定义求值”推出 guard 可求值；这并不声称 guard 在任意状态都可运行。一般 preload 必须用实际执行路径与读取权限证明其安全，尤其不能把会失败的读取移到源程序本来发散或不会读取的路径之前。

检查若分配私有 scratch、使用辅助状态或改变内存表示，第 4 条应通过可见 frame/memory relation 处理，不能继续要求整个 Mem 全等。这类关系应对照 Compositional CompCert、direct refinements 和 ReLoC；不应重新把“有 state relation”作为贡献。

外部程序能进入片段内部的 label、例外控制出口或未匹配的调用 continuation 会破坏组合。Host 必须验证入口限制，或明确提供所有入口的对应。当前 Clight passes 对被复制的带 label 片段保守跳过，外围 goto 则由实际 continuation/label 证明覆盖。

## 不同行为目标的实例化

| 判断种类 | 局部证书必须说明 | 怎样接完整程序 |
| --- | --- | --- |
| 行为精化 | 条件下的局部仿真、frame、事件与进展 | 复用 CompCert/块仿真宿主，再组合 backend |
| 变化契约 | 保持域与允许变化域；新前后状态/异常规格 | 用兼容契约的调用/上下文规则；再用编译器保证实现新程序语义 |
| 合约/enforcement | 满足策略、允许报错/干预、合法运行 transparency | 使用带策略的事件语义/monitor composition |
| 数值近似 | 输入域、误差关系和预算 | 限制上下文并传播误差，最后连接数值 I/O 规格 |
| 超性质 | 公共状态关系、两次运行观测及 guard 的依赖 | 使用 relational/product semantics 的组合；普通功能正确性不足 |

修复后再由 CompCert 编译，可以保持修复程序的行为，却不会自动证明修复正确。更新、enforcement、误差和超性质同理。应清楚区分变换证书与后端保持各自负责的判断。

## 从当前原型推进

| 阶段 | 实际工作 | 完成标准 |
| --- | --- | --- |
| 1 | 为现有 presumption 子集实现统一 Clight condition compiler，保留 validity、类型与短路 | 规则不用再按 guard 形状手写 lowering；提取代码与 C 到 Asm 定理连接 |
| 2 | 消费带证明的静态事实，生成残留检查；绑定规则应用位置 | 同一个条件规则证书用于静态应用、残留 guard 和全部动态检查 |
| 3 | 接入受限但真实的内存规则；明确 metadata/指针操作和权限 | 真实片段、检查代码、失败路径与整程序证明全部完成 |
| 4 | 对照 Chamois/CoreJIT，评估既有 Host/validator 的复用 | 说明新增算法及其必要性，而不只增加另一套上下文证明 |
| 后续 | 入口推导、证据缓存、恢复、其他 judgment family | 每次扩展增加具体算法、协议与组合证明；不以接口占位算支持 |

最初的 19 个证明文件是历史基线。分支、纯表达式及语句区域使用不同宿主组合证明，尚不能称为所有片段共享一个上下文定理。共享 guard lowering 已成为实际算法并由异质实例使用；仍应检验扩展状态关系、动态域和检查 effects 时需要哪些新的 Host 义务。
