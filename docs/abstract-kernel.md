# 由语言实例提供性质与条件选择

这条实现路径把整数、内存、地址及 overflow 表示移出了通用核心。核心处理前提公式和证据；具体语言负责给出检查代码、条件选择的含义，以及替换如何进入该语言的完整程序证明。这里区分已编译的接口与尚未接通的 PolCert 适配。

## 插件与语言分别提供什么

| 接口 | 提供者与义务 |
| --- | --- |
| `language S` | 语言提供 command、test、observation 和执行关系，以及 `conditional` 构造器。`conditional_spec` 证明检查不改变入口状态或增加观察，随后执行选中的分支。观察的内容由实例决定。 |
| `property_dimension S A I` | 性质维度提供原子前提 `A → S → Prop`，检查结果 `A → S → option bool`，以及在入口域 `I` 上的证据正确性。 |
| `check_primitives` | 语言把每个原子检查降低为 validity test 和 value test。validity 必须总能执行；value 仅需在 validity 成功时有定义。两者必须对应抽象检查结果。 |
| 局部变换证书 | 插件证明前提成立时的 refinement 或 preservation，观察关系也由语言或插件提供。 |
| 入口域与上下文证明 | 宿主证明到达实际插入点时满足 `I`，并证明局部替换兼容其控制流、状态关系和整个程序执行。 |

接口没有要求原子前提都是布尔可判定谓词。`Some true` 提供正证据，`Some false` 提供负证据；`None` 只表示不能判定。只证明“接受蕴含性质”的保守检查器可通过 `positive_dimension` 接入，拒绝被编码为 `None`。这样 `not` 无法把保守拒绝变成错误的接受。

`combine_dimensions` 与 `combine_primitives` 以原子类型的和组合维度。核心无需理解其中一个原子是算术、另一个是 alias，或两者是其他语义性质。实例仍须证明检查代码安全、性质适合局部变换，而且入口域确实成立。

## 已证明的通用算法

`compile_condition` 将公式编译成使用语言 `conditional` 的短路控制流，具有真、假和 unknown 三个 continuation。否定只交换真和假，保留 unknown。`compile_condition_correct` 精确证明执行对应所选 continuation，包括检查失败的路径；最终版本化把假和 unknown 都导向原片段。

`property_guard_refinement` 使用候选到原片段的局部义务。`property_guard_preservation` 使用原片段到候选的局部义务，要求候选能匹配每次源执行。它们没有将执行为空的候选视为可用编译优化。`EndpointBridge.v` 还证明：在源结果模状态关系确定、候选有进展且关系对称传递时，可以把 backward endpoint refinement 转为 forward preservation；它包含遗漏进展义务的反例。

`residualize` 消去由静态证书证明的原子，折叠布尔常量。证书必须在整个入口域上成立。它保持原前提的逻辑性质，不要求保留保守检查器的拒绝行为：已证明的事实可以消去，即使动态检查会返回 unknown。`residual_guard_preservation` 将这一步接到通用编译证明。它目前尚未用于原生编译驱动。

这些核心定理实际经 Rocq 9.2 编译，`Print Assumptions` 为闭合证明。这里的接口义务是定理参数；闭合不表示插件无需证明它们。

## 实际 Clight 与端到端实例

`ClightCondition.v` 给出两种语言实例。一种是由纯 Clight 表达式测试构成的 decision tree，降低后每个节点都是实际 `Sifthenelse`。`decision_dispatch` 在 Clight 小步语义中证明：有限次无迹步骤到达选中的叶子，函数、continuation、局部环境、temporaries 和内存保持相同。另一种实例直接使用 Clight terminating big-step fragment，观察包含 trace、temporaries、memory 与 outcome；它自身不覆盖发散。

`encoded_tree_rule` 将性质维度、实际检查原语、前提公式、类型保持、入口域和局部值保持绑定到源与候选表达式。`encoded_tree_rule_sound` 把这份证书交给 `ClightTreeRewrite` 宿主。宿主允许 return、临时赋值、赋值右侧及严格表达式上下文，证明完整 Clight 程序的 forward simulation，包括调用、循环、switch、label 和 goto。守卫包裹的三个叶子上下文不含 label，因此不会产生绕过检查的入口。

`ClightDecisionRule.v` 进一步提供 `encoded_decision_rule`，允许 validity/value 原语本身是条件树。它使用 `decision_test_language` 与同一个 `compile_condition`，输出相同的宿主契约。[signed32 乘法取消实例](clight-signed-cancellation.md) 已通过这一接口进入真实 C→Asm 编译器；实际 Loop 的动态仿射合成也复用其共享公式编译定理。

具体的 `(x+x)/2 → x` unsigned32 实例使用一侧的 no-overflow 维度，生成：

```c
if (x <= 2147483647U) {       /* validity: 检查提供正证据 */
  if (1) return x;            /* value: 成功的证据为 true */
  else return (x+x)/2U;
} else return (x+x)/2U;       /* unknown: 原片段回退 */
```

这棵树由通用编译器生成，两个实际表达式及其 lowering 证明由 Clight 实例提供。没有假设 C 可以读一个隐含的 CPU overflow flag。源表达式有定义可推出原子操作数是适当的整数，这是该实例的入口域证明。

`TreeCompiler.compile_property_rewrites` 在 SimplLocals 后使用新宿主，并复用先前四类规则与分支 pass。`compile_property_rewrites_correct` 是实际编译函数从 `Csem` 到 `Asm` 的 backward simulation，`compile_property_rewrites_preserves_spec` 保持排除出错的规格。具体定理不要求源程序全局无溢出。提取后的 Driver 现在调用这一函数，原生测试核对结果、快路／回退边界和生成树的 IR 形状。

这些 CompCert 定理继承上游假设；完整证明端点是形式化 Asm。外部解析、汇编、链接和 libc 的原生运行仍是执行检查。

## PolCert 的对接边界

v10 `InstrTy.INSTR` 本身暴露 `NonAlias`、非别名保持、状态等价稳定性，以及 Bernstein 读写条件下的交换证明。`PolCertSchedule.v` 已直接使用这一真实模块实例化 `AbstractSchedule`，证明有限相邻交换证书保持结果模状态等价。它不解释地址，也不是多面体 schedule validator。

`PolCertLoopGuard.v` 已把真正的 `Loop` 实例化为条件语言，生成带 validity/value 的版本化 `Loop.stmt`，分别证明 forward preservation 与 backward endpoint refinement，并包含恒不成立条件下的任意候选死分支例子。入口域可由外围语言建立。实际 `Loop.test` 只读取数学整数参数，因此不能直接承载内存 alias 检查；外层 Clight 适配器必须执行相应检查并建立入口性质。

`PolCertLoopProgram.v` 进一步提升到实际 `Loop.t` 的 wrapped semantics，保留源的 context 与变量 metadata。入口域必须由真实 `Compat/NonAlias/InitEnv` 推出；候选的 backward endpoint 在 metadata 一致时可直接接入。恒假条件例子也已提升。这里的完整 `Loop.t` 程序仍不是完整 C 程序。

三个接口及真实 `Loop` 的 57 个证明依赖已在当前 CompCert 基础库上从锁定源码恢复并完整重编译。可选命令是 `make polcert-proof`；源码哈希、兼容补丁和准确边界见 [PolCert 适配](../adapters/polcert/README.md)。上游 VPL 保留自身的 monad/oracle 公理；新增适配器定理只依赖声明的 `INSTR` 参数。

v10 的 `Opt_prepared_correct` 当前是“目标 Loop 终止执行 → 存在源 Loop 终止执行且结果 `State.eq`”。统一并行驱动的目标是 `ParallelLoop`。二者都不能直接用于声称完整 C 程序的优化正确性。需要完成数学 Loop 与固定宽度 Clight 的具体语言桥接、范围与访问条件、候选进展，以及适合 region 的上下文证明。

`PolCertOptimizer.v` 已直接调用真实 `Opt_prepared` 并消费其正确性证明。适配器使用现有 `PolIRs.Loop`；metadata 通过已证明的相等检查核对，失败时返回原 Loop 程序。该入口沿用上游 alarm monad 的成功返回契约。复现与精确边界见 [优化器适配](../adapters/polcert-optimizer/README.md)。

目前已接通的真实 Clight 宿主是表达式替换；任意多语句／循环 region、可执行 alias guard 和完整 Loop lowering 仍未接通。条件树直接嵌入会复制叶子代码，可能需要后续共享 continuation 降低代码体积。本轮没有性能收益或原生多面体优化的实验结论。

`PolCertAffineClight.v` 和 `PolCertAffineGuard.v` 已补出数学整数与 signed32 的表达式桥接：静态区间检查覆盖常量、变量、加法及常量乘法的每个中间值；实际 Clight 范围 guard 的接受建立输入区间，布尔测试 lowering 保持实际 Loop 的求值。这些定理消费已证明的性质接口，没有向通用核心加入整数语义。详细契约和不支持的运算见 [仿射桥接](polcert-affine-clight.md)。

后续 [计数循环桥接](polcert-clight-loop.md) 已提供一个外层 Loop 与 `Instr/Seq/Guard` body 的 lowering，基本指令由语言插件提供执行与内存 view 证书。循环端点已提升为任意函数／continuation 中的小步执行；这尚不能代替区域替换的完整程序 simulation。嵌套循环、具体内存实例、区域提取及 private temporary 的宿主 frame 仍需补充。

[嵌套循环桥接](polcert-nested-clight.md) 现已补充指定 live frame 下的 private temporary 关系与递归 Loop lowering。它保留参数／外层计数器，检查 scratch pool 的全部冲突，并复用现有指令插件；具体宿主仍须建立外围 live 集合、函数 temporary 声明及区域 simulation。

[同地址读取插件](clight-same-address.md) 已通过上述通用性质与完整程序宿主进入实际 C→Asm 编译器。源 load 的有定义求值建立指针检查有效性，接受的地址相等性质允许重复读取消除。它是已接通的内存表达式实例，不代替循环区域所需的可执行 non-alias 检查。

[动态仿射合成](affine-dynamic-synthesis.md) 进一步将选定的不溢出前提直接编成安全的检查树，先检查子运算再用 signed64 检查父运算。树本身可作为一个测试，经 `decision_test_language` 接入原核心；不支持的原子保持 unknown。这一实例不要求提议输入区间，但仍需宿主建立 signed32 参数 view，且尚未进入原生驱动。
