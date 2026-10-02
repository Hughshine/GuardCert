# 已有覆盖与候选研究问题

核对日期：2026-10-02。结论是：**有值得试验的候选问题，但“通用 conditional rewrite 框架，局部证明接入 CompCert”本身已有直接先例；当前原型不能据此宣称新颖性。** 本文将已确认的覆盖与我们的研究推断分开。跨领域需求见 [扩展 survey](survey-general.md)，接口调整见 [框架扩展设计](framework-extension.md)。

## 最直接的先例

### CompCert 主线已经有条件化的局部规则

本项目锁定的 CompCert v3.18 中，`Constprop` 通过 `ValueAnalysis` 得到抽象事实，再做常量传播、强度削减、分支解析和调用目标简化。`op_strength_reduction_correct` 的局部结论使用 `Val.lessdef`，其 Section 的前提包括真实寄存器值与抽象环境的对应；随后 `Constpropproof.transf_program_correct` 给出整个 RTL 程序的 forward simulation。

核对点：[局部前提](../vendor/CompCert/x86/ConstpropOpproof.v)、[局部规则算法](../vendor/CompCert/x86/ConstpropOp.v)、[完整程序证明](../vendor/CompCert/backend/Constpropproof.v)。具体定义与定理为 `MATCH`、`op_strength_reduction_correct`、`transf_program_correct`。

`CombineOp` 也已经使用 value numbering 的正确性事实合并运算和条件。`CombineOpproof.combine_op_sound` 在 `get_sound` 下证明结果精化；它不是对任意寄存器输入无条件成立的文本替换。[算法](../vendor/CompCert/x86/CombineOp.v)、[局部证明](../vendor/CompCert/x86/CombineOpproof.v)、[宿主 CSE 证明](../vendor/CompCert/backend/CSEproof.v)。

因此，条件化规则、局部结果关系、分析事实的可靠性以及整程序连接都不是空白。这里的证据主要由编译期分析提供；把其中某条规则改成运行时版本选择，还需要另外构造和证明检查代码。

### Peek：已有 verified peephole 框架

Mullen、Zuniga、Tatlock、Grossman 的 **Verified Peephole Optimizations for CompCert，PLDI 2016**，提出 Peek：优化作者证明局部仿真与进展义务，通用定理利用已验证的活跃性分析提升到全程序。论文验证了 28 条规则。它直接覆盖了“插件提交局部证明，框架承担上下文组合”这一核心想法。[论文 §§3–4](https://darzu.io/files/pldi2016.pdf)、[代码](https://github.com/uwplse/peek)。

接口允许死寄存器不同，要求内存对应；论文的片段限制包括等长、没有 call/return，并要求源片段内不发散。它还显式依赖调用约定和 allocator 的假设。论文中的应用证据重点是静态活跃性，并没有给出我们所讨论的通用 presumption 到检查代码的生成链；这不能被扩大成“Peek 原理上不能验证含 guard 的 rewrite”。[论文 §§3.2–3.3、4.3、5](https://darzu.io/files/pldi2016.pdf)。

**对本项目的约束：** 换到 Clight、增加几条算术规则或更新 Rocq 版本，是有用的工程工作，通常不足以作为主要研究贡献。

### Chamois：已有更一般的块仿真与验证器

**Formally Verifying Optimizations with Block Simulations，OOPSLA 2023** 已把源/目标 CFG、块入口关系不变量和可扩展重写规则交给通用验证器。当前 Chamois 文档还列出了 BTL 符号执行、内存重写、调度、lazy code、store motion 等接口。局部块、关系不变量、oracle 与全 CFG 的组合也已有很接近的实现。[论文入口](https://doi.org/10.1145/3622799)、[作者海报](https://www-verimag.imag.fr/~boulme/pub/poster_OOPSLA23.pdf)、[当前证明模块索引](https://certicompil.gricad-pages.univ-grenoble-alpes.fr/Chamois-CompCert/)、[oracle 接口](https://certicompil.gricad-pages.univ-grenoble-alpes.fr/Chamois-CompCert/html/ocaml/BTL_BlockOptimizer.html)。

本轮取得了摘要、海报、当前 BTL 语义与 OCaml oracle 类型，未取得论文全文及部分核心证明模块正文。故目前不能断言其条件重写库不支持某种动态前提。下一步的接口复用应直接对照其验证器，避免另造一个相同作用的局部仿真层。

### 其他直接邻居

| 工作 | 已有覆盖 | 仍需区分的接口问题 |
| --- | --- | --- |
| [CGO 2017 Optimistic Loop Optimization](https://pollylabs.org/publications/grosser-2017-Optimistic-Loop-Optimization.pdf) | 统一假设收集、参数空间投影、简化、检查生成；讨论检查自身回绕和参数 preload | 已有算法与系统。候选增量必须落到机械化的算法正确性和真实语义对应 |
| [ALIVE-INFER，PLDI 2017](https://people.cs.rutgers.edu/~santosh.nagarakatte/papers/pldi2017-alive-infer.pdf) | 自动推断并验证 peephole 规则前提 | 论文的前提主要是编译期规则应用条件；不能直接当作生成的运行时检查证书 |
| [AliveInLean，CAV 2019](https://web.ist.utl.pt/nuno.lopes/pubs.php?id=aliveinlean-cav19) | 在 Lean 中验证 LLVM peephole 验证器 | 其保证明确以 SMT 正确消解义务为前提；验证规则与生成安全 guard 是不同任务 |
| [Icing，CAV 2019](https://cakeml.org/cav19.pdf) | 可扩展 rewrite 库、前提接口、规则组合、HOL4 证明及 CakeML 连接 | §4 的 `cond` 检查被优化表达式上的条件，`assume` 返回外部需消解的命题；不能仅凭名称解释成运行时版本化 |
| [CoreJIT，POPL 2021](https://www.o1o.ch/about/assets/courir.pdf) | 已验证的 assume 插入、guard 无错误求值分析、去优化、优化组合与 JIT 全程序仿真 | 安全 guard 和恢复本身已做过。应比较我们的语义前提编译接口是否真提供不同能力 |
| [FM-JIT，POPL 2023](https://aurele-barriere.github.io/papers/fmjit.pdf) | 原生代码生成与效果抽象的精化组合 | 不能把“接 CompCert backend”单独算新意；需报告其原语规格与实现边界 |
| [Abstract Execution，JAR 2024](https://link.springer.com/article/10.1007/s10817-023-09692-0) | 对 schematic programs 的关系式证明，应用于重构、成本分析和并行化 | “不限优化的统一变换证明”也已有框架；真正增量应是一个具体可执行算法和定理 |

## 哪些主张目前不能成立

- 首个 verified conditional rewrite 或 verified peephole 框架。
- 首次把局部 rewrite 接到完整程序或经过验证的编译器。
- 首次用关系不变量、活跃性、内存关系或 oracle 降低证明负担。
- 首次统一组织乐观假设，或首次证明 guard 插入和去优化。
- 首次结合静态证据与运行时检查。Hybrid Type Checking、Gradual Program Verification、StaRVOOrS 都是必须比较的先例，见 [扩展 survey](survey-general.md)。

这些内容可以成为本项目的基础设施和实例，但论文需要指出实际新增的算法、适用规则或证明能力。把所有工作都放进一个 `Goal : Prop` record，并没有解决它们的语义与组合问题。

## 一个较具体的候选问题

> 对一类显式表达前提的片段变换，能否将同一份条件正确性证书分别用于静态应用和运行时应用，并机械证明从语义前提到实际检查代码的转换，包括定义性、检查位置和前提的有效范围？

这是我们的研究提议，**不是已确认的文献空白**。它接近 CGO 2017 的工程算法、CompCert/Chamois 的仿真复用和 CoreJIT 的 guard 安全证明；只有做出比这些工作的直接组合更具体的结果，定位才有说服力。

“condition synthesis”至少包含以下不同任务：

| 层 | 输入 → 输出 | 所需证明 | 当前原型 |
| --- | --- | --- | --- |
| 前提发现 | 源片段与候选 → 语义义务 Q | 在 Q 下的候选正确性；推断可由 oracle 提出并验证 | 规则作者手写 Q 与局部证明 |
| 编码 | Q → presumption AST | AST 的含义与 Q 对应 | 有 encoding record 和实例 |
| 入口推导 | 片段内部义务 → 入口谓词 A | A 足以建立所需执行域、内部不变量和局部仿真 | 无通用算法；不能用后续 synthesis 定理替代 |
| 静态消解与残留 | 静态事实 F、A → 剩余条件 H | F 在本次入口可靠，且 F ∧ H ⇒ A | 无已验证的通用 residualization |
| 检查生成 | H → 条件程序与真实 IR 代码 | 接受可靠、可安全求值、效果合规；可表达域内有接受能力 | 有独立 AST synthesis；Clight lowering 仍是几个形状的手写证书 |
| 插入与组合 | 条件代码、候选、回退 → 宿主程序 | 条件仿真、入口/出口与进展、实际代码绑定、后端组合 | 分支与纯表达式路径已接入；一般内存片段未接入 |

最有研究价值的部分可能在中间三层：不是给用户再添一个要手写的 guard 证明，而是**一个能运行、能拒绝不支持情况、能给出证明的前提处理算法**。如果所谓合成最终仍要求每个插件分别手写 guard、无错误求值证明和入口推导，框架收益会很有限。

这里不要求任意谓词的最弱 guard。首先证明接受可靠，再对明确的可表达域给出检查成功时的真/假对应、或有条件的接受完整性。否则永远返回 Reject 也满足安全性，却没有应用价值。

入口事实不必在每条指令后原样保持：局部定理可以从入口事实推出整段执行正确。只有在提前读取、把检查移到别处、缓存证据或跨调用复用时，才需要额外的有效范围、依赖变化或恢复证明。把这些区别写进接口，比笼统增加一个“稳定性”假设更有用。

## 应先做哪些实例

**保留现有算术规则作为接入基线。** `x/y → x>>1`、条件取消、死分支足以测试接口，但它们不能证明框架处理了新的语义难点。

**第一个实质实例：带 checked arithmetic 的入口条件编译。** 从一份包含嵌套加减、范围和否定的 presumption 生成 Clight 检查，自动保留 validity 与短路。再加入由可验证静态事实消去部分原子条件的算法。比较统一编译前后需要多少实例专属证明，并用检查自身溢出的反例验证其定义性处理。

**第二个实质实例：内存读取消除或移动。** 例如 `a=*p; *q=v; b=*p` 在字节区间不相交下改为复用 `a`。除不相交外，还要处理访问权限、检查代码可用的信息和事实使用的位置。现有 `CompCertMemoryRule.v` 只证明实际 `Mem.load/store` 的局部端点，没有可执行 C guard 或片段插入定理。不能把 block 编号当成程序能够读取的 metadata，也不能把 `p!=q` 当作一般字节不相交证明。[现有局部接口](../theories/CompCertMemoryRule.v)。

内存实例先限制到可证明的访问形状，或显式携带运行时 metadata；不要在 CompCert C 中直接用不同对象指针的大小比较实现通用地址区间检查。若需要机器地址语义，应单独证明其表示对应，Peek 已说明这一问题的重要性。

**跨领域实例作为接口压力测试。** 可先选行为保持的 refactoring 或 bounds-check 消除：它们仍消费相同的条件精化证明。安全修复、软件更新、近似计算和 constant-time 则分别需要变化契约、状态迁移、误差契约和超性质；它们不宜同时进入第一版实现，也不能通过改名字归入现有全等接口。

## 怎样决定值得继续

| 验收问题 | 有说服力的结果 | 会削弱定位的结果 |
| --- | --- | --- |
| 是否新增算法？ | 一个 verified encoder/compiler 或经证明的验证器，自动完成多条规则的 guard 生成 | 只增加 record，每条规则仍手写全部 guard 证明 |
| 是否复用证明？ | 同一份条件规则证书支撑静态、残留检查两种应用；宿主定理复用已有仿真基础 | 分别重写静态规则、动态规则和每个 pass 的上下文证明 |
| 是否有真实语义难点？ | 算术定义性和内存检查两种实例，共享核心生成与组合定理 | 只有几个标量恒等式和入口 `if` |
| 是否实际可用？ | 在真实 CompCert IR 提取执行，记录 guard 开销、接受率、代码增长及证明负担 | 只展示玩具语义定理，没有真实 lowering |
| 是否区别于最接近工作？ | 对 Chamois/CoreJIT/CGO 的同一例子说明具体缺少哪层自动化或定理 | 只列论文名，或以“更统一”“最新工具链”解释增量 |

当前最合理的判断是：**端到端原型证明了可行性；已有工作足以否定宽泛的新颖性主张；“前提到实际检查代码的已验证处理”是一个需要用算法和异质实例验证的候选方向。** 若这条链可以直接通过已有接口组合得到，项目仍可作为工程库，但应重新寻找更具体的问题，而不是强行扩大框架名称。
