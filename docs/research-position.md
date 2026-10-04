# 已有覆盖与候选研究问题

核对日期：2026-10-02。结论是：**有值得试验的候选问题，但条件变换、运行时版本选择和局部到全程序组合均已有先例；当前原型不能据此宣称新颖性。** 这些先例并不都提供本项目要的同一种接口或机械保证，应逐层比较。本文将已确认的覆盖与我们的研究推断分开。跨领域需求见 [扩展 survey](survey-general.md)，人工/工具候选见 [候选条件化设计](candidate-conditioning.md)，接口调整见 [框架扩展设计](framework-extension.md)。

实现进展补充于 2026-10-03：`1b6e3fd` 阶段已实现实际 C 的稳定地址参数、真实指针活动足迹检查、外部仿射／分块候选、完整 Csem→Asm 保证及提取运行，见[功能对齐记录](polcert-integration-target.md)和[地址参数证据](memory-affine-address-parameters.md)。因此下表的实现列已更新；上述文献核对日期及新颖性判断不因实现进展改变。[固定地址参数的边界扫描](memory-parameter-boundary-scans.md)随后也完成证明审计、提取和同源完整程序对照；[多个运行时条件方案](memory-version-families.md)也已进入同一实际编译器：抽象核心对异质定义域、前提和状态关系保持源观察，实际组件从已认证检查器获得；完整程序审计没有新增公理。同源测试新增接受 474 次函数调用，但地址查询和代码大小增长，因此不能由这项能力推断性能收益或文献新颖性。

## 哪个工作最接近

这是按本项目关注点作出的判断，不是论文之间的能力排名。最接近的工作取决于我们要新增哪层：

| 本项目的关注点 | 最直接的对照 | 为什么 |
| --- | --- | --- |
| 给定原/候选，推断成立条件并运行时选择版本 | COVE/cSTOKE 2015 | 从没有变换历史的候选推断条件；§5.5 已实验动态检查与原代码回退，但检查代码手写 |
| 从建模/变换义务产生、推导、简化并生成运行时条件 | CGO 2017 | 它实际实现了假设处理与入口版本选择，最接近用户提出的需求 |
| 机械证明动态假设、利用假设的优化及失败恢复 | CoreJIT 2021 | Assume/Anchor、检查安全分析、优化 pass 与整个 JIT 的仿真已经贯通 |
| 不同片段变换共享验证器并接入 CompCert | Chamois 2023 | 源/目标块关系、不变量与符号重写由通用验证器消费 |
| 局部 rewrite 插件到全程序的通用定理 | Peek 2016 | 已有直接的 verified peephole 库及上下文提升 |
| 规则暴露前提、交外部分析消解 | Icing 2019 | compiler/application preconditions 与可扩展 rewrite 接口 |

CoreJIT 是机械化推测机制的重要近邻；给定候选后推断成立条件，COVE 更直接。CGO 则最直接对应从已知建模/变换义务出发的假设处理。第一阶段若仍是 AOT CompCert 的入口版本化，就不必同时重建 JIT monitor 和活动栈去优化机制。

CoreJIT 是 passes 与运行机制的已验证实现；Alive2 是给定 LLVM 函数对的翻译验证器，二者不能只按“都验证优化”视为同一种服务。真正以已验证 peephole 验证器为主题的近邻是 AliveInLean。接口对照与证明边界见 [候选条件化设计](candidate-conditioning.md)。

CoreJIT §3.3.2 的输入包括 profiler 提出的 guard 表达式与 Anchor 位置。它验证可安全插入检查；§3.3.3 的常量传播利用检查通过后的事实；失败恢复由 metadata 对应回原版本。其“任意谓词”指 IR 可表达的 guard，不是自动编译任意 Rocq 命题。论文并未提供本项目讨论的通用“语义义务 → 前提 AST → 入口投影 → checked machine guard”算法。其全程序定理针对 CoreIR/JIT 执行，原生生成和 Lua 前端在 2021 论文的证明范围外。[CoreJIT §§1、3.1、3.3、4](https://www.o1o.ch/about/assets/courir.pdf)。

还需避免把两篇论文的范围直接相加：FM-JIT 2023 验证 CompCert 原生生成、解释器/原生执行交互和推测指令的编译，但 §1 明确将动态推测插入排除在该论文范围之外，输入可预先包含特化。其 runnable JIT 的 C primitives 也没有对应的实现正确性证明。它推进了 CoreJIT 未覆盖的后端问题，却不是“CoreJIT 全部优化 passes 加原生生成”已经整体机械连接的证据。[FM-JIT 引言限制、§5.5](https://aurele-barriere.github.io/papers/fmjit.pdf)。

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

这个判断不意味着 Peek 已做了我们要的 guard 生成：静态活跃性提供的是上下文观察接口，运行时值域/别名检查解决的是本次执行的语义条件。后者新增检查自身的执行、效果、失败路径和控制流义务；两层可以同时需要。研究应比较这些具体义务和接口的复用，不能因为同样有全程序定理就将两者等同。

### Chamois：已有更一般的块仿真与验证器

**Formally Verifying Optimizations with Block Simulations，OOPSLA 2023** 已把源/目标 CFG、块入口关系不变量和可扩展重写规则交给通用验证器。当前 Chamois 文档还列出了 BTL 符号执行、内存重写、调度、lazy code、store motion 等接口。局部块、关系不变量、oracle 与全 CFG 的组合也已有很接近的实现。[论文入口](https://doi.org/10.1145/3622799)、[作者海报](https://www-verimag.imag.fr/~boulme/pub/poster_OOPSLA23.pdf)、[当前证明模块索引](https://certicompil.gricad-pages.univ-grenoble-alpes.fr/Chamois-CompCert/)、[oracle 接口](https://certicompil.gricad-pages.univ-grenoble-alpes.fr/Chamois-CompCert/html/ocaml/BTL_BlockOptimizer.html)。

本轮取得了摘要、海报、当前 BTL 语义与 OCaml oracle 类型，未取得论文全文及部分核心证明模块正文。故目前不能断言其条件重写库不支持某种动态前提。下一步的接口复用应直接对照其验证器，避免另造一个相同作用的局部仿真层。

### 其他直接邻居

| 工作 | 已有覆盖 | 仍需区分的接口问题 |
| --- | --- | --- |
| [COVE/cSTOKE，OOPSLA 2015](https://theory.stanford.edu/~aiken/publications/papers/oopsla15a.pdf) | 给定原/候选及测试，推断前提并检查条件正确性；§5.5 运行时回退 | 动态检查代码手写后编译拼接；没有所需的机械化生成/上下文链。部分浮点实例使用 unsafe axioms |
| [Conditional Equivalence，2010 技术报告](https://www.microsoft.com/en-us/research/publication/conditional-equivalence/) | 程序演化中的条件等价、组合检查及抽象域推断算法 | §5.1 说明抽象不动点推断未实现；partial equivalence 不足以保持终止/发散行为；不是动态 guard 生成系统 |
| [CGO 2017 Optimistic Loop Optimization](https://pollylabs.org/publications/grosser-2017-Optimistic-Loop-Optimization.pdf) | 统一假设收集、参数空间投影、简化、检查生成；讨论检查自身回绕和参数 preload | 已有算法与系统。候选增量必须落到机械化的算法正确性和真实语义对应 |
| [ALIVE-INFER，PLDI 2017](https://people.cs.rutgers.edu/~santosh.nagarakatte/papers/pldi2017-alive-infer.pdf) | 自动推断并验证 peephole 规则前提 | 论文的前提主要是编译期规则应用条件；不能直接当作生成的运行时检查证书 |
| [AliveInLean，CAV 2019](https://web.ist.utl.pt/nuno.lopes/pubs.php?id=aliveinlean-cav19) | 在 Lean 中验证 LLVM peephole 验证器 | 其保证明确以 SMT 正确消解义务为前提；验证规则与生成安全 guard 是不同任务 |
| [Icing，CAV 2019](https://cakeml.org/cav19.pdf) | 可扩展 rewrite 库、前提接口、规则组合、HOL4 证明及 CakeML 连接 | §4 的 `cond` 检查被优化表达式上的条件，`assume` 返回外部需消解的命题；不能仅凭名称解释成运行时版本化 |
| [CoreJIT，POPL 2021](https://www.o1o.ch/about/assets/courir.pdf) | 已验证的 assume 插入、guard 无错误求值分析、去优化、优化组合与 JIT 全程序仿真 | 安全 guard 和恢复本身已做过。应比较我们的语义前提编译接口是否真提供不同能力 |
| [FM-JIT，POPL 2023](https://aurele-barriere.github.io/papers/fmjit.pdf) | 原生代码生成、预先插入的推测指令及效果抽象的精化组合 | 动态推测插入不在该论文范围；C primitives 实现未证明。不能把“接 CompCert backend”单独算新意 |
| [Abstract Execution，JAR 2024](https://link.springer.com/article/10.1007/s10817-023-09692-0) | 对 schematic programs 的关系式证明，应用于重构、成本分析和并行化 | “不限优化的统一变换证明”也已有框架；真正增量应是一个具体可执行算法和定理 |

## 哪些主张目前不能成立

- 首个 verified conditional rewrite 或 verified peephole 框架。
- 首次把局部 rewrite 接到完整程序或经过验证的编译器。
- 首次用关系不变量、活跃性、内存关系或 oracle 降低证明负担。
- 首次统一组织乐观假设，或首次证明 guard 插入和去优化。
- 首次从独立候选推断正确性条件，并用动态检查选择原版本；COVE/cSTOKE 是直接先例。
- 首次结合静态证据与运行时检查。Hybrid Type Checking、Gradual Program Verification、StaRVOOrS 都是必须比较的先例，见 [扩展 survey](survey-general.md)。

这些内容可以成为本项目的基础设施和实例，但论文需要指出实际新增的算法、适用规则或证明能力。把所有工作都放进一个 `Goal : Prop` record，并没有解决它们的语义与组合问题。

## 一个较具体的候选问题

> 对一类显式表达前提的片段变换，能否将同一份条件正确性证书分别用于静态应用和运行时应用，并机械证明从语义前提到实际检查代码的转换，包括定义性、检查位置和前提的有效范围？

另一个应保留的入口是：给定人工或工具产生的 S/T，在可检查的条件域中寻找并验证充分条件，随后进入同一条检查生成和组合链。它无需信任候选作者，也不要求作者先说明完整变换历史。这个前端更接近 COVE。当前实际仿射／tiling 路线已经从有限范围 profile 提案和候选重验中获得充分条件，并自动生成范围及实际活动足迹的检查；其正确性模板由语言实例证明。它仍不处理任意两个 C／Clight 片段的条件发现，也没有最弱条件保证。

进一步建议把可用观察、检查安全和静态事实作为条件推断的输入，形成有真实代码与证书的候选验证服务。可执行前提和最优 guard synthesis 本身也已有 VMCAI 2011、CAV 2014 的先例，不能据此宣称新意。具体算法候选、首批实例与推进顺序见 [贡献计划](contribution-plan.md)。

这是我们的研究提议，**不是已确认的文献空白**。它接近 CGO 2017 的工程算法、CompCert/Chamois 的仿真复用和 CoreJIT 的 guard 安全证明；只有做出比这些工作的直接组合更具体的结果，定位才有说服力。

“condition synthesis”至少包含以下不同任务：

| 层 | 输入 → 输出 | 所需证明 | 当前原型 |
| --- | --- | --- | --- |
| 前提发现 | 源片段与候选 → 语义义务 Q | 在 Q 下的候选正确性；推断可由 oracle 提出并验证 | 一般规则仍由作者给出模板；实际仿射候选已有有限范围提案、独立源检查和依赖证书重验；任意 S/T 未覆盖 |
| 编码 | Q → presumption AST 或语言检查程序 | AST／程序接受的含义与 Q 对应 | 公式编码和实例；真实足迹分离也有自动生成的私有循环检查，其语义由具体实例证明 |
| 入口推导 | 片段内部义务 → 入口谓词 A | A 足以建立所需执行域、内部不变量和局部仿真 | 没有任意规则的通用算法；具体矩形指针路线从正常源执行推导条件定义性、被使用参数的整数值及实际访问能力 |
| 静态消解与残留 | 静态事实 F、A → 剩余条件 H | F 在本次入口可靠，且 F ∧ H ⇒ A | 已有有证书的通用 residualization；尚未接入原生驱动或自动入口分析 |
| 检查生成 | H → 条件程序与真实 IR 代码 | 接受可靠、可安全求值、效果合规；可表达域内有接受能力 | 已有公式与 validity 条件树的通用合成、具体算术／内存检查和实际 Loop 仿射合成；新语义原语仍需语言实例证明 |
| 插入与组合 | 条件代码、候选、回退 → 宿主程序 | 条件仿真、入口/出口与进展、实际代码绑定、后端组合 | 分支、表达式、有限静默语句及规范矩形／部分仿射域循环已进入 C→Asm；真实指针候选恢复公共游标，有状态核心已具体实例化；任意循环／内存关系区域未覆盖 |

最有研究价值的部分可能在中间三层：不是给用户再添一个要手写的 guard 证明，而是**一个能运行、能拒绝不支持情况、能给出证明的前提处理算法**。如果所谓合成最终仍要求每个插件分别手写 guard、无错误求值证明和入口推导，框架收益会很有限。

这里不要求任意谓词的最弱 guard。首先证明接受可靠，再对明确的可表达域给出检查成功时的真/假对应、或有条件的接受完整性。否则永远返回 Reject 也满足安全性，却没有应用价值。

入口事实不必在每条指令后原样保持：局部定理可以从入口事实推出整段执行正确。只有在提前读取、把检查移到别处、缓存证据或跨调用复用时，才需要额外的有效范围、依赖变化或恢复证明。把这些区别写进接口，比笼统增加一个“稳定性”假设更有用。

## 应先做哪些实例

**保留现有算术规则作为接入基线。** `x/y → x>>1`、条件取消、死分支足以测试接口，但它们不能证明框架处理了新的语义难点。

**第一个实质实例：带 checked arithmetic 的入口条件编译。** 从一份包含嵌套加减、范围和否定的 presumption 生成 Clight 检查，自动保留 validity 与短路。再加入由可验证静态事实消去部分原子条件的算法。比较统一编译前后需要多少实例专属证明，并用检查自身溢出的反例验证其定义性处理。

**另一个可比较的内存实例：读取消除或移动。** 例如 `a=*p; *q=v; b=*p` 在字节区间不相交下改为复用 `a`。除不相交外，还要处理访问权限、检查代码可用的信息和事实使用的位置。旧 `CompCertMemoryRule.v` 提供实际 `Mem.load/store` 的局部端点；当前多指针循环路线已经提供源证据覆盖的实际物理单元检查和片段插入，但尚未因此获得这一任意语句序列的读取消除入口。不能把 block 编号当成程序能够读取的 metadata，也不能把 `p!=q` 当作一般字节不相交证明。[局部接口](../theories/CompCertMemoryRule.v)、[实际循环足迹路线](memory-multiple-pointer-guards.md)。

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

[检查前缀实例](memory-prefiltered-versions.md)进一步通过同一端点和同源完整程序验证。在这批测试中，候选选择相同且 alias 查询减少约 11.2%，代码文本增大；结构正确性不保证一般接受范围或运行时间改善。这是框架检查组合与具体检查策略的实现证据，不构成文献新颖性结论。

[带入口起点的片段](memory-started-fragments.md)将源正常执行可提供的实际访问域限制落实到运行时检查与候选：检查枚举 `[start, upper)`，不要求源没有访问的前缀具有权限。该实例共享原抽象核心及 Csem→Asm 端点，并实际验证非零起点的候选执行；负根和负地址参数仍回退。407 模块／557 证明源码的审计保持既有 42 项完整程序假设。这是具体语言实例的表达范围扩展，文献定位及新颖性结论仍需独立论证。
