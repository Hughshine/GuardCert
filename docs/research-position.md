# 已有覆盖与候选研究问题

当前整体叙事沿用 `topdown/research-positioning` 的 [paper narrative](topdown/paper-narrative.md)：**语言无关 verified optimistic transformation 框架，加有实质算法与条件正确性证明的 CompCert 循环实例**。框架、语言实例、优化／domain 实现者的责任和最难验收见 [责任矩阵](framework-responsibilities.md)，已列入 [活动目标与计划](current-work-plan.md)。框架的贡献由可复用的条件／证据处理和安装设施体现；循环实例必须实际提供候选验证、入口推导和真实语义对应。不能只凭一条 abstract select 定理或一个外围 if 支撑这项叙事。以下文献与固定提交的证据限制继续有效，预期贡献不等于已证实的新颖性。

初次核对日期：2026-10-02；五个直接近邻与实现证据定向复核：2026-10-05（main `cf4d442`）。该固定基线的定位见文末修订结论及[逐能力证据矩阵](evidence-to-claim-2026-10-05.md)；后续评审吸收与当前计划见[综合记录](review-synthesis-2026-10-05.md)和[工作计划](current-work-plan.md)。下文旧实现表格为历史阶段，不能用于判定当前支持范围。结论是：**有值得试验的候选问题，但条件变换、运行时版本选择和局部到全程序组合均已有先例；当前原型不能据此宣称新颖性。** 这些先例并不都提供本项目要的同一种接口或机械保证，应逐层比较。本文将已确认的覆盖与我们的研究推断分开。跨领域需求见 [扩展 survey](survey-general.md)，人工/工具候选见 [候选条件化设计](candidate-conditioning.md)，接口调整见 [框架扩展设计](framework-extension.md)。

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

## 既有仿射路线的历史证据补充

以下保留此前路线的阶段记录，其计数不与 10 月 5 日主只读接口的计数累加；旧 affine／tiling 到主只读接口的迁移仍需单独验收。

[检查前缀实例](memory-prefiltered-versions.md)进一步通过同一端点和同源完整程序验证。在这批测试中，候选选择相同且 alias 查询减少约 11.2%，代码文本增大；结构正确性不保证一般接受范围或运行时间改善。这是框架检查组合与具体检查策略的实现证据，不构成文献新颖性结论。

[带入口起点的片段](memory-started-fragments.md)将源正常执行可提供的实际访问域限制落实到运行时检查与候选：检查枚举 `[start, upper)`，不要求源没有访问的前缀具有权限。该实例共享原抽象核心及 Csem→Asm 端点，并实际验证非零起点的候选执行；负根和负地址参数仍回退。407 模块／557 证明源码的审计保持既有 42 项完整程序假设。这是具体语言实例的表达范围扩展，文献定位及新颖性结论仍需独立论证。

[有符号窗口实例](memory-signed-windows.md)已通过实际源和候选对应、条件定义性及真实检查编码、统一 Csem→Asm 证明、440 模块／590 证明源码审计和 7982 次完整汇编调用。3238 次实际分支诊断覆盖负根、负参数和负下标快路，34 个未定义参数入口实际执行零次参数测试。单指针路线使用静态单元分离，依赖验证保持独立。[有符号分块](memory-signed-tiling.md)随后也进入实际候选、lowering 和完整程序证明，442 模块／592 源码审计保持原有假设，完整汇编验证已通过。该阶段之后的多指针 signed 快路见下文；更一般深层仿射域仍在推进。这些实例扩大具体语言实例的表达范围，不构成独立的文献新颖性结论。

[有符号多指针实例](memory-signed-multiple-pointers.md)随后进入同一源／候选桥、实际运行时检查与 Csem→Asm 端点。461 模块／611 证明源码的干净全量审计保持原有假设；14 种配置通过 9660 次实际汇编调用，5644 次分支诊断覆盖负根、共享存储分离和真实重叠回退。检查枚举源本次实际足迹，保留完整二次扫描与只读别名保守拒绝。这一实例验证语言实例可为抽象有状态框架提供更宽的语义性质，并不单独建立相对既有工作的文献新颖性。

## 2026-10-05：基于实际证据的修订结论

逐能力与五个近邻的 evidence-to-claim matrix 见 [2026-10-05 证据矩阵](evidence-to-claim-2026-10-05.md)。以下结论以 main `cf4d442` 为固定证据基线；此前表格保留为 10 月 2–3 日历史阶段，不代表 10 月 5 日支持范围。

截至 2026-10-05、固定 main `cf4d442`，GuardCert 已不止是“连接条件仿真、guard 与上下文”的可行性原型：它具有实际被提取编译入口消费的只读前缀扫描、部分探针语义下保持结果与安全的条件简化、保持原规则证书的共享出口 lowering，以及单／双 memory-loaded bounds、有限参数 stride 和多 cache 的真实 Clight 使用者。最具体的证据是：检查不预先假定完整稳定 footprint，而从实际源剩余执行取得当前点的定义性与权限依据，仅在已完成 non-alias 检查后运输 load 稳定性并推进下一点；接受后才执行缓存或调度候选，拒绝时保留真实源片段及其公开出口。相同设施已经连接完整 Csem→Asm backward simulation 和原生行为回归。

这些结果支持一项限定范围的 artifact 主张：**GuardCert 在已支持的 Clight 模板内，机械连接源路径提供的检查依据、有限只读条件生成及安全后处理、条件性局部变换和真实宿主安装，并复用其检查及上下文证书。** 它们尚不自动支持文献新颖性。CGO 2017 已有假设组织、简化、检查生成与安全／依赖 preload；COVE/cSTOKE 已有条件候选验证和动态回退；CoreJIT 已机械证明安全 guard 插入与去优化；Chamois 和 Peek 已覆盖不同形式的局部验证与全程序连接。C／Clight 层、generic kernel／host adapter 分工、动态前提、安全 guard、共享出口和多次 pass 组合均不能单独作为首创依据。

当前最值得检验的研究差异是：**如何把真实源路径逐步提供的定义性、权限与稳定性证据组织为可复用的检查构造接口，并在保持部分求值安全的同时复用原条件规则证书完成生成、简化和 lowering。** 这是已有算法和机械证明边界之间的具体比较问题，而非已证实的空白。需要以同一个 alias-sensitive loaded-bound 例子对照 CGO／CoreJIT 的义务，并直接核对 Chamois／Peek 可复用的接口；后者未核实的部分必须标为未知，不能据此声称缺失。

现有边界必须同时保留：宏片段宿主仍要求源独立进展；有限求值宿主不代表一般发散宏片段已覆盖；双动态矩形选择器要求 extent≤12、静态 stride 和受限 body；loaded bound 与参数 stride 的有限组合不能推广成双 loaded 与参数 stride 的一般同次组合。一般 buffer、多个依赖 preload、复杂 body、旧 affine／tiling 到主只读接口迁移和更一般条件发现仍未完成。共享出口与探针简化已有指定 fixture 的静态 Clight 体积结果，没有运行性能或普遍代码规模结论；审计记录说明未增加全局公理，但沿用既有假设和工具链信任边界。

因此，实际研究主张应建立在上述**已实现的证据处理算法与真实语义实例**上，并把“可复用源路径证据是否降低证明负担、是否能以可接受成本扩展优化覆盖”保留为待验证问题。整体呈现仍是语言无关框架与困难 CompCert 实例共同构成论证；证据矩阵用于检验这项叙事中的具体增量，不将框架缩成单条条件组合定理，也不让核承担 domain 特有的假设发现。若同例比较表明这些义务可以通过已有接口直接得到，项目仍有经过验证的工程价值，但应继续寻找具体增量，不将未验证的覆盖或首创写入论文。

## 评审之后的实现更新

上述 10 月 5 日评审结论固定于 `cf4d442`。后续新增 `open_region_protocol`／`open_region_contract`，已经编译验证整段局部小步宿主、unsigned memory-bound 缓存规则、真实源／guarded 目标 alias 无限执行，以及完整 Csem→Asm 端点。它不要求原片段的无条件完成性，见[实际案例](clight-guarded-circular-case.md)。这关闭一个具体宿主缺口；不据此宣称新的抽象 guard 定理、一般多面体迁移或文献空白。提取／原生结果与当前计数以[阶段记录](research-checkpoint-2026-10-05.md)为准。
