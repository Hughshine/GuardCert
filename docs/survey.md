# 文献初查与需求

核对日期：2026-10-01。范围是与“带前提的局部优化如何得到完整程序保证”直接相关的代表性工作，并非系统性、穷尽性综述。下文区分论文中的数学论证、机器检查证明和实现证据；不把运行时验证假设等同于形式化验证编译器。

2026-10-02 补充：研究对象扩展为带条件的表达式、语句和区域 rewrite；[intro.md](intro.md) 提供动机草稿，[presumptions.md](presumptions.md) 先分类前提表达能力，再分别定义编码、入口推导和条件合成。已复核 IMPACT 2012 §6 的 flag 语义及 conjecture 边界。

同日第二轮核对：加入 verified peephole、非优化场景与新颖性分析，见 [跨领域 survey](survey-general.md) 和 [已有覆盖与候选问题](research-position.md)。后者收紧本文的候选定位：通用局部到全程序的连接已有直接先例，增量必须体现在具体前提处理算法及其证明。

## 以用户指定的 CGO 2017 论文为主线

用户给出的 ACM DOI `10.5555/3049832.3049864` 对应 **Optimistic Loop Optimization**，作者 Johannes Doerfert、Tobias Grosser、Sebastian Hack，CGO 2017，292–304 页。全文可从[作者提供的 PDF](https://pollylabs.org/publications/grosser-2017-Optimistic-Loop-Optimization.pdf) 阅读；[爱丁堡大学记录](https://www.research.ed.ac.uk/en/publications/optimistic-loop-optimization/)可交叉核对元数据。IEEE DOI 为 `10.1109/CGO.2017.7863748`。

论文已经提出统一的假设收集、泛化、简化与 guard 生成流程，并在 Polly 实现。假设可来自建模和变换，覆盖不变读取、算术语义、循环有界性、多维下标与别名。§6 特别处理检查自身的回绕，以及提前读取参数的安全性。因此，“统一管理乐观优化前提”本身已有直接先例。我们要考察的是如何把这一流程的语义义务机械化，并连接到 CompCert 的完整程序证明。[全文 §§2、4–6](https://pollylabs.org/publications/grosser-2017-Optimistic-Loop-Optimization.pdf)

这里有一个容易混淆的细节：用于多维数组恢复的每维下标约束，与真实分配对象的访问权限、地址计算安全，是不同的义务。框架应分别表达，不能用一个笼统的 `in_bounds` 命题替代。[全文 §4.5](https://pollylabs.org/publications/grosser-2017-Optimistic-Loop-Optimization.pdf)

## 相关工作地图

“阅读依据”表示本轮实际核对的范围；“未形成该保证”只描述这些来源中的证明边界，不断言后续版本也没有。

| 工作 | 对本问题的作用与边界 | 阅读依据 |
| --- | --- | --- |
| Cuervo Parrino、Narboux、Violard、Magaud，IMPACT 2012，[Dealing with arithmetic overflows in the polyhedral model](https://acohen.gitlabpages.inria.fr/impact/impact2012/workshop_IMPACT/cuervo.pdf) | oracle 提出参数条件，版本化代码由验证器检查；必须关注源与生成代码的控制算术。论文明确说验证器正确性证明尚未完成。Coq 实现不能自动等于正确性证明。 | 全文，重点 §§3、8 |
| Doerfert、Hammacher、Streit、Hack，IMPACT 2013，[SPolly: Speculative Optimizations in the Polyhedral Model](https://www.st.cs.uni-saarland.de/publications/files/doerfert-impact-2013.pdf) | 运行时信息与函数特化可扩大可优化片段的范围；说明输入片段识别也可带假设。不是这里需要的 CompCert 上下文定理。 | 摘要与方案部分 |
| Tristan、Leroy，PLDI 2009，[Verified Validation of Lazy Code Motion](https://xavierleroy.org/publi/validation-LCM.pdf) | CompCert 中已验证的翻译验证：复杂优化器可不受信任。其提前求值安全问题与 guard preload 密切相关，尤其不能把会失败的读取移到源程序发散之前。 | 摘要、引言 |
| Tristan、Leroy，POPL 2010，[A Simple, Verified Validator for Software Pipelining](https://xavierleroy.org/publi/validation-softpipe.pdf) | 符号执行与活跃变量关系支持局部块验证。但 §6.2 将从展开块提升到真实循环的结果明确列为当时未在 Coq 中证明的部分。局部验证和完整循环证明必须分别验收。 | 全文重点 §6 |
| Flückiger 等，POPL 2018，[Correctness of Speculative Optimizations with Dynamic Deoptimization](https://arxiv.org/abs/1711.03050) | 版本等价、假设透明性与去优化状态重建；提供中途失败恢复的语义框架和双模拟论证。不能把它简化为入口处 `if`。 | 全文重点 §§3–6 |
| Barrière 等，POPL 2021，[Formally Verified Speculation and Deoptimization in a JIT Compiler](https://www.o1o.ch/about/assets/courir.pdf)（CoreJIT） | Coq 中验证推测与去优化，连接局部优化、同步点和动态编译执行。该论文的原生代码执行仍在证明范围之外。 | 全文重点 §4；[代码](https://github.com/Aurele-Barriere/CoreJIT) |
| Six 等，CPP 2022，[Formally Verified Superblock Scheduling](https://popl22.sigplan.org/details/CPP-2022-papers/13/Formally-Verified-Superblock-Scheduling) | CompCert 中跨分支调度、符号执行与活跃变量验证，提供实际完整编译链的经验。这里的 speculative scheduling 不能自动解释成运行时假设与去优化。 | 官方摘要、[作者代码文档](https://www-verimag.imag.fr/~boulme/CPP_2022/) |
| Gourdin 等，OOPSLA 2023，[Formally Verifying Optimizations with Block Simulations](https://doi.org/10.1145/3622799) | Chamois/CompCert 的通用块仿真验证框架，已覆盖局部块到 CFG 的复用；候选不变量与 CFG 映射可由 oracle 提供。“通用局部证明框架”也已有直接先例。 | 摘要、[作者海报](https://www-verimag.imag.fr/~boulme/pub/poster_OOPSLA23.pdf)；10-02 补读当前 BTL 语义和 [oracle 类型](https://certicompil.gricad-pages.univ-grenoble-alpes.fr/Chamois-CompCert/html/ocaml/BTL_BlockOptimizer.html)，未取得论文全文及部分核心证明模块正文 |
| Barrière、Blazy、Pichardie，POPL 2023，[Formally Verified Native Code Generation in an Effectful JIT](https://aurele-barriere.github.io/papers/fmjit.pdf)（FM-JIT） | 通过效果抽象和精化连接 JIT 执行与 CompCert 原生代码生成。证明边界仍要区分原语规格及其 C 实现。为未来接入 backend 提供具体路线。 | 全文重点 §§3.4、4.5–4.6 |
| Stewart、Beringer、Cuellar、Appel，POPL 2015，[Compositional CompCert](https://www.cs.princeton.edu/~appel/papers/compcomp.pdf) | 结构化内存关系与垂直、水平组合；为上下文可见内存和私有状态提供依据。模块链接的组合性并不直接等于函数内部片段替换。 | 全文重点 §§4–5 |
| Menendez、Nagarakatte，PLDI 2017，[ALIVE-INFER](https://people.cs.rutgers.edu/~santosh.nagarakatte/papers/pldi2017-alive-infer.pdf) | 自动推断优化前提，并检查定义性与结果精化。主要是编译期优化规则前提，不能把所得条件直接当作已验证的运行时 guard。 | 全文重点 §§2–3 |
| Lopes 等，PLDI 2021，[Alive2: Bounded Translation Validation for LLVM](https://users.cs.utah.edu/~regehr/alive2-pldi21.pdf) | 很适合发现候选规则和 guard 的反例；有界展开意味着不能替代一般循环的机械证明。 | 摘要与方法范围说明 |
| Anand 等，PLDI 2024，[Optimistic Stack Allocation and Dynamic Heapification for Managed Runtimes](https://www.cse.iitm.ac.in/~krishna/preprints/pldi24/pldi24.pdf) | 乐观优化也可改变对象表示，并在逃逸时恢复堆表示。入口检查与状态全等不足以涵盖这一类；其 §5.1 给出证明概述，并非本文所需的 CompCert 机械证明。 | 全文重点 §5.1 |

## 从这些工作推导的框架需求

以下是我们的需求归纳。它们是跨论文的设计判断，不是任何单篇论文的原文主张。

1. **前提是一份可核对的语义契约。** 除源程序建模假设外，还要包含变换新引入的条件，例如新下标、展开步长、临时表达式的范围。不需要假定整个程序所有算术均不溢出；需要精确覆盖实际证明依赖的运算。
2. **推断、验证与执行分层。** 编译期验证器检查“这个候选在这些前提下正确”；运行时 guard 检查“这次进入是否满足前提”。oracle 可以复杂且不受信任，但不能绕过前一个证明义务。
3. **接受可靠，拒绝可保守。** guard 接受必须推出所需前提。拒绝包括假设不成立、检查算术无法安全求值、无法安全 preload；全部可以回退。无须首先证明 guard 是最弱前提或在所有合法输入上都会接受。
4. **检查代码具有自己的语义。** 符号公式为真不等于实际机器代码判断正确。宽度、符号、短路、地址计算和读取权限都必须在实现层验证。检查不能新引入可观察事件、破坏 live-in，或在原代码不会访问的位置先发生错误。
5. **前提必须覆盖有效期。** 入口状态中的谓词，要能推出整个片段内所需性质。片段再次进入时重新检查；想跨入口缓存，就额外证明被依赖的状态没有失效。中途才会失效的性质需要去优化或其他恢复协议。
6. **片段接口包括状态、轨迹和控制出口。** 仅比较某个结果变量不足以支持上下文替换。要包含 live-out、上下文可见内存、返回/跳转/异常出口、调用交互，以及发散和静默步骤的进展条件。
7. **替换有明确的适用上下文。** 单入口、多出口通常足够；必须排除外部跳转直接进入内部、漏掉 `break`/`continue`/`goto` 或调用续体。入口和出口映射不能留给非形式化的 glue code。
8. **证书绑定实际被替换的代码。** 与旧片段证明相配的证书，不能用于修改后的片段或另一位置。多个位置、多次 pass 的组合需要证明绑定和前提更新，而不是累计一组未经重新核对的 flags。
9. **明确选择证明强度。** 首个原型可用精确等价；真实 CompCert 接口通常需要精化及状态关系。源程序 undefined behavior、目标可观察行为和源/目标内存表示不能混成一个“结果相同”。

## 候选研究定位

初查提出的定位是为 CompCert 中带运行时前提的局部变换，连接条件仿真、可执行 guard 和上下文替换。第二轮核对确认：这条表述与 Peek、Chamois、CoreJIT 等工作有大量重叠，不能直接作为新颖性主张。

较具体的候选是：同一条件规则证书如何用于静态证据与残留运行时检查，以及如何验证编码、入口推导、检查编译和证据使用位置。这个问题仍需对比最接近工作的实际算法；不能以“动态前提”或“安全 guard”几个词认定已有空隙。分层、实例与否定标准见 [研究定位](research-position.md)。

最有说服力的验证应使用至少两个性质不同的优化插件，共享同一个上下文定理，接入一个真实 CompCert IR。应同时展示非法输入回退、检查自身失败回退和完整程序行为保证。只在 Loop IR 中证明最终状态相同，或只证明 guard 返回 `true` 时公式为真，都不能单独满足这个目标。
