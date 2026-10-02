# 从候选变换到带检查的程序

2026-10-02 的需求与设计补充。本文记录新的文献核对和拟议接口；**没有新增候选条件推断器或 Rocq 定理**。当前实现仍是规则作者提供语义前提和局部证明，框架合成抽象 condition，并用手写 lowering 证书连接真实 Clight。

## 研究对象

给定原片段 S 和候选 T，在明确的前提语言及片段接口中，寻找足以保证 T 精化 S 的入口条件 A，生成检查 A 的实际代码 G，再构造：

```text
if G then T else S
```

最终目标是这个新片段在允许的上下文中精化 S，并与 CompCert 后端正确性组合。候选可以来自优化器、人工修改、搜索、LLM 或实现替换；条件化与验证不应依赖候选产生过程已经保持正确。

这包含两种不同的前提来源：已知变换算法可以输出自己的证明义务；给定一对片段则需要关系式分析推断成立域。两者应在条件证书之后共享编码、检查生成和宿主组合。不能把已实现的“给定 presumption 编译 Bool”称为已经解决“给定代码对发现前提”。

## 比 CGO 2017 更直接的另一条文献线

| 工作 | 核对依据 | 对本问题的覆盖与边界 |
| --- | --- | --- |
| Sharma、Schkufza、Churchill、Aiken，OOPSLA 2015，[Conditionally Correct Superoptimization](https://theory.stanford.edu/~aiken/publications/papers/oopsla15a.pdf)（cSTOKE/COVE） | 全文重点 §§2–3、5.3、5.5 | 从原/候选 x86 代码及测试推断前提，用 SMT 检查条件正确性，涵盖别名、对齐和值域等。§5.5 的运行时检查是手写 C 后编译拼接；没有这里要求的机械化检查生成与上下文证明链。部分浮点实例显式使用 unsafe axioms，不能当作一般 IEEE 等价保证 |
| Kawaguchi、Lahiri、Rebêlo，2010，[Conditional Equivalence](https://www.microsoft.com/en-us/research/publication/conditional-equivalence/)（MSR-TR-2010-119） | [全文](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/paper-69.pdf) §§4.2–4.4、5.1 | 面向重构和程序演化，提出组合验证与抽象域参数化的条件推断。§5.1 明确说抽象不动点推断未实现；其 partial equivalence 允许任一版本发散，不能直接作为完整行为精化的证书 |
| Steinhöfel、Hähnle，JAR 2024，[Schematic Program Proofs with Abstract Execution](https://link.springer.com/article/10.1007/s10817-023-09692-0) | 全文引言、§5.1 | 通过失败证明的反馈寻找重构规则所需条件，包含 footprint、异常和副作用。说明前提发现不局限于编译优化；这些语义条件不都能变成廉价入口检查 |
| Barrett、Goldberg、Zuck，RV 2003，[Run-Time Validation of Speculative Optimizations using CVC](https://theory.stanford.edu/~barrett/pubs/BGZ03.pdf) | 正文引言与生成算法的检索核对 | 从循环置换验证义务自动推导运行时测试，并考虑恢复。是 CGO 之前的相关谱系；仍以循环变换为主题，不能用来替代非循环实例 |

COVE 尤其重要：论文 §2 明确区分“已知规则及其条件”与“没有变换历史的任意候选序列”。因此，人工/机器候选的条件化是合理的使用场景，但 **source/candidate → 条件 → 运行时回退** 这条概念流程本身已有先例。需要检验的增量是其中哪些算法及真实语义连接获得了机械保证、可复用性和新的适用能力。

## CoreJIT 与 Alive2 的区别

| 系统 | 核心输入与任务 | 正确性依据 |
| --- | --- | --- |
| [CoreJIT，POPL 2021](https://www.o1o.ch/about/assets/courir.pdf) | profiler 提供优化意图、guard 和位置；已实现 passes 插入 Assume、传播事实、内联并维护去优化 metadata | 这些 passes 与 JIT 执行的 Coq 仿真证明 |
| [Alive2，PLDI 2021](https://users.cs.utah.edu/~regehr/alive2-pldi21.pdf) | 给定源/目标 LLVM 函数，检查 refinement | SMT 翻译验证；循环有界；论文不是已验证验证器实现 |
| [AliveInLean，CAV 2019](https://web.ist.utl.pt/nuno.lopes/pubs.php?id=aliveinlean-cav19) | LLVM peephole 规则验证 | 已验证验证器，保证以 SMT 正确消解义务为前提 |
| COVE，OOPSLA 2015 | 给定原/候选、测试，推断并验证条件正确性 | 抽象解释、测试与 SMT；动态检查实验采用手写代码 |

“验证变换是否保持行为”是共同点，但 CoreJIT 不提供任意代码对的通用验证器。其关键对象还有运行中改变代码、失败时重建当前状态与活动栈。我们的候选验证入口更接近条件翻译验证；若以后支持中途失败恢复，CoreJIT 则提供更直接的协议与证明参考。

## Peek 的相似层与差异层

[Peek，PLDI 2016](https://darzu.io/files/pldi2016.pdf) 的局部 rewrite 到全程序定理是应复用的先例。它工作在 CompCert 汇编，借助已验证的静态活跃性分析允许死寄存器变化；这并不是运行时状态谓词的测试。论文没有提供从 presumption 到动态 guard 及原片段回退的通用生成接口。

两个层次可以同时需要：

- 静态接口证明说明哪些位置可改变、哪些入口/出口合法以及上下文会观察什么。
- 运行时条件说明这一次进入时值域、别名或函数身份是否满足候选的语义条件。

因此，GuardCert 不应声称不需要活跃性或 frame 证据；也不能把提供局部到全程序定理当作新贡献。新增 guard 会引入检查安全、代码增长、辅助状态和控制流义务，仅换一个 IR 不会自动解决它们。Peek 可以作为宿主层的技术参考，不能直接等同于整个候选条件化服务。

## 三种使用入口

| 入口 | 用户或工具提供 | 框架完成的目标 |
| --- | --- | --- |
| 规则入口 | S/T 模式、前提 AST、条件局部证书 | 实例化、静态消解、检查生成与插入 |
| 候选入口 | S、T、观察/frame/控制接口，可选测试和分析 witness | 在受限 DSL 中提议条件，核对条件局部证书，再复用后续链 |
| 检查入口 | S、T、提议的条件或 guard | 验证其语义和执行安全，再完成插入与组合 |

候选入口的概念签名可以是：

```text
guardify(host, source, candidate, interface, condition_domain, hints)
  : Reject reason
  | Certified(guarded_fragment, condition, certificate)
```

它不保证对所有候选成功。推断可以由不受信任的搜索器提出条件和 witness，再由已验证 checker 或 proof-producing 流程核对。测试可用于选择有用条件、发现反例和扩大接受域，不承担普遍正确性。SMT 若纳入可信边界，应明确说明；若要求保持当前 Rocq 证明边界，应验证其证书或重建证明。

证书要覆盖条件下的局部精化、编码对应、检查安全、回退状态、控制出口和进展，再由 Host 提升到完整程序。永久为假的条件虽然安全，但无应用价值；应对指定的条件域和实例报告接受率、检查成本和拒绝原因，不承诺任意程序的最弱条件合成。

## 人工候选示例

考虑所有运算均为 `uint32_t` 的表达式：

```c
/* source */    (x + x) / 2u
/* candidate */ x
```

候选入口应尝试发现充分条件 `x <= 0x7fffffffu`，核对模 2^32 算术下的条件等价，再生成：

```c
x <= 0x7fffffffu ? x : (x + x) / 2u
```

这同时要求检查不先计算可能回绕的 `x+x` 来错误判断“数学上不回绕”。当前原型已经有这条规则及端到端接入，但前提和 lowering 由作者提供；**还没有从这两个表达式自动发现条件**。该例用于验证接口，研究评估还需要内存或调用类实例。

第一版可采用三类场景：整数表达式/路径 rewrite、字节访问不相交下的读取消除、函数身份或表示条件下的快速路径。前两者已有不同程度的原型基础，第三者要求扩展代码环境与调用接口。重构、库实现替换可提供候选；具体是否支持，取决于其副作用、异常、终止性和前提能否被当前 Host 与条件域表达。它们是设计用例，不是现有已实现能力。
