# 跨领域的带前提变换：文献与需求

核对日期：2026-10-02。本文扩展 [最初的编译优化 survey](survey.md)，覆盖名称中不含 optimistic 的工作。研究新颖性判断见 [已有覆盖与候选问题](research-position.md)。这是一份代表性 survey，不是证明“相关文献已穷尽”的系统综述。

检索词包括 conditional rewrite、peephole、precondition inference、schematic program transformation、refactoring、hybrid type checking、gradual verification、change contract、repair、dynamic software update、runtime enforcement、representation independence、approximate compilation、query rewrite 与 transactional correctness。优先使用作者论文、官方出版页面和公开源码文档。

同日追加检索 conditional equivalence、conditionally correct superoptimization 与 run-time validation，补足“给定独立候选，再寻找成立域”的谱系。新的接口比较见 [候选条件化设计](candidate-conditioning.md)。

## 扩展文献表

“核对范围”区分全文中的选定部分、摘要和源码接口。后者不足以支持“该工作完全没有某项能力”的否定结论。未在本项目构建这些外部 artifacts。

| 工作 | 本轮核对范围 | 已有能力及对接口的要求 |
| --- | --- | --- |
| Sharma 等，OOPSLA 2015，[Conditionally Correct Superoptimization](https://theory.stanford.edu/~aiken/publications/papers/oopsla15a.pdf)（COVE/cSTOKE） | 全文重点 §§2–3、5.3、5.5 | 独立候选的条件推断与 SMT 验证；动态检查实验手写 C 并编译拼接。比单纯已知规则应用更直接对应人工/机器候选入口；部分浮点实例显式使用 unsafe axioms |
| Kawaguchi 等，2010，[Conditional Equivalence](https://www.microsoft.com/en-us/research/publication/conditional-equivalence/) | [全文](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/paper-69.pdf) §§4.2–4.4、5.1 | 非优化的程序演化与条件等价。论文推断算法和 prototype 支持要区分；抽象不动点推断未实现，partial equivalence 允许任一版本发散 |
| Barrett 等，RV 2003，[Run-Time Validation of Speculative Optimizations using CVC](https://theory.stanford.edu/~barrett/pubs/BGZ03.pdf) | 正文引言与生成算法的检索核对 | 根据置换验证义务自动生成运行时测试，考虑恢复；是早于 CGO 的循环变换谱系 |
| Cousot、Cousot、Logozzo，VMCAI 2011，[Precondition Inference from Intermittent Assertions and Application to Contracts on Collections](https://pcousot.github.io/publications/CousotCousotLogozzo-VMCAI-LNCS-6538-pp150--168-Jan-2011.pdf) | 全文重点引言与方法范围 | 同时推断静态契约及可执行检查；条件只使用调用者可见信息，检查没有可见副作用。其非确定性契约语义与普遍条件精化需区分 |
| Dillig、Dillig、Chaudhuri，CAV 2014，[Optimal Guard Synthesis for Memory Safety](https://www.cs.utexas.edu/~swarat/pubs/CAV14-extended.pdf) | 全文重点 §§1、4–5 与 Theorem 1 | abduction、前后向分析、ghost offset/extent 与变量可观察性，生成保护内存访问的 guard；相对给定不变量证明 Pareto 最优性。带代价的 guard 合成本身已有算法先例 |
| Mullen 等，PLDI 2016，[Verified Peephole Optimizations for CompCert](https://darzu.io/files/pldi2016.pdf)（Peek） | 全文重点 §§3–5；[代码入口](https://github.com/uwplse/peek) | 局部 rewrite 证明与已验证活跃性提升到全程序。需要比较可见状态与死寄存器，不能强制全部状态相等 |
| Lee、Hur、Lopes，CAV 2019，[AliveInLean](https://web.ist.utl.pt/nuno.lopes/pubs.php?id=aliveinlean-cav19) | 作者摘要、元数据 | 已验证 peephole 验证器；SMT 消解可靠性是明确的保证前提。候选验证与运行时代码生成要分别验收 |
| Becker 等，CAV 2019，[Icing](https://cakeml.org/cav19.pdf) | 全文重点 §§2、4 | HOL4 中的条件 rewrite 与可扩展浮点语义；区分 compiler precondition 和 application precondition，不能把静态 `cond` 当成运行时 guard |
| Becker 等，ECOOP 2022，[Verified Compilation and Optimization of Floating-Point Programs in CakeML](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2022.1)（RealCake） | 官方摘要与元数据 | 实数语义到浮点机器代码的端到端 I/O 契约，结合 accuracy analysis；正确性不总是 IEEE 位级相等 |
| Steinhöfel、Hähnle，JAR 2024，[Schematic Program Proofs with Abstract Execution: Theory and Applications](https://link.springer.com/article/10.1007/s10817-023-09692-0) | HTML 全文重点引言、§5.1 | 对程序模式做关系式证明，支持重构、成本分析和并行化；需要 footprint、异常与适用条件。不是仅优化框架 |
| Flanagan，POPL 2006，[Hybrid Type Checking](https://escholarship.org/uc/item/0j63v3dn) | 作者库摘要 | refinement 条件静态尽量检查，其余动态检查；“统一静态与动态证据”已有先例。动态拒绝可产生 contract failure |
| Bader、Aldrich、Tanter，VMCAI 2018，[Gradual Program Verification](https://www.cs.cmu.edu/~aldrich/papers/vmcai2018-gradual-verification.pdf) | 全文重点 §4、§4.3 | Coq 中的渐进验证，静态信息减少动态检查；执行语义包含显式 error。论文的核心状态模型没有本项目需要的完整 CompCert heap/perms |
| Ahrendt 等，FMSD 2017，[Verifying data- and control-oriented properties combining static and runtime verification](https://link.springer.com/article/10.1007/s10703-017-0274-y)（StaRVOOrS） | HTML 全文重点 §§4、7 | 部分静态证明简化规格，残留检查交给运行时 monitor；§7 的定理保持 violating traces。不能依据早期 2015 论文的未完成证明描述其后续工作 |
| Yi、Qi、Tan、Roychoudhury，TOSEM 2015，[Software Change Contracts](https://www.jooyongyi.com/papers/TOSEM15.pdf) | 作者全文重点 §3；出版版日期 | `preserves_when` 与允许变化的前后状态/异常契约并存。修复和功能更新不能都要求与旧程序行为等价 |
| Sharma、Schemmel、Cadar，OOPSLA 2025，[P³: Reasoning about Patches via Product Programs](https://daniel.schemmel.net/publication/2025-product-programs/) | 作者摘要与元数据；[项目摘要](https://srg.doc.ic.ac.uk/publications/25-p3-oopsla.html) | 为真实 C patches 自动构造 product programs，支持 AFL++ 与 KLEE。关系式 patch 规格是直接先例；实验工具支持不等于 CompCert 式普遍正确性定理 |
| Nguyen 等，VMCAI 2021，[Automated Repair of Heap-Manipulating Programs using Deductive Synthesis](https://ilyasergey.net/assets/pdf/papers/nem-vmcai21.pdf) | 全文摘要与引言 | 从 Hoare 规格推导和验证 heap repair。修复代码满足目标规格，旧代码可能正是不满足它的程序 |
| Stoyle 等，POPL 2005，[Mutatis Mutandis: Safe and Predictable Dynamic Software Updating](https://www.cs.ucr.edu/~neamtiu/pubs/popl05stoyle.pdf) | 全文重点更新安全条件与 §4 | 更新点、旧代码访问限制和 representation converter。类型安全迁移不自动等于新旧功能相同 |
| Hayden 等，OOPSLA 2012，[Kitsune](https://www.cs.umd.edu/~mwh/papers/hayden12kitsune.html) | 作者摘要 | 显式更新点和数据迁移是实际系统接口；需要代码版本、堆状态和活动栈。不可把其工程能力等同于完整机械证明 |
| Bloem 等，TACAS 2015，[Shield Synthesis: Runtime Enforcement for Reactive Systems](https://arxiv.org/abs/1501.02573) | 作者摘要 | 持续观察并按需修正输出，目标是满足安全规格并控制偏离。失败处理可以是纠正输出，而非回退原程序 |
| Ligatti、Bauer、Walker，2005 技术报告，[Enforcing Non-safety Security Policies with Program Monitors](https://www.cs.princeton.edu/~dpw/papers/editauto-tr-720-05.pdf) | 正文摘要与 enforcement 定义 | 可插入、抑制动作，考虑无限流和 transparency。应显式区分事件策略、允许的干预与行为保持 |
| Frumin、Krebbers、Birkedal，LMCS 2021，[ReLoC Reloaded](https://iris-project.org/reloc/) | 官方论文/源码索引与实例说明 | 已有并发、高阶状态的关系式精化与表示独立性框架；泛化 state relation 并非新的主张 |
| Zhang 等，POPL 2024，[Fully Composable and Adequate Verified Compilation with Direct Refinements between Open Modules](https://flint.cs.yale.edu/flint/publications/drinjp.html) | 作者摘要与元数据 | CompCert 内存模型上的 Kripke 关系与 memory protection 支持模块组合；可见内存和开放调用已有具体语义接口 |
| Becker 等，FMCAD 2018，[A Verified Certificate Checker for Finite-Precision Error Bounds in Coq and HOL4](https://rmonat.fr/data/pubs/2018/fmcad18.pdf)（FloVer） | 全文重点 Theorem 1 | 可信 checker 接受数值范围与误差证书；目标是有限精度误差界，不是原/目标位级等价 |
| Almeida 等，USENIX Security 2016，[Verifying Constant-Time Implementations](https://www.usenix.org/conference/usenixsecurity16/technical-sessions/presentation/almeida) | 官方摘要 | product programs 验证执行观测上的 constant-time。相同功能结果不足以支持此性质；guard 本身也可能泄密 |
| Chu 等，PLDI 2017，[HoTTSQL: Proving Query Rewrites with Univalent SQL Semantics](https://homes.cs.washington.edu/~suciu/hottsql.pdf) | 全文重点完整性约束部分 | Coq 中的查询 rewrite，前提可来自 keys、functional dependencies 与 schema；结果含 bag multiplicity，不只是标量 |
| Ricciotti、Cheney，JAR 2022，[A Formalization of SQL with Nulls](https://link.springer.com/article/10.1007/s10817-022-09632-4) | 官方摘要、贡献说明 | Coq 中覆盖 NULL、三值逻辑、set/bag 等语义。说明前提库必须适配所在语言，不能套用 C 的布尔/整数模型 |
| Necula，POPL 1997，[Proof-Carrying Code](https://doi.org/10.1145/263699.263712) | 官方摘要与作者论文索引 | 安全依据可以是经可信 checker 消费的证明证据，不必是每次执行重新判断的 bool |
| Guerraoui、Kapałka，PPoPP 2008，[On the Correctness of Transactional Memory](https://kapalka.eu/files/opacity-ppopp08.pdf) | 作者 PDF 的检索摘要、出版元数据；未读取正文定理 | opacity 涉及包括中止事务在内的执行历史；终态相等和 commit 成功不足以描述 abort/retry 的正确性 |

## 按语义义务分类

以下是从上述工作及 [最初 survey](survey.md) 归纳的设计需求，不是这些论文提出的共同框架。

| 场景 | 前提/证据 | 正确性判断 | 失败或变化协议 | 现有原型的覆盖 |
| --- | --- | --- | --- | --- |
| 条件算术、死分支、代数 rewrite | 类型、范围、无回绕、路径事实 | 等价或行为精化 | 不改代码，或入口回退 | 已有标量与分支实例 |
| 别名消除、读写移动、检查消除 | 字节区间、权限、不变值、执行域 | 条件仿真，定义性与事件对应 | 入口回退；不安全检查须保守拒绝 | 数组对象的非别名检查与完整程序已接通；任意指针切片与一般提前读取仍有缺口 |
| 函数特化、间接调用、快速路径 | 函数身份、闭包环境、对象布局、CPU 能力 | 对可用代码环境的条件精化 | 通用调用/慢路径 | 当前表达式快照没有 genv；调用位置不支持 |
| 源码重构、库实现替换 | footprint、API 不变量、异常条件 | 允许上下文中的等价/精化 | 静态拒绝；必要时运行时选择 | 部分行为保持实例可复用；一般接口待扩展 |
| 私有表示变化、对象栈分配 | escape、ownership、表示关系 | 关系式精化和表示独立性 | 堆化、重建、迁移 | 全状态相等接口不足 |
| JIT 去优化 | 假设、同步点与当前状态映射 | 跨版本仿真 | 从当前检查点恢复 | 入口 fallback 不能代替 |
| 合约插桩、渐进验证 | 已证明事实、残留义务 | 类型/安全性与合约保证 | 指定的 error/blame | 原样回退不是合约失败策略 |
| 补丁和程序修复 | 变化契约、目标规格、未影响输入域 | 新规格及未影响域的保持 | 有意改变结果、异常或状态 | 与旧程序无条件仿真不适用 |
| 动态软件更新 | update point、旧引用与状态转换证据 | 更新安全；另证新功能契约 | 安装新版本并迁移状态 | 没有代码版本/活动栈迁移 |
| 运行时 enforcement | 事件历史、策略 automaton | 策略满足、transparency、偏离约束 | 抑制/插入/纠正事件 | 当前等轨迹不允许这类干预 |
| 数值近似或表示精度变换 | 输入域、范围、误差预算 | 可组合的误差/数值规格 | 更精确慢路径，或已允许的近似 | 原值相等不能表达 |
| constant-time/信息流 | 公共输入关系、观测策略 | 两次或多次运行的超性质 | 依目标安全语义定义 | 单次行为仿真不保证 guard 安全 |
| 查询重写 | schema 约束、NULL 条件、bag 语义 | 查询等价/精化 | 元数据证据或计划选择 | 可借证据协议；不能直接用 CompCert 的宿主定理 |
| 并发/事务 | ownership、版本、环境干扰、历史 | contextual refinement、opacity 等 | monitor、abort/retry、同步 | 顺序 CompCert 的定理不能直接覆盖 |

分类的关键并不是再添一批 `Atom`。它至少区分四个互相独立的选择：

1. **要保证什么：** 行为保持、新规格、允许的误差，还是执行间关系。
2. **何时得到证据：** 编译期、链接/装载时、入口、每次访问，还是持续监控。
3. **如何对应状态：** 相同可见值、live-out 关系、内存 injection、ownership、代码版本或历史。
4. **失败怎么办：** 不应用、原片段回退、检查点恢复、中止重试、迁移、报错或干预。

不能用一个 `Q : State -> Prop` 加一个入口 `bool` 无代价地覆盖全部组合。任意未来行为、终止性或信息流性质一般也不能由一个完整可判定的入口检查决定。合理的表达力目标是：明确每类判断的宿主语义与组合定理，提供可检查的前提子语言，并使不支持的情况显式拒绝。

## 对本项目的直接影响

将 umbrella 名称改为“带前提的程序变换与组合证明”是合适的；`optimistic` 描述其中一种证据与失败策略。第一条实现主线仍应是顺序 CompCert 中的行为保持变换，因为它与现有编译器定理直接组合。

扩展需求用于防止接口过早锁死：语义 snapshot 应能包含代码环境，状态关系不应永远是全等，证据不应只能是 bool，失败策略不应混为原代码回退。修复、近似与超性质需要各自的判断和 composition 结果；只把它们放入同一个 record，不等于已经统一证明。

已有工作分布广，并不自动构成空隙。决定项目价值的，应是一个具体的前提处理算法、可复用的证明及其在真实 IR 上的收益；详见 [候选研究问题](research-position.md)。
