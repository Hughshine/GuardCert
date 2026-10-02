# 进一步核对：性质传递与状态关系的已有工作

2026-10-02。本页补充 overnight 研究中核对的 primary sources，并区分已读内容和后续判断。

## 静态分析性质到低层表示

Barthe、Blazy、Laporte、Pichardie、Trieu 的 [Verified Translation Validation of Static Analyses，CSF 2017](https://software.imdea.org/events/software-seminars/2017/06-27/) 已提供 CompCert／Verasco 中传递分析性质的方法：defensive form 加入运行时检查，再由 relational relative-safety checker 验证低层表示。客户端包含 RTL 优化及更低层的安全／内存分析。

本次读取官方研究所摘要及 [Blazy 的作者报告](https://mw.hh.se/wg211/images/b/b6/M18Blazy-Slides.pdf) 第 11–13 页。报告用 `assert` 把可执行性质编码到程序，再运输安全性。论文 HAL 全文入口当前拒绝访问；没有据此声称已审计完整 Rocq artifact。

对本项目的推论：可执行性质编码、关系式核对和 CompCert 组合已有强先例。应具体比较检查是证明运输载体还是最终部署的分支选择，以及是否生成保留源程序的候选／fallback；仅凭报告不能认定其没有后者。

## 隐藏状态与开放模块组合

Zhang、Wang、Wu、Koenig、Shao 的 [Fully Composable and Adequate Verified Compilation with Direct Refinements between Open Modules](https://arxiv.org/html/2302.12990v5) 提供带 memory protection 的 Kripke 关系 `injp`，用同一关系表示 compiler passes 的 rely/guarantee，并支持直接 refinement 的纵向与横向组合。论文应用到 Clight 起点的完整 CompCert 链。

本次读取摘要、§2.1.2 与 §§3–4 的接口重点，没有运行 artifact。对本项目的推论：任意内存表示变化与 external calls 不能只要求状态相等；宿主接口可能需要保护私有状态、允许关系演进。不过当前检查／回退的纯 guard 核不必理解 injection，具体宿主可以提供对应契约。不能把一般开放模块组合再次当作独有贡献。

## 非优化变换与 definedness

Monniaux 的 [Memory Simulations, Security and Optimization in a Verified Compiler，CPP 2024](https://arxiv.org/html/2312.08117v1) 解释 CompCert 中 stack canaries、pointer authentication 与 tail recursion elimination 的证明。重点包含 memory extension／injection、私有状态以及 `Vundef` 的 definedness refinement。

本次读取 §§2–3 的语义与 canary 证明描述，以及 simulation 相关段落。对本项目的推论：性质检查和状态关系可以服务安全插桩，但 guard 失败调用错误处理与失败运行源片段属于不同协议。必须分别声明行为目标；不能从当前纯检查／源式回退端点自动推出安全 enforcement 或常量时间性质。

## 对实现的影响

通用核消费语言提供的性质、检查原语、条件选择及证据。具体宿主处理有定义入口、观察、临时状态、labels、calls 和 program simulation。新嵌套循环桥接已处理指定 live frame 下的 scratch 变化；它不等于一般 memory injection 或开放模块组合。

候选贡献仍是可运行、已验证的前提处理与检查编译，配合条件证书及明确宿主范围的复用。候选前提发现、tiling 表达式、具体内存实例与多语句区域的端到端实例需要继续实现，才能评估相对先例的增量。
