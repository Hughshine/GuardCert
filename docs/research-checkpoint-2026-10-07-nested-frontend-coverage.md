# 阶段记录：实际数组 BODY、完整上下文及前提收紧

日期：2026-10-07。父版本 `cc02ac738a2ca9cb7c0360341955146b838d69ea`。
完整研究目标继续 active；本记录固定本阶段证据，不代表完成 PolCert 基本能力
或 OLO usability 的全部验收。

## Narrative 核对与执行决策

重新 fetch 后，`origin/topdown/research-positioning` 为
`271f6fc941910456da43a76e9f0eed38e8a5e200`。main 中的
[paper narrative](topdown/paper-narrative.md) 与
[context-lifting](topdown/context-lifting.md) 正文直接 diff 无差异。
本轮落实到 [当前计划](current-work-plan.md)、
[责任说明](framework-responsibilities.md) 和
[实现核对](narrative-implementation-check-2026-10-06.md)：

- 最小 kernel 消费证书并证明局部 guarded correctness。条件处理属于上层库；
  语言宿主另证分派、状态运输和整程序安装，实例提供 region／site 证据。
- 三方责任与四个逻辑环节不一一对应，不要求使用者手填四个重复 record。
  Source/model 对应、检查安全、progress／control 不能藏进未经证明的 callback。
- 扫描是证明链闭合后的中间实现。后续 compact condition 必须另证安全、
  accepts⇒模型义务及实际入口运输；新旧接受域无需相同，也不要求最弱条件。
- OLO 的功能和 usability 分开验收；代码大小、runtime check work、完整成本、
  有用接受域和作者证据负担分别报告。Contract clauses 重构仍由真实 host
  的重复和语义差异驱动；当前不增加 kernel 抽象或第二 IR。

## 本阶段能力

同一实际 C frontend／提取 compiler 运行七类函数：in-place update、多数组
读写、真实 dependence chain、constant stores、active 才定义的 BODY scalar、
两次 guarded sites，以及包含 prefix effects／pre-loop return／post-loop return
的完整函数。Alias、同 allocation 分离 slices、非零入口 row、空循环、loaded
offset wrap、BODY stored-value wrap 及 profile 的 exclusive 上界均有输入。
详见 [coverage](nested-frontend-coverage.md)。

原 default profile 静态不安装 chain 的 interchange／tiling。两个明确无 guard
的错误变体经同一 compiler 的 disabled 模式编译到 assembly，在指定输入上
分别改变 30／5 个数组 words，证明这是真依赖反例。这里观察的是 pipeline
拒绝，未断言某一个内部 checker 分支的返回值。

优化方再提出 child-count∈[1,2) 的更强前提，root-count∈[1,5) 不变。
同一 checker 接受 chain 的重排，同一 guard producer 编码较窄前提：三行
一列输入走候选，原反例输入回退原 AST。Guard 仍包含有序 capture、numeric
及 header stability／alias 义务。没有新增通用前提发现、WP 或最优 guard。

Compiler／Rocq／kernel 不变。仍调用
`ClightGuardedNestedFrontendCompiler.compile_ncs_frontend_regions`，成功输出
由 `compile_ncs_frontend_regions_correct` 连接 Csem→Asm backward simulation。
父阶段 proof closure 20 endpoints／569 dependencies／1,104 source digests、
同一 42-global compiler baseline 及零新增 global axiom 的绑定保持。
新实验是已有定理下的行为覆盖，不是新增 proof endpoints。

## 验证与证据边界

| 新实验 | 结果与范围 |
| --- | --- |
| Default profile | 6 配置×119 输入＝714 full assembly calls |
| 错误无 guard 变体 | 另 2 assembly counterexample calls，不算成功优化 |
| Default Clight | 357 calls／370 dispatches，147 fast／223 refusals |
| Default machine paths | 另 10 GDB probes，观察三个指定位置的 stores |
| One-column profile | 238 full assembly calls，全部七类函数安装候选 |
| One-column Clight | 238 calls，每配置 16 fast／118 refusals |

每次完整调用核对 A 的 6,144 words、B／C 各 2,048 words、headers、public
counters 与 context markers，先比较 GCC wrapping-arithmetic reference 和独立
动态 source-word model。Clight 插桩只作分支证据；GDB 观察未插桩 assembly 的
三个位置，不能说成全部 store trace。较窄 profile 没有额外 GDB probes。

`make nested-frontend-validate nested-frontend-coverage-validate` 通过。报告绑定
source／helpers、原 compiler／proof、配置、model、全数组输出与 probe artifacts；
各 SHA 见 coverage 文档。Compiler SHA 保持
`04d799e2617550ec5895fdb2b27cf8319c1796e6ee41e831baae30173329e478`。
旧 OLO 16-call report、父阶段 75-call native／16-call Clight／6-probe 报告均
固定保留，不借后继结果改写旧阶段能力。

实际 manuscript 的 introduction／case study／evaluation 与 evidence map 已更新。
离线 Tectonic 编译 14 页并核对变更页，source／evidence bindings 一致；paper
report SHA 为 `d3bdb12352191f753c4f11da0a4e5031d9b73f7827b0f549a3ae326f04323dba`。
该报告不重跑研究实验。

## 剩余工作

先建立 fresh-checkout empty-build 路径。随后在同例实现并证明 compact
sufficient conditions，测量实际检查成本、完整成本、接受域与作者证据负担，
复用既有候选／host 证明。更广 affine/polyhedral source、参数化域变换及
完整原 BT 的动态布局／delinearization 仍需推进。当前固定 flat-stride profile
和运行次数不能证明这些能力；没有 timing／profitability 或最终 novelty 结论。
