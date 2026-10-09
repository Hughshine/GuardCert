# Narrative 澄清与当前 quotient 实现对照

本轮按用户提示重新 fetch/read narrative：可见远端仍为
`8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9`，两份 main 正文与远端一致。
这里吸收其现有澄清，不声称看到了较新提交。

1. **Kernel 止于局部正确性。** 条件库／domain derivation在kernel以上；完整程序
   安装由语言host证明。当前 native quotient 后继未改变kernel或host定律。
2. **区分三方责任与证据来源。** 原源static checker、原执行的许可、运行时capture
   和状态运输各有作用。Factory内部生产适用前提；C使用者只给标注和策略。
   `C_opt/C_derive/C_guard/C_host`不是四个必须逐site手填的records。
3. **Reusable 服务要被真实消费。** Capture relation、参数扩展和最终candidate
   checker在actual compiler proof中接线；scope/progress/公开出口由host链交付。
   Direct Clight proof与generic `guardify`调用保持区别。
4. **Repeated rewrite针对当前程序。** 本轮实测旧pass重写新q fallback；已用
   接收actual intermediate program的resolver实现默认策略，仍量化任意提议。
   不是把某一次调用的历史cache当成证明中纯callback。
5. **最难的是许可—条件—入口—continuation链。** 当前q服务证明机器操作安全、
   private frame及actual fixed-parameter candidate执行；它未扩大loaded child
   headers或动态pointer alias。下一源族扩展必须同时闭合这些义务。
6. **功能、成本与贡献分开验收。** [新build证据](quotient-double-tiling.md)显示
   11原例27处q版本与完整程序路径；总coverage仍14/62，完整调用慢1.300657倍。
   这不能代替广泛PolCert/OLO功能、useful costs或已有工作对比。

吸纳后的执行顺序见[工作计划](current-work-plan.md)和
[benchmark验收](benchmark-alignment.md)：优先实际原语料/configuration缺口，
每条扩展立即连接完整程序；同时减少实际条件/点执行工作。条件库分类和contract
整理以实际共享和blocker为依据，不能变成推迟optimizer接线的新前置要求。
原BT、LLVM/SPEC、larger tiers以及其他顺序变换仍在active goal中。

## Literal promotion后继对两项澄清的具体落实

再次fetch仍见同一narrative，没有声称看到更晚提交。
[新后继](double-literal-operands.md)从原fusion5的实际拒绝出发，消费language的
实际Clight expression/assignment forward证明，再通过已有host安装，在所得
当前program上运行domain optimizer，连接最初C输入的Csem→Asm。这展示的是
具体证明服务和host的复用；不是kernel新定律，也不是新增runtime guard类别。

局部表达式定理的前提是原source execution和cast；它们用于证明，编译器不会
预执行source。后续guard的source fallback是当前normalized source，不是要求
AST与最初parsed程序逐字相同；前一simulation提供原程序关系。每个阶段的
source、guard、candidate和site证据属于其实际输入program，C用户不填callbacks。

完整重放的15/62、31sites只新增fusion5第一段，不能算第二段或全部configuration
覆盖。Tricky2进入producer后缺point space，保持未支持；成本0.978860属于本build
原fusion5短完整调用，不重标此前polynomial测量或宣称稳定加速。参数addresses／
实际观察运输、scalar/rank-one producer及更广source/configuration仍按计划推进。
