# 新增先例：CompCert-loop 的结构变换接入

2026-10-02 核对 Knothe、Bringmann 的 2026 年预印本 [Combining Small-Step and Big-Step Semantics to Verify Loop Optimizations](https://arxiv.org/html/2602.19868v1) 及作者的 [CompCert-loop 源码仓库](https://github.com/knothed/CompCert-loop)。本次阅读论文方法、变换章节与仓库说明，未移植或运行其 artifact。

论文通过抽象行为语义连接大步与小步流水线，补充有限／无限 trace 的发散建模，并在 Cminor 实现循环变换。因此“局部结构变换能进入 CompCert 完整程序定理”和“框架仅消费抽象语义性质”已有很直接的先例。不能把这两点单独作为 GuardCert 的新颖性依据。论文第 5 节的大步阶段不支持 goto；仓库还披露了 loop unswitching 未匹配真实前端形状的限制。

GuardCert 的当前路径不同：语言提供静默片段的下降度量与完成重建，保留原 Clight 小步外围，包括 goto；但片段范围更窄，不允许无限内部执行。条件性质、检查自身的定义性和程序回退另有接口。该论文展示的变换没有提供本项目正在研究的通用 presumption 编码与可执行条件合成器；论文里的 coinductive `guard` 是保证 trace 生产的证明条件，不能等同于运行时的优化检查。

这一比较支持继续把研究问题放在“给定候选，怎样生成可安全执行的成立条件，并将其证书接入真实机器程序”上。当前循环宿主和嵌套进展证明是基础设施。更有辨识度的实例仍需真实循环重排、overflow／footprint 条件、出口修复和实际候选收益。
