# VLIM 与当前研究定位

2026-10-02。新发现的近邻工作是 Turner 与 Chakraborty 的 [VLIM: Verified Loop Interchange for Optimised Matrix Multiplication，DATE 2026](https://durham-repository.worktribe.com/output/4819889/vlim-verified-loop-interchange-for-optimised-matrix-multiplication)，DOI `10.23919/DATE69613.2026.11539281`。

目前证据来自作者大学仓储元数据及[会议论文的搜索索引文本](https://past.date-conference.com/proceedings-archive/2026/DATA/116.pdf)。直接获取分别返回 403、404；尚未取得可完整阅读的 PDF，也未构建代码。下列比较必须保留这一限制。

已核对的内容：VLIM 在 Capla/CompCert 路径上提供带证明的 rewrite algebra；包括 statement 到 function 的提升、组合与递归查找。索引中的 function 正确性从源执行得到候选执行，保留输出和可变参数结果。其实例是 loop interchange。论文使用了 rewrite guard 一词，但当前片段尚不足以判定它是否代表实际运行时检查与回退。[作者仓储](https://durham-repository.worktribe.com/output/4819889/vlim-verified-loop-interchange-for-optimised-matrix-multiplication)、[会议论文索引](https://past.date-conference.com/proceedings-archive/2026/DATA/116.pdf)。

据此，我对当前研究方向作以下判断，而非对 VLIM 未读部分作否定结论：

- “局部 rewrite 证明可组合、可提升”已经有很接近的机械化先例，不能单独作为 GuardCert 的新颖性主张。
- 应逐例比较前提从哪里来、如何得到机器可执行的检查、无法检查如何回退、检查是否保持入口状态，以及完整程序定理覆盖哪些行为。
- 需要一个异质实例检验复用。表达式恒等式和真正的内存／循环区域应共享条件编译与宿主连接，而非仅共享几份 record 的名字。
- PolCert 的 abstract instruction 交换性质可以作为语言提供的能力；框架负责条件组合、检查与宿主接入。自动合成仍须受可观察信息、检查安全和证明可核对性的约束。

后续对照的具体问题：VLIM 的 guard 是静态适用性检查、逻辑前提还是注入的运行时代码？条件性 rewrite 是否生成原代码回退？其 statement lifting 对一般控制流、发散和状态关系有哪些要求？这些问题在取得全文和 artifact 前保持未决。

2026-10-04 重新尝试公开全文链接：会议 PDF 仍为 HTTP 404，大学仓储页面直接访问仍为 HTTP 403；搜索索引可读。索引中的图 8 具体给出函数 rewrite 的顺序组合和自动推导正确性，图 9 给出首次成功的 AST 遍历；交换条件还讨论可交换的共享写入。`rewrite guard` 的描述包含归纳证明，但这仍不足以确认它是否产生实际检查与回退代码。当前新增的逐段候选证书是功能实现，不能以“组合本身”区别于这一先例。[会议论文索引](https://past.date-conference.com/proceedings-archive/2026/DATA/116.pdf)。

2026-10-04 另核对了 [FRESCO 团队的公开项目页](https://fresco.gitlabpages.inria.fr/)与 [Capla 官方语言文档](https://fresco.gitlabpages.inria.fr/capla/language/index.html)。文档说明已验证的 Capla→CompCert 后端、未经验证的 C 输出以及 64 位目标限制。只读检出公开 Capla language 的 master `b7fa07585c36651b58d52c05fe6df1541a0089eb`，针对循环交换与 rewrite algebra 的源码定位尚未找到对应实现；没有构建该代码，也没有据此推断 VLIM artifact 或 runtime guard 的能力。这一检查只补充公开项目的定位，论文的上述问题仍未决。
