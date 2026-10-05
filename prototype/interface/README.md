# 语言无关入口协议原型

当前使用者契约见 [guarded-rewrite-contract.md](../../docs/guarded-rewrite-contract.md)：使用者选择片段、候选及位置，框架插入只读 condition、源回退并证明等价。底层入口协议的设计与分类见 [language-independent-interface.md](../../docs/language-independent-interface.md)。

`GuardInterface.v` 暴露语言、检查、条件变换和上下文四份契约；它证明 guarded refinement、独立的 preservation 及满足宿主插入／目标可安装条件时的程序 refinement。状态、观察、检查的安全性质和关系均由实例解释。检查的存在性不能代替非确定语言的所有路径进展。

`GuardInterfaceExamples.v` 提供不依赖 CompCert 的数学函数语言。检查保留公开输入并覆写私有 scratch；实例覆盖绝对值特化、候选／回退、函数 continuation、任意死候选和 unknown 的否定，还证明源 preservation 不排除新增目标结果。

`GuardedRewrite.v` 提供只读条件、条件性局部等价、基于相同 view／frame 还原的局部提升及程序等价组合。`LocalScheduleEquivalence.v` 复用现有交换链，补足两方向的执行对应。`GuardedRewriteExamples.v` 展示单元分离下的有限循环写入重排和非回绕下的分支删除；各有 frame、条件编码和纯函数 continuation 证明。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-proof
```

这条命令编译十个接口模块及三个既有依赖，并保存源码摘要和 40 个接口闭合端点的检查记录，其中只读 rewrite 扩展占 31 个。模块提供关系式局部还原、多次替换组合、文本求值前提的入口推导及矩形地址／去线性化证书示例。`DeterministicLocalReasoning.v` 允许在显式源完成性与候选确定性下复用单向执行运输，包括对原始结果确定、公共观察不唯一的关系式观察。它不重建现有 CompCert 编译器，也不提供任意语言的现成适配器或一般条件发现。

Clight 模块提供真实片段宿主、写 frame 接口、只在活动路径读取指针的条件、表达式及短路树原子的公式合成、前端空语句规范化及结构化片段确定性证明。`make interface-clight-proof` 审计 53 个端点，它们没有超出既有 Clight 的六项全局假设。`ClightPrivateCandidateExample.v` 证明实际候选可以改变隐藏的临时变量，仍保持边界观察等价，并证明原始结果确实不同。这个文件只证明局部性质；下述投影编译接口另提供新函数 temps 和全局 freshness 的连接。片段宿主使用终止执行的 `exec_stmt`。

`ClightReadonlyCompiler.v` 将用户的选择器、只读证书、局部等价和源入口证明连接到既有进展宿主及完整 Csem→Asm 定理。`ClightPreloadCompiler.v` 给出具体分支实例；`ClightReadonlyMatrix.v` 给出实际 2×2 循环交换实例；`ClightReadonlyRectangle.v` 支持运行时矩形尺寸，`ClightReadonlyLoopUpdates.v` 接入读旧值再写回及保留行内依赖的循环交换；`ClightReadonlyLoopRule.v` 封装规则作者的单向证明到只读编译规则的连接。`ClightRectangleAssumptions.v` 连接范围条件、模型文本位置与机器地址表示。`ClightReadonlyCellSwap.v` 提供两个普通对齐单元的真实 non-alias 检查和写入交换；`ClightCellFrame.v` 实例化字节写界及稳定指针参数。`make interface-compiler-proof` 审计四十三个端点，没有新增公理；实际内存相等复用 CompCert 内存记录的 proof irrelevance。六个原生目标（`interface-native`、`interface-matrix-native`、`interface-rectangle-native`、`interface-cells-native`、`interface-loops-native`、`interface-private-native`）分别构建实际提取编译器并检查 guard 插入及原生执行。原始出口接口要求完整内存／出口 temps 相同；`ClightReadonlyProjectedCompiler.v` 另接入边界观察等价，保护所有原程序 temps、内存和事件，允许已声明且新鲜的候选私有 temp 不同。`ClightPrivateCandidateCompiler.v` 用额外私有赋值检验这个完整程序连接。参数 stride、稳定内存边界、动态循环 alias 及一般 affine 私有迭代器仍待接入。使用方式与证明职责见 [Clight 接入设计](../../docs/clight-guarded-rewrite-design.md)，主线要求见 [验收账本](../../docs/optimistic-loop-acceptance.md)。
