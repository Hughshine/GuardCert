# 语言无关入口协议原型

当前使用者契约见 [guarded-rewrite-contract.md](../../docs/guarded-rewrite-contract.md)：使用者选择片段、候选及位置，框架插入只读 condition、源回退并证明等价。底层入口协议的设计与分类见 [language-independent-interface.md](../../docs/language-independent-interface.md)。

`GuardInterface.v` 暴露语言、检查、条件变换和上下文四份契约；它证明 guarded refinement、独立的 preservation 及满足宿主插入／目标可安装条件时的程序 refinement。状态、观察、检查的安全性质和关系均由实例解释。检查的存在性不能代替非确定语言的所有路径进展。

`GuardInterfaceExamples.v` 提供不依赖 CompCert 的数学函数语言。检查保留公开输入并覆写私有 scratch；实例覆盖绝对值特化、候选／回退、函数 continuation、任意死候选和 unknown 的否定，还证明源 preservation 不排除新增目标结果。

`GuardedRewrite.v` 提供只读条件、条件性局部等价、基于相同 view／frame 还原的局部提升及程序等价组合。`LocalScheduleEquivalence.v` 复用现有交换链，补足两方向的执行对应。`GuardedRewriteExamples.v` 展示单元分离下的有限循环写入重排和非回绕下的分支删除；各有 frame、条件编码和纯函数 continuation 证明。

`ReadonlyConditionComposition.v` 提供带依赖的有限检查阶段：后一个证书的域可包含此前已经建立的性质。语言只实例化常量／顺序检查的实际构造、分派和安全定律；框架证明整体只读、安全、可用及接受的全部性质。`ClightConditionComposition.v` 给出真实决策树代数，内存上界规则已直接消费该设施；见 [接口使用说明](../../docs/condition-stage-interface.md)。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-proof
```

这条命令编译十一个接口模块及三个既有依赖，并保存源码摘要和 43 个接口闭合端点的检查记录，其中只读 rewrite 扩展占 34 个。模块提供关系式局部还原、多次替换组合、文本求值前提的入口推导及矩形地址／去线性化证书示例。`DeterministicLocalReasoning.v` 允许在显式源完成性与候选确定性下复用单向执行运输，包括对原始结果确定、公共观察不唯一的关系式观察。它不重建现有 CompCert 编译器，也不提供任意语言的现成适配器或一般条件发现。

Clight 模块提供真实片段宿主、写 frame 接口、只在活动路径读取指针的条件、表达式及短路树原子的公式合成、前端空语句规范化及结构化片段确定性证明。`make interface-clight-proof` 审计 57 个端点，它们没有超出既有 Clight 的六项全局假设。`ClightPrivateCandidateExample.v` 证明实际候选可以改变隐藏的临时变量，仍保持边界观察等价，并证明原始结果确实不同。这个文件只证明局部性质；下述投影编译接口另提供新函数 temps 和全局 freshness 的连接。片段宿主使用终止执行的 `exec_stmt`。

`ClightReadonlyCompiler.v` 将用户的选择器、只读证书、局部等价和源入口证明连接到既有进展宿主及完整 Csem→Asm 定理。`ClightPreloadCompiler.v` 给出具体分支实例；`ClightReadonlyMatrix.v` 给出实际 2×2 循环交换实例；`ClightReadonlyRectangle.v` 支持运行时矩形尺寸，`ClightReadonlyLoopUpdates.v` 接入读旧值再写回及保留行内依赖的循环交换；`ClightReadonlyLoopRule.v` 封装规则作者的单向证明到只读编译规则的连接。`ClightRectangleAssumptions.v` 连接范围条件、模型文本位置与机器地址表示。`ClightReadonlyCellSwap.v` 提供两个普通对齐单元的真实 non-alias 检查和写入交换；`ClightCellFrame.v` 实例化字节写界及稳定指针参数。`make interface-compiler-proof` 审计一百九十九个端点，没有新增公理；实际内存相等复用 CompCert 内存记录的 proof irrelevance。十五个原生目标（`interface-native`、`interface-matrix-native`、`interface-rectangle-native`、`interface-cells-native`、`interface-loops-native`、`interface-private-native`、`interface-stable-load-native`、`interface-loaded-bound-native`、`interface-common-native`、`interface-runtime-stride-native`、`interface-indexed-load-native`、`interface-indexed-bound-native`、`interface-equality-native`、`interface-equality-head-native`、`interface-loaded-matrix-native`）分别构建实际提取编译器并检查 guard 插入及原生执行。原始出口接口要求完整内存／出口 temps 相同；`ClightReadonlyProjectedCompiler.v` 另接入边界观察等价，保护所有原程序 temps、内存和事件，允许已声明且新鲜的候选私有 temp 不同。`ClightPrivateCandidateCompiler.v` 用额外私有赋值检验这个完整程序连接。`ClightStableLoadCompiler.v` 另将普通参数 load 提升到候选私有 temp，消费活动路径、单元 non-alias、前缀不变性和实际循环局部化证明。727 次 C 调用通过，详见 [稳定 load 使用者案例](../../docs/clight-stable-load-case.md)。`ClightLoadedBoundCompiler.v` 将实际内存上界接到同一完整定理；514 次 C 调用通过，源进展独立于上界稳定，普通 load 可进入 tree-valued 条件合成。详见 [内存上界使用者证明](../../docs/clight-loaded-bound-case.md)。`ClightReadonlyRuleEmbedding.v` 保持精确规则生成的代码相同地提升到公共观察，`ClightCommonRewriteCompiler.v` 在同一函数中组合这些规则：576 次调用／2880 行输出、十四组原生回归通过，见 [组合使用者 pass](../../docs/clight-common-user-pass.md)。`ClightRuntimeStrideCompiler.v` 已接入真实参数 stride 的二维纯写循环交换，345 次调用／342 行输出和九处实际 guard 通过，统一 pass 也运行同一程序；详见 [使用者证明](../../docs/clight-runtime-stride-case.md)。`ClightIndexedLoadCompiler.v` 又将有界动态 indexed 写足迹接到只读 alias 检查和 load 提升，独立入口与统一 pass 均通过 1095 次调用／2188 行输出；见 [案例](../../docs/clight-indexed-load-case.md)。`ClightIndexedBoundCompiler.v` 进一步将 indexed 写足迹与内存上界组合：检查安全沿实际源前缀建立，不能预设完整入口 footprint；独立入口／统一 pass 均通过 1079 次调用／2154 行输出。三元素数组中入口上界 8、第三次写入使其变为 3 的合法源用例通过；见 [案例](../../docs/clight-indexed-bound-case.md)。内存上界与 2×2 调度已由后述模板组合；一般动态尺寸／stride 的组合、无界／仿射足迹、参数 stride 的复杂 body 及一般 affine 私有迭代器仍待接入。使用方式与证明职责见 [Clight 接入设计](../../docs/clight-guarded-rewrite-design.md)，主线要求见 [验收账本](../../docs/optimistic-loop-acceptance.md)。


`ClightCounterProgress.v` 将计数器的 active／remaining／next 及正性、递减和实际自增求值交给语言实例。`ClightCircularCounter.v` 用 unsigned 模距离证明固定上界、单位步长源 `!=` 循环进展，包含 unsigned 回绕 fallback。`ClightCounterCondition.v` 提供任意自增表达式下的活动头部运输，`ClightEqualityLoop.v` 在只读 `i==0 && 0<(int)n` 下证明实际 `!=→<`，`ClightEqualityCompiler.v` 接入完整 Csem→Asm。独立入口和统一 pass 各通过 703 次调用／703 行输出，六个函数中有七处真实 guarded rewrite；十三种提取配置重建回归通过，15 份既有源码／Clight 摘要保持相同。详见 [等式退出使用者证明](../../docs/clight-equality-loop-case.md)。选中片段本身可能发散的步长 2／变化目标循环仍不由当前宏片段宿主支持。


`ClightReadonlyExpression.v` 将实际值表达式／有限 dispatch 实例化到相同只读核。`readonly_expression_rule` 提供完整 `val` 的局部等价、类型和每次源求值的域；`ClightReadonlyTestSyntax.v`／`ClightReadonlyTestProof.v` 在具体 skip/break 头部及 assignment／return 位置做真实小步模拟，无需外围循环 rank。`ClightEqualityHead.v` 在当前 `i≤n` 下证明 `!=→<`，`ClightReadonlyTestCompiler.v` 接到完整 Csem→Asm，并允许先行 pass 的实际 forward simulation 组合。统一入口已串接 projected region pass 和这个逐步 pass；独立／统一入口各通过 333 次调用／284 行输出和十处实际改写，两个明确无限的源仅编译和检查。十四种配置回归通过，前阶段 17 份报告中仅统一等式退出程序增加预期头部检查，其余 16 份源码／Clight 摘要相同。现有 STEPWISE 八项与 COMPILER 35 项基线外没有新公理。详见 [逐步实例](../../docs/clight-stepwise-head-case.md) 和 [宿主能力分类](../../docs/host-capabilities.md)。

`ClightOrderedInequality.v` 暴露 `ordered_inequality_rule left right LEFT RIGHT`：实际 signed32 表达式的 `left!=right` 在当次 `left≤right` 下改成 `<`。普通 load／bitwise 计算／常量均可作为操作数；源实际求值提供域，检查不假定跨迭代稳定。选择器核对完整表达式和类型，独立／统一入口各通过新 fixture 的 737 次调用和八种实际 contexts。源 volatile load 先产生一次事件，后续 guard 只读其 temp；signed 控制溢出未执行。当前完整审计 184 端点、十四种提取配置回归通过；旧 19 份报告中仅两份头部程序因新增常量比较改变 Clight，其他 17 份源码／Clight 摘要相同。见 [普通表达式比较实例](../../docs/clight-loaded-comparison-case.md)。

`ClightNestedStrictProgress.v` 将既有 body 的 `framed_progress` 接到外层 memory-bound 源的独立最大值 rank，仅保护 outer iterator，不预设 bound 稳定。`ClightLoadedMatrixSyntax`／`Guard`／`Loop`／`Compiler` 在实际 2×2 模板中消费它：四 word alias 检查沿实际源行前缀建立安全，全部通过后才快照 bound 并真正交换两层循环。独立／统一入口各通过 668 次调用／673 行输出和七处真实 guard；199 端点审计没有新增公理，十五种提取配置回归通过，21 份既有源码／Clight 摘要相同。源 alias 使第一行后提前退出或增大 bound 的合法输入得到保持；一般动态尺寸／stride 及旧 affine 迁移仍待完成。见 [二维内存上界案例](../../docs/clight-loaded-matrix-case.md)。
