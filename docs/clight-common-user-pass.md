# 一个使用者 pass 中的多种 guarded rewrite

2026-10-05。[主契约](guarded-rewrite-contract.md) 将片段选择和候选搜索交给使用者；这个实例是框架的一个使用者，把已有循环／分支规则接到同一个 pass 和完整 C→Asm 端点。

## 混合精确出口与私有出口

[ClightReadonlyRuleEmbedding.v](../prototype/interface/ClightReadonlyRuleEmbedding.v) 提供 `exact_readonly_as_projected`。使用者已有完整原始出口相等的 `readonly_clight_rule` 时，补充源 temps 写界，就能复用带公共观察的宿主。`exact_clight_local_observed` 把精确片段等价提升到任意观察关系的饱和执行；`exact_projected_replacement` 证明生成的 guard／候选／回退语句完全相同。

这项接入没有要求精确规则重新证明私有变量性质，也没有把候选的私有差异扩大到原程序变量。投影宿主仍保护所有原程序 temps、完整内存、trace 和控制 outcome。

`quiet_source_write_bound` 给普通结构化 quiet source 一个保守 temps 写界：允许集合取所有被语句提及的 temps。它是可核对的语法过近似，不是最小写集、liveness 分析或内存足迹证明。已有更精确写界的使用者可直接提交自己的证书。

## 使用者组合规则

[ClightCommonRewriteCompiler.v](../prototype/interface/ClightCommonRewriteCompiler.v) 的选择顺序为：

1. 双 memory-bound、逐点两层前缀安全的 2×2 数组交换；
2. 带源行前缀安全的 memory-bound 2×2 交换；
3. memory-bound 动态矩形交换；
4. memory-bound 行数与参数 stride 的有界布局交换；
5. 带源前缀安全 indexed 检查的内存上界快照；
6. 固定单元写入下的内存循环上界快照；
7. 带有界动态 indexed 写足迹的 payload 参数 load 提升；
8. 固定单元 payload 参数的循环 load 提升；
9. 任意正双 memory-bound 尺寸的幂等零写入化简；
10. 两个变化内存上界的单次迭代消除；
11. 固定寄存器上界、单位 unsigned 自增的等式退出规范化；
12. 固定 2×2 交换；
13. 运行时 stride 的二维纯写交换；
14. 固定 stride 的动态矩形 store、读写更新及保留行内依赖的交换；
15. 两个 non-alias 单元的 store 交换；
16. 带延迟读取检查的分支 rewrite。

选择器返回的都是绑定实际源语句的有证书规则。现有精确规则经上述嵌入，共用 projected host；带快照的规则直接使用投影接口。使用者可以改变选择顺序或加入自己的规则，语法遍历与资源选择仍由这个 pass 决定。

每处动态检查在对应片段到达时运行。前一个 rewrite 保留 continuation 所需的公开状态，后一个 rewrite 再用当时的状态建立入口域／前提。一组成功检查不会被当作整个函数的入口事实；候选的私有 temp 可以跨互不重叠的已选片段复用，每处先执行自己的 preload。

`common_progress_supported_sound` 组合结构化进展、嵌套变化内存上界和单位 unsigned 自增的模距离证书。内存上界的嵌套协议只保护计数器，允许回退时两项 bound 都改变。每个被选择的完整循环仍需受支持的源协议。被选择且可能发散的完整 `!=` 循环尚不能用这个宏片段协议替换；后续逐步 pass 另处理其有限头部。

完整端点 `compile_common_rewrites_correct` 是 Csem→Asm backward simulation，经过实际 projected Clight forward simulation。这是一个 pass 内多次真实片段替换的全局证据，和抽象重复 rewrite 的组合定理一起说明使用方式；没有声称完整 Clight 双向行为等价。

## 实际程序中的验收

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-common-native
```

C fixture 在同一个函数中依次执行参数 load 循环、三种动态矩形循环、2×2 模板、条件分支中的两个 store pair、延迟读取分支，以及内存上界循环。参数 snapshot 和上界 snapshot 使用同一新鲜 pool temp，实际出现于两个不同的程序位置。

实际提取和执行通过 576 次调用、2880 行输出。Clight 中分别确认 store、RMW、行内依赖和 2×2 的四处 `j` 外层／`i` 内层候选，两个条件分支均有真正交换后的 store；两次快照确实使用同一个私有 temp。十五种提取编译器配置在当前 199 端点审计下重建并全部通过。

程序在后续 store 覆盖之前输出 payload 结果，避免较早循环的错误被覆盖掩盖；输出每一组循环的公开 iterator 出口及全部数组单元。后续两个 store pair 分别将 parameter 写成 0 或 22，随后分支必须使用当前值，检验 guard 的放置。非别名和别名输入同时覆盖普通 payload 与会改变循环次数的 bound。

审计中，组合选择器继承原有真实内存重排的 `Axioms.proof_irr`，按片段加内存基线比较；完整编译端点保持既有 CompCert 编译器基线。这不是删除或隐藏内存记录相等所需的已有假设。

统一 pass 另在 [运行时 stride fixture](clight-runtime-stride-case.md) 上通过 345 次调用／342 行输出，核对九处实际改写及两次 rewrite 之间改变参数的入口状态。这是同一编译端点的第二个程序；上面的混合规则函数本身不包含参数 stride。

它又在 [动态 indexed footprint fixture](clight-indexed-load-case.md) 上通过 1095 次调用／2188 行输出：同一对象的非活动参数单元、不同对象和 const 参数均可进入有界扫描候选，部分重叠及超 cap 输入回退。这是该完整端点的第三个程序；上面的混合规则函数没有 indexed 写足迹。当前 cap=16，生成树有 17 个候选出口，检查成本和代码大小分别记录。

这个组合不增加各规则独立的语法／语义覆盖：一般动态数组足迹、一般动态 memory-bound 尺寸与多维调度的组合，以及参数 stride 的更复杂 body 仍是 [主线验收账本](optimistic-loop-acceptance.md) 中的缺口。没有性能测量。

第四个程序是 [源前缀安全的 indexed 内存上界](clight-indexed-bound-case.md)：1079 次调用／2154 行输出通过。它在 alias 写入可能提前结束源循环时，沿已通过的检查前缀证明下一次比较安全；不会假定完整入口上界对应的 footprint 有效。三元素数组中入口上界 8 和 INT_MAX 均合法回退并保留三次源迭代。上面的混合规则函数仍没有这个模板；统一 pass 的覆盖由四个实际程序共同记录。


第五个程序是 [固定上界的等式退出](clight-equality-loop-case.md)。统一选择器已接入完整 AST 核对、两项只读 guard、实际 `<` 候选与源 `!=` fallback，源进展的模距离不依赖接受条件。完整编译接口现审计 164 个端点；独立入口和统一入口各通过 703 次调用／703 行输出、七处实际 guard。上面的混合规则函数不包含这个模板。


## 与逐步求值 pass 的组合

当前 `compile_common_rewrites` 先用 `transform_projected_readonly` 运行上述宏片段选择器，再由 `compile_readonly_tests_after` 做 [逐步头部／值表达式 rewrite](clight-stepwise-head-case.md)。前一个 pass 提供实际 Clight forward simulation，后一项全局定理组合两者并连接 CompCert backend。共用完整 Csem→Asm 端点，不把两项前提提前固定在函数入口。

每次头部检查当前 `(int)i≤(int)n` 后，将 `!=` 改成 `<`；允许改变 bound、步长 2 及 volatile body，因为此 pass 不选择整段循环、不要求其 rank。赋值 RHS、return 和具体 skip/break 头部可改写，任意带 label 分支保持结构。先行宏片段的 `!=` fallback 也可能被后来的头部 pass 再次改写：保持源行为，但实际 AST 会增加每次头部检查。旧的等式退出 fixture 脚本分别核对这两个层次。

新头部 fixture 的独立入口和统一入口各通过 333 次调用／284 行输出、十处实际改写；十四种提取配置回归通过。两个明确无限的源函数也编译并确认头部被改写、原步长／bound 更新仍在；未运行它们，保证来自实际小步模拟。完整编译接口现审计 184 个端点，STEPWISE 基线为现有八项，没有新全局公理。它不由此提供无限整段调度或 memory-bound 二维交换。

第七个实际程序是 [普通 load／计算表达式的比较](clight-loaded-comparison-case.md)：统一入口通过 737 次调用，核对每次头部重新读取当前 bound，并包含一次源 volatile load 后的只读快照比较。该模板从实际源比较求值建立域，在当次 `left≤right` 下证明两个 signed32 完整比较值相同；没有将 body 改变的 bound 缓存为入口参数。原头部程序新增常量检查，其余 17 份既有源码／Clight 摘要相同；十四种配置在 184 端点审计下回归通过。

第八个实际程序是 [内存上界与二维 2×2 调度](clight-loaded-matrix-case.md)：统一入口在同一次宏片段替换中消费源行前缀的四 word 检查、实际 load 稳定性、私有 snapshot 和列优先调度。668 次调用／673 行输出、七处实际 guard 通过；独立入口运行同一程序也通过。当时的宏选择器先尝试这个模板，新的 body frame／strict rank 协议提供独立源进展；其余规则的前提和覆盖保持各自声明。199 端点审计无新增公理，十五种配置回归通过，21 份既有源码／Clight 摘要相同。一般动态 memory-bound 尺寸／stride 仍是缺口。

[通用只读前缀扫描](readonly-prefix-scan-interface.md)阶段将当前完整编译审计扩展到 209 端点，纯接口 49 个闭合端点、Clight 59 个端点没有新增公理；十五种配置全部重建回归通过，23 份既有源码／Clight 摘要相同。统一入口的 indexed memory-bound 规则实际调用新生成器，其他规则的局部与全局契约保持相同。

当前综合入口也消费动态 memory-bound 矩形、参数 stride 布局和 [双内存上界的单次迭代消除](clight-dual-loaded-unit-case.md)。后者通过 3,035 次调用和七处实际 region，包含共享只读 bound、两个 counter 的出口、连续替换以及 alias 改变内层／外层上界。精确规则经现有嵌入进入 projected host，源进展不借用稳定性前提。该阶段完整审计为 297 端点、二十种配置全部回归通过，31 份原生报告；相对 `2485d94` 的 29 份已有 source／Clight 摘要相同。单次迭代模板本身不提供一般两维数组调度。

综合入口现在首先选择 [双 loaded 的固定 2×2 数组交换](clight-dual-loaded-matrix-case.md)。它复用一槽候选 cache 和现有宏宿主，每点两项分离全部通过后才建立后续真实执行；七处实际 region、22,303 次调用／行输出通过。独立入口另使用共享出口，综合入口仍生成十一份原循环回退；一槽 pool 使 31 份已有程序的 source／Clight 摘要相对 `2181c5f` 保持相同。该阶段完整审计 317 端点、21 种配置全部回归通过，33 份原生报告。一般双动态尺寸继续推进，没有性能结果。

综合精确规则现在还选择 [双动态上界的幂等写入化简](clight-dual-repeated-store-case.md)：任意正 signed32 rows／columns 且写址分离时，只写零一次并恢复两个真实 counter 出口。规则没有私有 cache，继续经精确规则嵌入复用 projected host；综合入口通过 3,035 次调用和七处实际 region。当前完整审计 333 端点、22 种配置回归通过，35 份原生报告绑定当前产物；相对 `c711ed9` 的 33 份已有 source／Clight 摘要保持相同。一般双动态尺寸的数组调度仍继续推进。
