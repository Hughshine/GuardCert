# 一个使用者 pass 中的多种 guarded rewrite

2026-10-05。[主契约](guarded-rewrite-contract.md) 将片段选择和候选搜索交给使用者；这个实例是框架的一个使用者，把已有循环／分支规则接到同一个 pass 和完整 C→Asm 端点。

## 混合精确出口与私有出口

[ClightReadonlyRuleEmbedding.v](../prototype/interface/ClightReadonlyRuleEmbedding.v) 提供 `exact_readonly_as_projected`。使用者已有完整原始出口相等的 `readonly_clight_rule` 时，补充源 temps 写界，就能复用带公共观察的宿主。`exact_clight_local_observed` 把精确片段等价提升到任意观察关系的饱和执行；`exact_projected_replacement` 证明生成的 guard／候选／回退语句完全相同。

这项接入没有要求精确规则重新证明私有变量性质，也没有把候选的私有差异扩大到原程序变量。投影宿主仍保护所有原程序 temps、完整内存、trace 和控制 outcome。

`quiet_source_write_bound` 给普通结构化 quiet source 一个保守 temps 写界：允许集合取所有被语句提及的 temps。它是可核对的语法过近似，不是最小写集、liveness 分析或内存足迹证明。已有更精确写界的使用者可直接提交自己的证书。

## 使用者组合规则

[ClightCommonRewriteCompiler.v](../prototype/interface/ClightCommonRewriteCompiler.v) 的选择顺序为：

1. 内存中的循环上界快照；
2. 普通 payload 参数的循环 load 提升；
3. 固定 2×2 交换；
4. 运行时 stride 的二维纯写交换；
5. 固定 stride 的动态矩形 store、读写更新及保留行内依赖的交换；
6. 两个 non-alias 单元的 store 交换；
7. 带延迟读取检查的分支 rewrite。

选择器返回的都是绑定实际源语句的有证书规则。现有精确规则经上述嵌入，共用 projected host；带快照的规则直接使用投影接口。使用者可以改变选择顺序或加入自己的规则，语法遍历与资源选择仍由这个 pass 决定。

每处动态检查在对应片段到达时运行。前一个 rewrite 保留 continuation 所需的公开状态，后一个 rewrite 再用当时的状态建立入口域／前提。一组成功检查不会被当作整个函数的入口事实；候选的私有 temp 可以跨互不重叠的已选片段复用，每处先执行自己的 preload。

`common_progress_supported_sound` 组合原有结构化进展与新的内存循环头进展证书。每个被选择的完整循环仍需受支持的源协议。被选择且可能发散的 `!=` 循环尚未由此接通。

完整端点 `compile_common_rewrites_correct` 是 Csem→Asm backward simulation，经过实际 projected Clight forward simulation。这是一个 pass 内多次真实片段替换的全局证据，和抽象重复 rewrite 的组合定理一起说明使用方式；没有声称完整 Clight 双向行为等价。

## 实际程序中的验收

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-common-native
```

C fixture 在同一个函数中依次执行参数 load 循环、三种动态矩形循环、2×2 模板、条件分支中的两个 store pair、延迟读取分支，以及内存上界循环。参数 snapshot 和上界 snapshot 使用同一新鲜 pool temp，实际出现于两个不同的程序位置。

实际提取和执行通过 576 次调用、2880 行输出。Clight 中分别确认 store、RMW、行内依赖和 2×2 的四处 `j` 外层／`i` 内层候选，两个条件分支均有真正交换后的 store；两次快照确实使用同一个私有 temp。十组原生实例在当前 102 端点审计下重建并全部通过。

程序在后续 store 覆盖之前输出 payload 结果，避免较早循环的错误被覆盖掩盖；输出每一组循环的公开 iterator 出口及全部数组单元。后续两个 store pair 分别将 parameter 写成 0 或 22，随后分支必须使用当前值，检验 guard 的放置。非别名和别名输入同时覆盖普通 payload 与会改变循环次数的 bound。

审计中，组合选择器继承原有真实内存重排的 `Axioms.proof_irr`，按片段加内存基线比较；完整编译端点保持既有 CompCert 编译器基线。这不是删除或隐藏内存记录相等所需的已有假设。

统一 pass 另在 [运行时 stride fixture](clight-runtime-stride-case.md) 上通过 345 次调用／342 行输出，核对九处实际改写及两次 rewrite 之间改变参数的入口状态。这是同一编译端点的第二个程序；上面的混合规则函数本身不包含参数 stride。

这个组合不增加各规则独立的语法／语义覆盖：一般动态数组足迹、内存边界与多维调度的组合，以及参数 stride 的更复杂 body 仍是 [主线验收账本](optimistic-loop-acceptance.md) 中的缺口。没有性能测量。
