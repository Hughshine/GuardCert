# Loaded nested source 的进展、程序安装与固定 profile compiler

这是 [loaded pointer 局部规则](research-checkpoint-2026-10-06-affine-loaded-pointer.md) 的后继阶段。已证明的缓存运输与候选规则现在接到完整 Clight 程序，并给出 `compile_affine_loaded_pointer_correct` 的 Csem→Asm backward simulation。安装 profile 仍使用原 normalized fixture 的固定标识符；本阶段没有真实 C frontend 的非空接受、提取或新原生执行证据，完整目标继续 active。

## 关闭的困难义务

优化接受需要证明：body 的全部实际 stores 不改变观察到的 bound 单元，因而可以缓存并重排。回退原循环的程序安装却不能先假设这项稳定性。否则 guard 拒绝时，局部 contract 仍无法用于完整程序证明。

[ClightStrictNestedProgress](../prototype/interface/ClightStrictNestedProgress.v) 给 strict signed loop 建立独立的 framed 小步协议。它只要求每次成功的 true test 蕴含 iterator 是小于 `Int.max_signed` 的 signed word，以及 body 的嵌套协议逐步保护该 iterator。循环距离取机器最大值与当前 iterator 的差；它不取当前 memory bound。每次 increment 严格降低距离，body 的协议 rank 处理内部执行。因此，body 可以改变 bound 的内容，甚至改变下次测试是否有定义；协议不承诺无定义源的行为。

[ClightLoadedSequenceProgress](../prototype/interface/ClightLoadedSequenceProgress.v) 对真实 AST 核对 signed load/test/increment，递归组合 finite statements、sequences、cached loops 和 loaded loops。fuel 是源 AST 大小，只限制证书构造。cached loops 沿用旧 protected-bound 协议；loaded loops 不要求保护 memory bound，也不要求绑定其 pointer 为 stable temporary。选择器保守拒绝 body 改写外层 iterator。

六个 compiled fixtures 核对 loaded triangle、保留 prefix、body 写 `p[0]=0` 均通过进展检查，以及 body 改写外层 iterator 被拒绝；另外核对不同 sequence association 与实际写内存的 quiet suffix 同时通过 source profile 和 progress。改变 bound 的 fixture 只说明语言进展能力；优化 matcher 不会因此接受这个改变后的 body。这些都是 normalized Clight fixture，没有改称真实 frontend 输出。

## 验证责任

| 层 | 本阶段新增／消费 | 未因此完成的责任 |
| --- | --- | --- |
| 语言无关框架 | 原条件顺序组合、readonly 证书和局部保持服务继续被原 loaded rule 消费；kernel 未修改 | 核不判断 loaded header 的机器性质，不证明某次缓存或调度合法 |
| Clight 语言实例 | strict nested progress、真实语法核对、sequence placement、private-pool/scope 检查；[table host](../prototype/interface/ClightLoadedRegionHost.v) 复用原程序安装定理 | 源片段必须通过支持域；一般非单调或任意无限源没有由此获得协议 |
| optimizer/domain | [candidate factory](../prototype/interface/ClightAffineLoadedPointerCandidates.v) 复用原 mapped、tiling 和 schedule generation 后重新核对；接受 code、restore、条件和原 loaded fallback 绑定同一证书 | 固定 profile 到真实 frontend names 的适配尚缺；候选正确性和全部写入排除 bound 的证明仍由 domain 提供 |
| CompCert 后端连接 | [compiler](../prototype/interface/ClightAffineLoadedPointerCompiler.v) 保留真实 SimplExpr/SimplLocals、checked table、安装和后端，组合到 Csem→Asm | endpoint 的量化正确性不证明 matcher 在真实 C 上非空接受 |

`alp_installed_program_correct` 消费单个已认证候选的 retained-prefix contract，给完整 Clight 程序的 forward simulation；`apply_loaded_region_table_correct` 可以消费任意 optimizer 提供的已证 table。二者保护原程序所有临时变量和完整 memory，复用旧 private pool 与 scope 服务。

新的候选工厂先核对真实 source 的 flattening、preload prefix、loop 与 quiet suffix，再以 statement equality 将其 canonical prefix/loop 绑定 `alp_observed_source`，保留 suffix 的实际执行效果。它没有给任意 C 程序套一个理想化源模型。Mapped／tiling 各自调用独立 checker；schedule producer 和 candidate normalization 的结果仍经 mapped checker。宽度、alias 编码和实际 Clight lowering 失败，以及 candidate checker 拒绝，均不给 table 增加 rewrite。程序安装另外核对 source progress 和 private pool。

这是一项临时、可审核的固定 profile。它展示实际 certificate→table→host→backend 的连接，但不是新的通用 loaded optimizer，也不构成真实 C 上的功能验收。不以 endpoint 数量主张作者证明负担或 novelty 收益。

## 验证与后续验收

运行 `opam exec --root=/tmp/guard-opam --switch=guard -- make affine-loaded-placement-proof`。独立报告位于 `build/affine-loaded-placement/proof/report.json`；原局部证明报告与原 affine-inner compiler 的提取／native 报告保留为不同阶段。该审计编译新增模块、核对所选依赖闭包的时效和源码／object 摘要，并检查语言端点不超过原 CompCert 假设、domain/compiler 端点不超过原 CompCert＋mapped＋tiling baseline。此处不是 clean 重编译整个闭包。

审计通过 55 个端点，其中 11 个语言服务端点；所选闭包 546 项依赖，共绑定 890 份源码摘要。新 `compile_affine_loaded_pointer_correct` 与独立旧 compiler regression 均继承 42 项 baseline 假设，没有额外全局公理。所有报告中源码、compiled object 和 audit script 摘要均再次逐项核对。报告 SHA-256：

```text
1cc92928fa804fe89f6fa9f65432c84acab6c05856bd1efb0c9361c4b08ba764
```

编译记录保留了新增 fixture 修改后触发的依赖时效拒绝；完成修改后重新运行审计，当前报告通过，不以较早 object 作为成功结果。原 891 调用矩阵没有重跑，不能作为新 loaded compiler 的运行证据。

下一项必须推广实际源 adapter：让 cache/iterator/pointer 和 retained source receipt 来自真实 frontend AST，不依赖 fixture 标识符；同一动态条件和实际 checker 在完整 C 程序上选中真实候选，并核对接受、回退、alias 发散、公开出口与外围上下文。随后继续任意 bound pointer、多个依赖 preload 的安全读序与 original-entry 事实、private snapshot，以及一般深层 affine 域。当前 guard 域仍使用有限正常源完成，不能描述成任意无限源的有限前缀证明。

本阶段重新 fetch 后，评审分支仍为 `f793629`、`9673381`、`3e9f008`，没有新增意见。`docs/topdown/paper-narrative.md` 与 fetched `topdown/research-positioning` 正文字节一致；按 narrative 将稳定性、source progress、候选证书和完整程序安装分别验收。
