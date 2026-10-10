# 两条实际 Clight 路线的组合与完整语料边界

这个 checkpoint 将 source-tree residual 路线与已有 typed-double 路线组合。
目的在于保留两条路线的功能，并让每一步对实际中间程序的证明连接到同一个
CompCert backend。它落实 [narrative](topdown/paper-narrative.md) 的责任边界，
没有增加 kernel 或语言 host 的语义法则。

## 使用方式与证明交接

C 使用者提交 `#pragma scop` 标注的原程序、phase 选项及 untrusted profile／策略
数据。标注只选择尝试优化的位置。使用者不提供 source/model、guard 或 context
的语义 callbacks；已实现的 factory 和 site checker 必须 discharge 这些义务。

[CombinedDoubleTreeResidualCompiler.v](../prototype/interface/CombinedDoubleTreeResidualCompiler.v)
的 `checked_selected_combined_residual_double_program` 实际执行：

```text
normalized Clight P0
  -> checked source-tree pass
actual intermediate Clight P1
  -> checked typed-double passes
actual intermediate Clight P2
  -> CompCert backend
Asm
```

第二步以 `P1` 为输入；其适用性、private resources 和安装证据针对这个实际程序
取得。证明先组合 `P0 -> P1` 和 `P1 -> P2` 的 Clight forward simulations，再连接
前端 normalization 和 backend，得到成功编译时原 `Csem` 到目标 `Asm` 的
backward simulation：`compile_selected_combined_residual_double_program_correct`。

这展示有限顺序组合的具体使用方式。它不表示可在原 `P0` 上寻找全部 sites，
再把旧证据直接用于已改变的 `P1`，也不是任意上下文自动闭包定理。
源执行是证明的语义起点，运行时不会先执行 source 来决定候选是否合法。

| 责任方 | 这个组合中的交付 |
| --- | --- |
| Framework kernel／条件库 | 复用局部 guard 证书组合和 generic formula residualization |
| 语言／IR host | 安全 capture、private/public frame、机器 lowering、公开出口、合法 site 与 progress、CompCert 衔接 |
| Domain／优化实现者 | 实际 source/model 对应、候选检查、binder／branch facts 和 postpass 执行保持 |
| Native proposer | 调用 Pluto、构造模型与候选提案；其提案仍由已验证的检查裁决 |

模型前提到入口条件的推导属于 domain 服务；机器执行和 entry/refusal transport
属于具体语言实例。候选体的 residualization 已有证明，OLO 的紧凑入口条件构造
仍有独立的交付义务。Context clauses 仍按实际 host 需求检验。

[组合证明审计](double-tree-combined-residual.json)覆盖新增 81 行和两个端点，
沿用前序全局假设，无新增 globals；端点最多依赖 42 个原 globals。没有改动
成功的前序证明源和 objects。

## 完整输入对照

[完整摘要](double-tree-combined-residual-corpus.json)固定 62 个原例及两个公开说明的
initializer adaptations，每个运行 unmarked、untiled、requested tiled，共 192 项。
两个 adaptations 是不同源码，单独计数。

| 配置 | 完整输出匹配，含 adaptations | 原例中观察到 tree 安装 | 原例中观察到 typed 安装 | 原例安装形状的并集 |
| --- | ---: | ---: | ---: | ---: |
| Unmarked | 62/64 | 0 | 0 | 0 |
| Untiled | 62/64 | 7 | 15 | 22 |
| Requested tiled | 61/64 | 3 | 22 | 25 |

合计 185 项输出匹配，其中原例 179/186，adaptations 6/6。原 corcol3／pca 的
六配置由 CompCert frontend 拒绝非 constant initializer；jacobi-1d-imper 的
requested tiled 编译在 180 秒超时。没有 native mismatch 或 link failure。

Tree 和 typed 的计数来自不同的最终 Clight 诊断，按 case 取并集，不直接相加。
前序 standalone residual 的 untiled 安装为八个原例；组合路线观察到 22 个。
这些是安装形状的证据。仍须逐项核对 scheduled model、最终 candidate、实际
guard 接受路径和保留的变换，才可报告 requested transformation 支持。

首次组合运行没有 typed counter：184 项匹配，另有 tce requested-tiled 超时。
第二次加入 typed counter 后 tce 完成；两个运行及其超时均保留。它们没有统一
的编译负载控制，不能以差异推出某项诊断或变换的精确成本。
Standalone residual 的满域 paired ratio 0.754 不移用于组合 compiler。

## 编译诊断成本的后继

前序 jacobi 的 15 秒 GDB 采样停在 VPL 的约束 pretty-printing／GC。
`Vpl.Debugging.trace` 的 Rocq 定义直接返回 value，但已有 OCaml hook 会先求值
message。后继 builder 使用 `Extraction Inline Debugging.trace`，由标准提取展开
原定义，消去诊断 message 的构造。候选检查、依赖检查及实际 compiler 定义保持。

独立的小提取实验证明 trace probe 等于其输入，`Print Assumptions` 为 closed；
生成 OCaml 为 `let trace_probe n = n`。后继提取产物也未保留 VPL trace 调用。
Native SCoP、scheduler 和最终 tree／typed 诊断仍可记录；VPL 细粒度 phase trace
不再可用。这是编译器日志成本的改动，不是 runtime guard 简化。

[固定后继摘要](double-tree-combined-residual-quiet.json)绑定 444 个提取及 native
modules、相同的 Rocq 语义／证明输入、identity probe 和旧采样。原 jacobi 与 tce
requested-tiled 输入均完成并匹配完整输出，编译分别约 86.6 和 117.5 秒。
Jacobi 诊断为 tree 安装两个 region、typed 零安装。相同请求是否保留分块形状
仍需核对实际候选，不能由编译完成推断。

[完整后继对照](double-tree-combined-residual-quiet-corpus.json)已完成相同的 192 项，
186 项完整输出匹配：原例 180/186、两个 adaptations 6/6。只剩原 corcol3／pca
的六项 frontend 拒绝；没有 compiler timeout、native mismatch 或 link failure。
逐项核对输入 hashes，源码、数值类型与计算保持。相对前序有且只有 jacobi tiled
的状态由 timeout 变为 native match。

| 配置 | 后继完整输出匹配，含 adaptations | Tree 原例 | Typed 原例 | 原例安装形状并集 |
| --- | ---: | ---: | ---: | ---: |
| Unmarked | 62/64 | 0 | 0 | 0 |
| Untiled | 62/64 | 7 | 15 | 22 |
| Requested tiled | 62/64 | 4 | 22 | 26 |

这些运行固定到同一个已证明的 compiler 入口。旧超时和旧计数继续保留，新的
corpus 摘要不把 requested-tiled 的 26 个安装形状当作 26 个已支持的分块变换。

## 接下来的验收

完整 identity-trace 对照已闭合，接下来追踪实际候选。对缺失的 source／target
结构、general pieces／ISS forward-progress 和真正的 tiling／域变换继续修复。
OLO compact entry-condition derivation、安全机器检查及 entry transport、重复
检查消除、CGO17 原计算和完整调用成本仍是验收目标。Safe refusal、输出匹配和
安装计数各自有用途，但不完成这组功能与效果要求。长期 goal 保持 active。
