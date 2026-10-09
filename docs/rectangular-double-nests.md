# 独立循环边界：source/model 与依赖 capture 的证明阶段

本阶段为真实 double assignment nests 保留每轴独立的运行时边界，
准备接入已存在的 polyhedral compiler。原语料中的 `intratileopt1–4`、
`seq`、`spatial` 使用 `N/M`，原 `matmul` 使用 `M/N/K`；默认数值相同
不构成边界相等的语义前提。当前是 source/model、checker 和安全
capture 的证明阶段，尚没有该新源族的 factory、Csem→Asm 端点或
native 安装。既有共同边界路线的覆盖和成本仍见
[header-access 记录](double-header-access.md)。

## Narrative 对照

本轮 fetch 后，`origin/topdown/research-positioning` 仍为
`8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9`；两份 topdown 文档与
main 相同。本文落实 [paper narrative](topdown/paper-narrative.md)
§§3–6、8 和 [context lifting](topdown/context-lifting.md) 的已有澄清，
不声称看到额外的新提交。

最小 kernel 的边界仍是局部 guarded correctness。以下工作由语言服务
和 domain 实例完成；最后的安装须消费实际 site、当前 intermediate
program 和适用的 progress 证据。数学 footprint、memory permissions、
机器表示对应和读取许可分别证明。支持族的 C 使用者只给标注源码和策略；
这里尚未闭合的 factory 义务是实现者的工作。

## 用独立 N/M 走过证据链

考虑这种源形状，body 为已支持的实际 double assignment：

```c
for (i = 0; i < N; i++)
    for (j = 0; j < M; j++)
        BODY;
```

每轴 descriptor 记录 `(iterator, header)`。Source AST checker 检查
I64 global headers、iterator freshness、实际 leaf decoder 与完整语句
重建。Loop 参数是 `[n,m]`；内层 prefix 增长不改变各 header 的参数
位置。`double_rectangular_nest_canonical_source_model` 在明确 entry、
layout、范围和 stability 前提下证明实际有限 Clight 执行与 Loop 执行
的 iff，并精确恢复公开 iterator exits。

Domain 为两轴提议充分 cap `[cap_N,cap_M]`，静态 affine footprint
checker 检查 access rows 在独立轴包络内的数学范围。Cap 的有效性
不提供 header 读取许可，也没有自动提供物理地址和权限证据。

实际 capture 按轴执行：先读取并检查 `1<=N<=cap_N`，接受时缓存精确
I32 值；然后才读取并检查 `1<=M<=cap_M`。后一个读取的许可来自原
执行确实进入下一层的事实。前一步拒绝时停止；例如 `N==0` 时不观察
`M`。这条路线保守地拒绝任一非正边界，后续安装须执行当前 source
fallback，保持包括未进入内层时的公开 `j` 在内的状态。原 source
execution 是证明的语义起点，运行时没有预执行原片段。

接受后的 observation 接线把真实 `Mint64` loads、blocks、自然数
counts、I64 范围和 private caches 的精确 I32 值交给 source/model 的
observed-loads 接口。最终 factory 还要把 receipts、static layouts
和范围推导组合成全部 reached points 的 instruction readiness，并
用同一固定参数验证实际 candidate。

## 验证责任与当前状态

| 连接 | 责任与证据 | 本阶段状态 |
| --- | --- | --- |
| 原 AST 与独立参数模型 | Domain：实际 source reconstruction、leaf decoder、freshness 和有限执行对应 | 已编译；source/model theorem 仍有显式适用前提 |
| 入口范围推出数学 footprint | Domain：逐轴 cap、affine row 和 count/cap transport | checker 已编译；物理 layout、地址、权限和 reached readiness 待接线 |
| 检查安全调用 | Language：真实 global binding/load；原执行许可下一层读取 | 逐轴 source license 和短路 capture 已编译 |
| 接受事实与 private state | Language：精确 I64→I32、flag/cache frame、memory 保持与 observations | Capture 已编译；最终安装的 freshness、entry/refusal transport 待闭合 |
| Memory observations 的稳定性 | Language/domain：实际 array stores 保持各 header load | Source/model 使用已有 global-store frame；factory 待生产具体 binding/disjointness |
| 固定参数的实际 candidate | Domain：最终 body checker 和 progress；language：actual lowering、公开出口 | 此新族尚未接入 producer、factory 或 compiler |
| 局部结果到当前完整程序 | Language host/site：scope、placement、资源、progress 和 backend | 复用既有 host，尚未交付新族安装证明 |

这些 Clight 证明直接构造执行证据。Kernel/host 定律没有更改，不将
import 称为直接消费 generic guardify theorem。有限多次 rewrite 仍
要求每一步重新检查当前程序和资源。

## 接下来的交付门槛

1. 从原 declarations、actual header receipts 和逐轴 cap checker
   生产完整 entry/readiness 与稳定性证据，证明 capture 前后和拒绝
   fallback 的公开状态关系。Source/model 的前提由 factory 闭合。
2. 为实际捕获的独立参数构造最终 candidate、条件化验证、progress 和
   Clight lowering，接支持当前 program 的 scoped compiler，证明新
   Csem→Asm。保留原浮点运算树和真实数组语义。
3. 提取、安装原语料，验证 `N!=M`、空／负边界、逐轴拒绝、多个 marked
   regions、public exits 和完整输出。保存实际 schedule、generated
   candidate、最终 checker 与 assembly path。
4. 先功能，再检查尺寸、运行工作、接受域和完整调用成本。Sequential
   phases、BT、LLVM/SPEC 和 larger tiers 继续在 goal 中。

当前源形状仍限制为零起点、严格上界、global I64 headers 和 perfect
assignment nests。非零／inclusive／affine bounds、statement sequences
及 mixed/untiled phase results 不在本阶段覆盖内。

## 固定证明证据

九个新模块共 1,044 行，37 queried endpoints 中 18 个 closed；最大
assumption set 为六个既有 globals，没有增加全局假设。审计跟踪 262
reachable sources，结合 inherited baseline 固定 9,318 bindings，并
保留各次失败与成功的编译快照。其摘要见
[rectangular-double-nests.json](rectangular-double-nests.json)，完整报告为
`build/rectangular-double-nests/proof-v1/report.json`。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_rectangular_double_nests.py --validate
```

这份审计只验证新 source/capture 阶段及其输入，没有新增原 benchmark
安装、native／assembly 路径或成本结果。
