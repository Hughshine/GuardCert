# Loop／branch 事实简化已接实际 compiler 与原程序成本对照

本后继处理 [runtime pruning](double-tree-pruned.md) 测出的 body membership
成本。实际 compiler 先检查 affine reference，再运行已证明的 pruning、fact
residualization 和相邻 guard 合并，最后降低实际结果。新的 factory 和当前程序
安装证明消费同一结果，完整端点是
`DoubleTreeResidualCompiler.compile_selected_residual_double_tree_program_correct`，
证明成功编译时原 `Csem` 到目标 `Asm` 的 backward simulation。

## 事实与执行证明

[PolCertGuardResidualization.v](../theories/PolCertGuardResidualization.v) 提供
`residual_statement bounds facts statement`。调用者给参数区间和已认证事实；
算法随实际 Loop binders 和进入的 guards 扩充事实，消去被事实决定的 tests。
Unknown 保留原 atom。Loop bounds 无法分析时保留整个原 Loop。当前归一化只
递归处理表达式并消除除以 1；没有 SMT oracle 或未证明的代数等价。

循环变量加入环境头部，已有事实的 variable indices 相应提升。实际 `Zrange`
成员证明提供 lower ≤ iterator 和 iterator+1 ≤ upper；新区间 upper 是分析到的
最大上界减 1。已进入的 guard 提供其 conjunction facts。由此实例化通用
`ResidualGuardCurrent.residualize_property`，证明实际 Boolean 求值相同，再
证明 statement 的有限执行保持。`ResidualGuardCurrent.v` 是原
`ResidualGuard.v` 的逐字节副本，只为适配当前依赖重编译。

[PolCertAdjacentGuards.v](../theories/PolCertAdjacentGuards.v) 在相邻 guards 的
tests 相同时，将其合为一次检查和有序 body sequence。Loop 环境不随 instruction
的 memory effects 改变；实际 Clight lowering 提供缓存参数的 private frame。
此服务不许可合并任意会读写 public state 的 checks。

原 tricky3 在每个 point 先写 `dist_min`，再分别按 cluster 和 dimension counts
执行 scalar IEEE assignments。简化后的接受路径可读为：

```text
for p in [0, pointc):
  dist_min := 0
  if clusterc <= dims:
    for j in [0, dims):
      if j+1 <= clusterc: dist := 0; kmin := 0
      clusterv := 0
  if not (clusterc <= dims):
    for j in [0, clusterc):
      dist := 0; kmin := 0
      if j+1 <= dims: clusterv := 0
```

Outer membership 已由 outer range 保证；child 的 lower bound 和所属 loop 的
upper membership 也由 range 保证。参数区间保证 cap membership。仍需另一个
child 的 membership，所以每个 inner iteration 保留一个适用检查。相同的
dist／kmin guards 共用一次检查，不改变原 instructions 或 operands。

## 三方责任与实际接线

Framework 的最小 kernel 保持；generic formula residualization 是可复用条件库。
Domain 提供区间、binder／branch facts 及上述执行对应。Language 复用 typed
private cache、实际机器表达式／statement lowering、Mem／IEEE 指令定律和 public
exit restoration。[ResidualCandidate](../adapters/compcert-memory/GuardMemoryDoubleTreeResidualCandidate.v)
组合三个 postpasses 与实际 compiler correctness；新的 guarded execution、
factory 和 selected-program compiler 接同一 host／backend。

C 使用者提交标注原源码和 untrusted profiles／phase proposals，不给语义 callbacks。
Native adapter 只诊断同一 extracted pure postpasses，仍将 reference 返回 final
checker；实际候选由提取的 proved compiler 产生，没有 semantic extraction override。
原 fallback、safe capture 和公开出口的证明继续由实际 factory 消费。

[Proof audit](double-tree-residual.json)有七模块 834 行／14 端点，4 个 closed，
最多 42 个原 globals，无新增 globals。108 行是逐字节重编译的 generic library，
其余 726 行为新 domain／接线模块。十五次 proof attempts 七成功、八失败均保留。
Audit 遍历 569 个 reachable sources，绑定 10,624 个文件。

## 执行与成本证据

[固定 native 摘要](double-tree-residual-native.json)绑定实际 compiler、三原程序
五配置、runtime inputs、未修改的 assembly 观察和完整成本对照。十五配置全部
输出匹配，三个普通 marked regions 均安装；unmarked 和错误 shift 均零安装。
Requested tiled 仍不等于实际分块。

原 tricky3 computation 保持逐字节，只将三个常量 globals 改为 argv inputs。
一个 profile `[0,32]` 的 binary 通过 21/21 输入。十一条 GDB 路径确认 conditional
captures、空 outer 不读 child、拒绝短路、max-bound loops 和原 scalar store
次数／变换后的次序。Iteration steps 与剩余 membership 各执行 `p*max(c,d)` 次。
`(2,3,5)` 仍是 10 个 inner iterations，`(1,0,0)` 为零。

| 接受路径的静态代码 | 前序 pruning | 本后继 |
| --- | ---: | ---: |
| Model guards | 12 | 4 |
| 实际 cmp instructions | 21 | 7 |
| 实际 instructions | 112 | 38 |

比较使用同一原计算、profile `[0,4096]`，并保留前序 pruned 版和同版本 CompCert
backend 编译的 unmarked source。六输入、三版本、七随机 batches，126 个测量输出
全部匹配。完整子进程 user＋system CPU 包括 startup、argv、initialization、checks、
candidate／fallback、公开出口、digest 与 printing；没有 pinning／频率控制。
这不是 kernel-only 或孤立 guard 成本。

| 输入 `(p,c,d)` | Residual 中位 ms | Pruned 中位 ms | Source 中位 ms | Residual/source 配对比值中位数 |
| --- | ---: | ---: | ---: | ---: |
| `(4096,0,0)` | 0.568 | 0.543 | 0.484 | 0.993 |
| `(4096,3,5)` | 0.592 | 0.609 | 0.513 | 1.042 |
| `(4096,4096,4096)` | 11.243 | 27.432 | 15.043 | 0.754 |

比值取每个 batch 内的配对样本，故不等于两个中位数之比。满域案例改善前序
约 1.837 的 source slowdown；小输入由 startup 等成本主导，未建立一般收益。
其余 empty／fallback 输入及全部 raw samples 保留在固定报告。

## 剩余验收

此次是候选体内条件简化，不是 OLO 紧凑入口条件 synthesis。局部义务到入口条件、
安全机器检查及 entry/refusal transport、shared-check memoization 仍须交付。
General piece／ISS forward/progress、真实 tiling／其他 sequential 域变换，以及
完整 PolCert 配置和 CGO17 原程序／contexts／tiers 仍保留。长期 goal 保持 active。

[完整语料记录](double-tree-residual-corpus.json)尝试 62 原例＋两 disclosed initializer
adaptations，各有 unmarked／untiled／requested tiled 三配置，共 192 项。185 项
完整输出匹配；原 corcol3／pca 的六配置拒绝非 constant initializer，另有
jacobi-1d-imper 的 requested tiled 配置在 180 秒 compiler timeout。两个 adaptations
分别运行并匹配，不能替代原 source 的六项缺口。没有 native mismatch 或 link
failure，也不能把诊断完成叫作功能验收通过。

Untiled 有八个原例出现 guarded installation：fusion1、fusion6、fusion7、
jacobi-1d-imper、multi-loop-param、multi-stmt-stencil-seq、polynomial、tricky3。
这不等于八个 requested transformations 都已支持。多例 phase 输入为空模型；
具体 source/model producer 原因仍待定位，不能将它们写成 scheduler 无优化机会。
首次 corpus helper 在已有目录处拒绝执行，已单独保存失败；原目录未修改。

新 [CombinedDoubleTreeResidualCompiler](../prototype/interface/CombinedDoubleTreeResidualCompiler.v)
先运行 tree pass，再让旧 typed-double passes 消费实际 intermediate Clight program，
组成完整 Csem→Asm theorem。81 行／两端点审计无新增 globals，两个 native builds
已完成；第二个分别输出 tree 与 typed installation 诊断。完整 native 对照仍在
运行，其覆盖与成本尚未验收。本后继的 0.754 成本结果属于单独 residual 路线，
不能自动转给组合路线。
