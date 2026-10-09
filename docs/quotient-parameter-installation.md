# Quotient 参数：从安全捕获接到完整程序证明

2026-10-09，重新 fetch/read narrative 后，可见远端仍为
`8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9`，
[paper-narrative.md](topdown/paper-narrative.md) 与 main 一致。本阶段按其中的
三方责任及 source/model 桥要求，把私有 quotient 服务接到了新的
`Csem→Asm` 定理。九个新模块884行、15个审计端点、三个 closed；最大42个
既有 compiler globals，没有新增全局假设。审计绑定511份 reachable proof
sources及8,983个文件，失败尝试一并保留。

这是**证明接线阶段**。新路径尚未提取为 native compiler，没有新 C／assembly、
context、安装计数或性能结果。[固定摘要](quotient-parameter-installation.json)
只绑定这次证明，不把前一 build 的14/62、30sites或成本数字改称 quotient 结果。

## 为什么添加这个参数

[前一 prefix pruning](pruned-double-tiling.md)仍以 source footprint 提供的常数
cap 枚举 tile；小输入接受后可能跳过许多空 tile。要提议随输入变化的 affine
tile bounds，可先捕获 `q=ceil(n/d)`，再让候选把 q 当作模型参数。这里 d 是
正的编译策略常量，n 来自原有安全 I64→private I32 capture。

例如 `d=32,n=33` 时，q 为2；可提议以 q 为上界的 tile loop。**该提议仍需
最终 checker 验证实际 source/candidate**，不能只凭除法定理认定任意 tile
边界正确。当前新增接口允许不受信任 adapter 给出此类候选，尚未交付新的
native bounds producer。

数学关系为：

```
q = (n+d-1)/d     iff     0 <= d*q-n <= d-1       (d > 0)
```

它可由 affine tests 表达。最终验证同时使用旧范围 `0<=n<=limit` 和这个
关系，因此不会要求候选在任意独立 q/n 组合下都等价。一般 quotient 服务
使用 residual `numerator-d*q`，对数学整数 numerator 证明精确 floor 编码。
Clight capture 则保留现有非负 numerator 限制；不把负数截断除法当成 floor。

## 新接口及其调用契约

| 服务 | 安全调用／证明前提 | 成功提供的证据 |
| --- | --- | --- |
| `PolCertParameterExtensionFor` | 给定 Loop instruction/model 实例 | 在 iterator prefix 后插入参数，保持 expressions/tests/arguments 及实际 Loop 执行；loop 内的 cutoff 随 binder 增加 |
| `PolCertQuotientParameterFor` | divisor 为正 | quotient relation 与数学 floor 精确对应；relation 成立时可解除模型 Guard |
| `PolCertQuotientCaptureFor` | `compile_capture` 成功、typed view、已证明的 interval membership、目标 temp fresh | 实际 Clight `Sset` 执行、精确 quotient、扩展 typed view/ranges、relation 成立，保持 memory/events及指定公共 temps |
| double 实例 | checked 原 source、原 n capture／footprint 证据及 private resources | 安全 ceil capture，传输两套 functor 的 interval 证据，候选实际执行和公开出口恢复 |
| checked region/program factories | 实际 program 的 selection、scope、资源和 progress 检查 | 局部 region contract、当前 Clight program 的 simulation 和完整 Csem→Asm backward simulation |

Capture 的 static analyzer 检查 `n+d-1`、除法及所有 intermediate 的 I32
表示范围。只有原 n guard 接受后才执行它；如果不能构造安全代码，factory
静态拒绝该 quotient 路线。Typed view 和 range membership 是调用前提，
不是服务会自动执行的一组额外 runtime tests。原有捕获和语言证明生产它们。

检查过程的公共 memory／trace 不变；q/cache/flag 是私有状态。Freshness 和
frame 证明使 private writes 可以运输到实际候选入口。该服务属于条件库和
具体语言实例，最小 kernel 保持不变。

## 哪些证明真的被 compiler 消费

实际依赖链如下：

1. 既有 source checker、capture/model 证明从原 Clight 执行取得 source Loop、
   n 的精确值及入口范围。原执行是证明起点，不是 runtime 预执行。
2. `compiled_double_ceil_capture_execution` 证明实际 quotient capture，提供
   `[q,n]` typed environment、ranges及 `quotient_relation`。
3. `checked_double_reduction_quotient_guarded_execution` **消费该 relation**，
   经 `DoubleQuotientModel.quotient_relation_exact` 得到 q 的数学值。它不是
   忽略新证书而另行假定 q 正确。
4. `checked_double_quotient_tiled_prepared_loop_at` 消费参数插入定理，把原
   source 执行扩到 `[q,n]`。原 scheduling/codegen 在旧 source 上运行；raw
   candidate 插入参数后交给 adapter。最终 checker 在精确 entry relation 下
   验证实际 adapted body；witness extension 和 adaptation 都是数据提议。
5. `compiled_double_quotient_candidate_execution` 连接固定 `[q,n]` 参数的
   实际 candidate Loop 和实际 Clight。随后复用公开 I64 iterator 出口恢复。
   原 n guard 拒绝时跳过 quotient capture，执行原 source fallback。
6. `check_quotient_reduction_double_region_sound` 内部组合这些义务，产生
   scoped host 消费的局部 contract。新的 selected pass 对空表返回原 program；
   非空表复用既有 installation theorem。
7. `QuotientDoubleTiledStableCompiler.compile_selected_quotient_tiled_stable_program_correct`
   给出 Csem→Asm backward simulation。后续旧 passes 消费 quotient pass
   产生的**当前 intermediate program**，重新检查对应 site 的证据。

因此，新服务不只停在 Boolean 编码或一个未接线的执行 theorem。与此同时，
这条证明仍直接构造 Clight 分支，不能把 kernel 未改或 module import 写成
直接调用 generic `guardify` theorem 的复用证据。

## 使用者和实例作者分别提供什么

已支持族的 C 使用者沿用标注源码和策略输入。新增参数、检查、候选验证和
出口／安装证据由 factory 内部生产，不要求每个 site 提交 semantic callbacks。
Native producer 还需接入新的 entrypoint，才会成为可运行的用户路径。

新 source/transformation family 的作者仍要证明其 source/model 对应、充分
入口条件、候选 checker 的使用及实际 lowering；新语言／host 作者要证明检查
安全、private frame、控制／出口、progress 和安装。`C_opt/C_derive/C_guard/C_host`
说明证据来源，不要求用户手填四份固定 records。

本阶段只扩展既有共同 n、double assignment/reduction、静态 global tensors 的
source family。它不新增 loaded child bounds、动态 pointer alias、一般 min/max
machine expressions、任意前提提取、第二个 IR 或新的 host/kernel laws。

## 验收与下一步

全部九份新源码已用锁定 Rocq 工具链编译，15个端点通过 assumptions audit。
尝试记录保留缺 import、nominal interval 不同及证明修正；成功源码和对象冻结。
复核命令为：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_quotient_double_tiled_installation.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/summarize_quotient_double_tiling_proof.py --validate
```

下一步是新 native compiler：从实际 raw candidate 提议动态 affine quotient
bounds，保存 q 参数／bound receipts，重新识别真实安装，运行原 polynomial、
mvt/matmul、完整62原例及两适配、错误提议／静态拒绝、动态回退和完整程序
上下文。随后测量同 compiler／flags 的完整调用成本。现有旧路线保留为该
compiler 中 quotient 拒绝后的优化机会，不能把它的安装算成新 quotient 安装。

Broader source structures、ISS／其余 sequential phases、原 BT、LLVM／SPEC、
larger tiers、条件接受域和有用效果继续必需。完整 goal 保持 active。
