# 原 loaded setup 的许可、检查输入与局部 decoder

2026-10-08，本阶段为原 `i<*N; K=i+*M` 补上语言库证明。七个模块实际
编译，29 个公开端点独立查询 assumptions，1,332 个文件摘要绑定；每个
端点最多使用原基线中的六项 globals，没有新增公理。该阶段没有新
factory、提取编译器、Csem→Asm 实例或 native 接受结果。

## 具体问题与行为

目标原片段是以下 setup 形状，leaf 可由既有 checked affine-pointer package
描述。源码不预先无条件读取 `*M`。

```c
for (; i < *N; i++) {
    K = i + *M;
    for (j = 0; j < K; j++)
        p[32 + 64*i + j] = q[4096 + 64*i + j] + a;
}
```

Capture 使用 fresh private `Ncache` 与 `Mcache`：先读取原 root，只有原
首次比较 active 时才捕获 raw `*M`。若外层为空，不要求 M 指向可读 cell，
也不观察 M。若外层 active 而 child 为空，原 `K=i+*M` 已执行，header
中的 word load 有许可；leaf 与 RHS 仍需各自的 reached-source 证明。
目前 numeric preparation 沿用 first-positive-child 条件，因此 first child
为空而后继非空仍不能靠本阶段获得接受。

原 header 的替换首先保持实际机器字语义，包括 wrapping。只有随后 domain
的 arithmetic/range guard 接受，才建立候选所需数学值与 no-wrap 对应。
读取安全、初始捕获值相等、未来 observation preservation 是三个不同义务。

## 新的证明链与责任

| 交付 | 作者责任与确切端点 |
| --- | --- |
| 机器字表达式替换 | Language：[ClightWordReadSnapshots.v](../prototype/interface/ClightWordReadSnapshots.v) 的 `snapshot_word_replacement_evaluation`、`snapshot_word_setup_execution`。语法覆盖 signed32 constants/temps/loads 与 add/sub/mul；source eval 为 Vint 时才导出其 load leaves 的 Vint 许可。替换需要各实际 current load 与 cache 的 receipts，不默认任意表达式或 load 安全。 |
| 原 setup 的条件捕获 | Language：[ClightAffineHeaderSnapshots.v](../prototype/interface/ClightAffineHeaderSnapshots.v) 的 `affine_setup_capture_execution` 从 unchanged original source 完成执行取得 whole-header 和 raw-child 读取许可，证明实际 capture、memory frame 和 public transport。它不导出未来 stability。 |
| 原源到 preparation 输入 | Language/domain producer：[ClightAffineSnapshotSourceInputs.v](../prototype/interface/ClightAffineSnapshotSourceInputs.v) 的 `affine_snapshot_capture_source_inputs` 自动生产 conditional `affine_snapshot_original_domain`，保留原 source 执行及公开出口。调用者不用先提供完整 cached loop 执行。 |
| 实际算术条件 | Domain 复用已有 guard，language 生产许可：[ClightAffineSnapshotPreparation.v](../prototype/interface/ClightAffineSnapshotPreparation.v) 的 `affine_snapshot_preparation_condition` 消费新 original domain，给实际 readonly Clight guard 的安全、available 与 accepted ready facts。Header temp words 来自首个 reached row；body parameters/scalars 来自 first-positive child 的实际首个 leaf。 |
| 当前 row 的执行对应 | Language/domain：[ClightAffineSnapshotRows.v](../prototype/interface/ClightAffineSnapshotRows.v) 的 `affine_snapshot_actual_row_decode_exact` 消费当前 N/M observations，先把 actual loaded setup 运输到既有 affine decoder，导出 counted physical points 和公开 column/K 出口；不是把 row correspondence 留给任意 callback。 |
| 原源前缀与写权限 | Language：[ClightObservedBodyPrefix.v](../prototype/interface/ClightObservedBodyPrefix.v) 的 DECODE 显式消费当前 observations；[ClightAffineSnapshotPrefix.v](../prototype/interface/ClightAffineSnapshotPrefix.v) 的 `affine_snapshot_prefix_initial`、`affine_snapshot_prefix_write_receipts` 生产原前缀与实际 reached writes 的物理 permissions。数学 box 本身不许可任何 access。 |

七个新模块共 1,180 行，包含观察依赖 prefix 的后继定义及其 generic scanner
定律；行数不是作者时间或减少证明负担的证据。原 kernel、host contract 和
candidate checker 没有变化。新 domain/factory 作者仍须生产 checked package、
header grammar、cached-body 静态形状等式、cache membership 与 typed/fresh
resources。这些静态证据应由受检 source adapter 自动构造，不能让源码用户
手填 semantic proof record。

## 调用前提与完成边界

Capture theorem 消费原 source 的有限 `E0 / Out_normal` 完成执行，以及
quiet/frameable/freshness。该 finite contract 不生产 open/diverging progress，
也没有独立证明任意入口终止。Host/site 在最终安装中继续承担实际 progress、
placement、公开集合与 continuation。

`affine_snapshot_original_domain` 仅要求 root 的初始 receipt、root active
时的 child receipt，以及 unchanged original source 完成。Preparation 从
这些证据生产 Vint domains，不循环要求尚待证明的 complete cached source。
Numeric refusal 不推出 semantic 前提的否定；它只为后续 factory 的安全
fallback 提供拒绝路径。Readonly preparation 保持完整 entry；capture 可以
改 private temps，另有 memory/public frame。

新的观察依赖 prefix decoder 消费 current N/M relation。其 receipt 只许可
当前 row 的访问；只有成功的 point preservation 能推进下一 row。现有
旧 `ClightObservedHeaderPrefix` 的 temp-only decoder 仍保留原范围，未改写
其成功源码或对象。

## 复核与冻结证据

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python scripts/audit_affine_header_snapshots.py --validate
```

报告：`build/affine-header-snapshots/proof-v1/report.json`，SHA-256
`abf2a96eb8480716daa4e51edbbec04181af616e3d5e75796319aa1b59db057a`。
独立 audit 从新模块发现可达 proof closure 并查询 29 个端点；不重跑冻结
祖先审计。父 report 的 1,810 个摘要、独立 compatibility namespace 和旧
42-global allowed baseline 均复核。新端点最多六项，0 closed endpoints。

30 次 source-build snapshots/logs 均保留并绑定：7 次成功与 23 次证明源码
拒绝。失败来自缺失 imports、局部名称/参数和 tactic 使用，不能算成 native
误编译。成功 source/helper/objects 与 report 冻结，后续使用新模块。

另以旧编译器 disabled 模式观察实际 C 的 Clight dump：root test 保留
`i<*N`，setup 保留 whole `K=i+*M`，没有新增 unconditional M preload。
这只是 frontend 形状诊断，不计入本报告 proof bindings，不证明新 guard
已经安装或 actual raw AST/source package 对应。

## 后继任务

1. 复用实际 pointer-cell checks 与 reached write receipts，为 N/M 观察建立
   source-licensed separation 条件；成功才推进原 prefix。若复用其他
   value-preserving 条件，同样须建立此 observation relation，不能跳过读取许可。
2. 用已许可 observations 与原 source 执行导出整段 cached loop 执行和公开
  出口；复用既有 active loop transport、affine source/model 与 candidate
   checker，不把 complete cached source 当作 guard 安全输入。
3. Checked source factory 生产静态形状、cache 和 typed resources，接实际
   guard exit、fallback、公开恢复、selected host 与 Csem→Asm；用原 marked
   C 验证 accepted、refused、empty outer/M null、header alias 改变次数、
   wrapping、cap、continuation 和多个 sites。
4. 继续 first-empty-child、broader alias、recursive loaded domains、scalar/
   chunk、OLO 原例及 compact sufficient conditions 和完整成本。

本阶段是 [当前计划](current-work-plan.md) 中 actual-header 桥的证明进展，
不作为完整目标或新源族 compiler 接通的结论。
