# 空 child 前缀、后续 body 许可与紧凑入口条件

2026-10-08，接续 [实际 loaded-affine pipeline](snapshot-polyhedral-native-pipeline.md)。
本阶段解决 first-empty-child 接受域扩展的一项证明依赖：从原执行恢复后续
真正到达的 body，并把其输入许可运输回检查入口。新条件服务已证明安全与
接受充分性；原 compiler/factory 尚未消费它，native 接受域保持原状。
完整目标继续 active。

## 为什么不能只放宽 Boolean

原 source 是 `i<*N; K=i+*M`，例如 `N=3, M=0` 时第一 row 的 child 为空，
第二 row 的 child 非空。Original source 首次 header 已许可 M，尚未许可
第一 row 的 body/RHS。旧 preparation 只利用首个 body，width 条件因此
要求 `K(0)>0`。从其 Boolean 中删除这一项，并不能证明后续 scalar/range/
address checks 可读。

另一处限制在 domain：`memory_source_width_model` 与
`memory_parametric_assumed_loop` 也包含 `1<=K(0)`，候选 certificate 只在
这个模型域下有效。新的运行时条件不能把该 certificate 自动扩大到
`K(0)=0`。这些模型域、source decoder 和 factory 的连接是下一阶段任务。

## 实际原执行提供什么

[ClightLeadingEmptyRows.v](../prototype/interface/ClightLeadingEmptyRows.v)给出
可复用的语言服务。`affine_setup_empty_child_run` 对任意 body 成立：header
求出 signed word，且 `Int.lt 0 word=false` 时，实际 setup 只赋 K、重置 j，
不执行 body，不要求它的 scalar、地址或 RHS 已定义。

`leading_empty_rows_recover` 消费给定原 source 的有限完成执行、原活动
root test、已许可的空 child header 及 protected ports，恢复越过任意有限
空前缀后的原 source suffix。入口内存与 protected temps 保持；实际 row
递增与 signed 范围逐步证明。`leading_empty_rows_body_receipt` 再取得后续
实际 reached setup；`affine_setup_active_child_receipt` 从它恢复 active leaf。
这是证明中恢复原执行，不是在运行时先执行原程序来许可 guard。

[ClightAffineSnapshotLaterBody.v](../prototype/interface/ClightAffineSnapshotLaterBody.v)
将服务实例化到现有 checked snapshot source package：

- `snapshot_later_header_value` 只消费原 domain、已捕获 header 参数与
  protected ports；不要求 body-only 参数已定义。Static shape equality
  将 replaced raw header 连接到同一 cached affine expression。
- `affine_snapshot_later_leaf_receipt` 在提出的 skip 前缀为空、下一 child
  active 时，产生在原入口内存上的实际 leaf 执行。
- `affine_snapshot_later_body_words` 从真实 array operations 的 address/
  scalar 使用和 leaf 执行，产生入口 body 参数的 signed-word typing。
  它不假定先执行了完整 cached loop，也不要求未来 header 已稳定。

该服务可处理机器字意义的负或零 empty prefix。它尚不建立后续所有点的
footprint receipts、全循环 N/M stability、nonalias 或 candidate 正确性。
这些义务不能从一个 reached body 的许可中推断。

## 条件推导与编码

[ClightFirstReachedWidth.v](../prototype/interface/ClightFirstReachedWidth.v)
接受 ordinary `skip` 提案、仿射 header 表达式、checked parameter bounds
和 low/high limits。令 `U(i)` 为该 header 的数学值，条件检查：

```text
skip + 1 <= N
low <= U(0) <= high
low <= U(N-1) <= high
1 <= U(skip)
skip > 0 时 U(skip-1) <= 0
```

`first_reached_width_math_sound` 利用仿射线性／端点范围证明全部 skipped
children 非活动、选中 child 活动，以及全域 header 范围。检查数为常数，
表达式尺寸仍取决于原 header；这项条件不代替 alias/stability 扫描。
服务不寻找最优 skip，也不推导任意程序的 weakest precondition。

`compile_first_reached_width` 复用现有 checked machine-arithmetic lowering；
`compile_first_reached_width_exact` 在 typed header view 与参数 bounds 下
证明实际 decision run 的精确 Boolean。无法编码时返回 `None`。
`first_reached_width_word_facts` 在 `Int.min_signed<=low` 和
`high<=Int.max_signed` 下连接数学事实与实际 `Int.lt` 条件；不能仅根据
数学上 positive 就断言原 wrapping header 是 active。

[ClightAffineSnapshotReachedCondition.v](../prototype/interface/ClightAffineSnapshotReachedCondition.v)
把编码接到实际 source 许可，并交付 `snapshot_first_reached_condition`。

| 契约项 | 本阶段保证与提供者 |
| --- | --- |
| Inputs | Checked source package、ordinary skip/bounds/limits 和实际编译出的 tree；domain proposer 可以不受信任。 |
| Requires | 原 capture/source domain、已检查的 outer header 和 header 参数 bounds。没有 body-only typing、cached completion、nonalias 或 candidate certificate 前提。 |
| Safe invocation producer | Language 从原 reached headers/capture 取得读取许可；已有 header/range 服务生产对应条件。新服务自行从这些事实建立 typed header view。 |
| Accepted ensures | Domain 的 first-reached/range 事实，及原入口 body address/scalar 参数可读。后者来自原实际 later leaf，不是此前要求调用者给出的事实。 |
| Effects / refusal | Readonly decision tree 保持完整 check-entry state；拒绝安全，不推出前提的否定，也不许可读取 body-only 参数。 |
| Caller responsibility | 只在该条件接受后调用需要 body typing 的 checks；保留 conditional capture 的私有入口运输。Factory、site 和 host 仍负责后续 candidate/fallback、公开出口和全局安装。 |

源码用户的目标接口仍是 supported marked C 与策略。本阶段没有把
`SOURCE`、header typing 或 decode 当作新的源码用户 callback；但新服务
尚未由安装 factory 调用，因此不声称已交付新的源码用户优化能力。

## 编译与审计证据

五模块共 680 行；24 queried endpoints、9 closed、至多旧六项 globals，
无新增公理。28 次 source-build attempts 含五次成功及 23 次 proof-source
拒绝，全部 source/log 保存；它们是证明开发记录，不是 compiler/runtime
miscompilation。原成功模块、对象、compiler 和 reports 保持。

[闭合计算](../prototype/interface/ClightFirstReachedWidthExamples.v)确认新 guard
可以编译；`N=3,M=0,skip=1` 的新条件接受而旧 width-model 拒绝；负／零
前缀的参数条件也可接受。后续 child 不存在、错误提案把已非空 row 称作空
前缀时均拒绝。这五项是 condition-library 计算，不是 native 优化接受结果。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/compile_leading_empty_rows.py --attempt initial
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_leading_empty_rows.py
```

Report：`build/leading-empty-rows/proof-v1/report.json`；SHA-256：
`a0d2f284662d043e1830c9dcc29025fa42e448a13e0ccb20dcb8e1d605147867`。
Reachable proof closure、helpers、父 report、成功及失败 snapshots 共绑定
1,432 个文件。旧 native report 的 2,500 bindings 重新核对通过；没有
重复 native 运行或新增性能证据。

## 下一步连接

先为允许 zero-width children 的实际 cached source 证明 source/model
执行对应及退出公式，并用放宽后的 assumed model 重新验证候选。旧
certificate 中的 `1<=U(0)` 不能默默略过。准备入口的 body typing 使用
本服务，reached-point permissions 与稳定性继续由原 source 执行逐步生产。
随后接 checked factory、compact plan、selected compiler 与实际 C/native
接受／回退矩阵，复用语言 installation/backend。

负 width 的 receipt 不等于负 width 的模型／出口证明：旧
`memory_parametric_settle` 对 j 的公式依赖非负 width；实际负 child 会
保留 reset 的 `j=0`。扩大到该情况还需对应出口证明。Broader alias、
recursive loaded domains、OLO 具体源与完整成本仍属于原完整目标。
