# 原源许可的 inner 短路扫描与整行接受

2026-10-07。[前一 BODY 消费者](constant-body-joint-scan.md)现已接到实际 inner
Clight loop。它逐 column 消费原源 prefix receipt，运行完整 constant BODY 的双观察
检查；接受才推进源 prefix，拒绝时 break。整行接受生产所有 column 的原 BODY
preservation，并直接接到 outer-prefix advance。实际 outer runtime loop、完整模型、
factory／候选安装和新 compiler 仍待连接。

## 实际代码和许可

[ClightConstantJointInnerScan.v](../prototype/interface/ClightConstantJointInnerScan.v)
生成的结构是：

```c
scan_limit = child_cache;
scan_column = 0;
for (; scan_column < scan_limit; ++scan_column) {
    /* 当前 constant BODY 的完整写地址 × observations 比较；不执行 stores */
    if (!flag) break;
}
```

`flag` 从上一已接受阶段保持为 true，不在每行重新初始化。每个 column 进入时，
`expression_body_prefix_receipt_at` 取得当前真实原 BODY 的完整执行及 permissions
back。旧 BODY 消费者许可这段子域的全部比较，内层运行定理不要求调用者另交
`BODY`／`TESTS`／`PRESERVE` 回调。接受推出观察保持，才生成下一 source prefix。

已到达 BODY 内仍累积全部比较，即使某项已拒绝；它内部的全部点均已有许可。
跨 column 的拒绝立即退出。`constant_joint_inner_first_refusal` 证明首次拒绝的
实际 guard 游标仍为零，没有 increment、后续 BODY 执行或其物理许可前提。
一般 loop 定理复用已有短路循环证明，在任一拒绝位置同样停止递归检查。

`constant_joint_inner_empty_execution` 另证实际 cache 为零时只复制 bound、清零
private cursor 并退出。该端点没有 observation、参数 word、output pointer 或 source
BODY receipt 前提；空 child 不许可、更不需要执行 BODY。完整入口仍须由 ordered
capture 许可这个 cache，empty outer 必须跳过 child capture 和整段 inner guard。
通用 prefix 接入当前要求 child count 非负；负的 empty child 的接入策略仍需在
完整 runtime gate／fallback 中明确，本文没有宣称已经接受。

## 原源入口与 guard 状态分开

原 source prefix 的 temps 记录实际逻辑 row／column，memory 记录源已到达的 stores。
Guard memory 保持原入口；检查代码用 private cursors，不能把公开 row 改成待扫描
row 来满足地址求值。

接口因此有独立的 source `entry`、guard `base`、`public` 和 `live`：

- `BASE_PUBLIC` 只连接两份状态共同的公开观察、指针和 cache。
- Source words 从原 prefix 的 protected-temp frame 取得。
- Guard words 通过 `values` 映射读取；row 可以映射为包围的 private cursor。
  `OTHER_LIVE` 保证这些映射名称受保护，column 则映射到当前 private cursor。
- 空域不要求 `BASE_WORDS`：它只在有 active column 时提供。完整 factory 仍须
  从实际 capture／numeric condition 和 namespace checker 生产这些 facts。

观察和 data locations 仍绑定真实地址／load receipts；`memory_accesses_back` 只
运输权限，没有把 source 已写后的数据值运输成 guard-entry 值。

## 固定入口的 header 服务

[ClightExpressionPrefixAt.v](../prototype/interface/ClightExpressionPrefixAt.v)复用原
prefix 服务，把 readiness 限制在当前入口，提供 `expression_body_prefix_receipt_at`
和 `expression_body_prefix_advance_at`。使用者只证明当前捕获入口的 header law，
无需对无关入口的任意 cache words 作保证。原 prefix 服务及 semantic kernel 没有修改。

[ClightJointInnerRowFrame.v](../prototype/interface/ClightJointInnerRowFrame.v)证明
logical inner entry 与原 outer entry 的 protected-temp／cache 对应。这些是语言
运输定律，不发现 source footprint 或候选前提。

## 从整行检查直接推进 outer

`constant_joint_current_row_execution` 消费原 outer prefix，调用已有
`nested_expression_prefix_open` 取得当前 inner prefix，而后运行上述真实 loop。
整行接受时，它同时生产：

1. 每个 column 的任意同 view 实际 BODY 执行都保持全部 captured snapshots。
   结论使用原 outer entry 的 row／column／stable frame，可供完整 cached-source
   transport 使用，不只保持某一次 chosen source witness。
2. 原 outer prefix 的 `i+1`。这个结论来自整行接受后的观察保持，不能许可尚未
   检查的下一 row；下一 row 仍须由实际 outer runtime loop 取得自己的 receipt。

调用输入仍包含 checked affine leaf／lowering、numeric math domain、原 source
word views、helper 初始化、scope/writes、私有名称及当前 header 定律。
Domain adapter 生产真实比较、覆盖和 preservation；语言库实现机器语义、frames
及 prefix 运输；kernel 消费最终证书，保持不变。新 original AST matcher、typed
pool checker 和完整 materialized guard certificate 尚未生产这些入口数据。

## 验证与后续

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make constant-joint-inner-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make constant-joint-inner-validate
```

独立 audit 继承固定的前一 BODY report，核对其 sources／objects，审计新 language／
domain endpoints、kernel 和旧完整 compiler assumptions。14 endpoints（5 language、
9 domain）、563 required dependencies、含 inherited material 的 1,067 源摘要通过。
新端点最多使用 6 项已有 CompCert globals，无新增公理；kernel 保持闭合，旧完整
compiler 保持 42 项 assumptions。报告 SHA-256：
`173626b13944a2572027a52ba3836560ea6f3fbfcac08d34372edd35d296732d`。

当前 inner、前一 BODY、constant-model、nested-header 及 loaded-offset validators
均通过。旧 native/path/work 只核对已有报告绑定，没有重跑矩阵。此次是 inherited
build 上的增量 audit，未另验空 build bootstrap。
本阶段没有新 compiler、extraction、native 或 timing，也没有新增具体数组
fixture；这里的 loop／refusal／empty／row advance 是实际 Clight 执行的量化证明。

下一项是实际 outer 短路循环及全部 rows 的 coverage，随后从接受生产完整
two-cache source 和 canonical model，接旧候选证书、原 AST factory、typed pool、
host、Csem→Asm 和真实 C 的接受／fallback／context。功能链闭合后继续 compact
条件、接受域／工作量／计时和同例作者责任比较。完整目标 active。
