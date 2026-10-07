# 已到达常量子循环的 joint observation scan

2026-10-06。这是 [constant-body 权限桥](constant-bound-model.md)的实际检查消费者。
它把原 `<5` BODY 的执行许可接到真实 Clight 写地址比较，保护 root 和 indexed
child 的 raw observations；接受后生产内层 source-prefix 推进所需的 preservation。
完整 inner/outer runtime scan、canonical model、factory 和新 compiler 仍须接入。

## 从原源许可检查，再从检查取得稳定性

对一个实际到达的 `(row,column)`，原 component 子循环完整执行 `<5` 的 BODY。
它不会在 component stores 之间重读 enclosing loaded headers，因而允许某次 store
改变这些 headers。已有 decode 将这段真实执行映射到 checked affine leaf/model；
权限桥把全部点的 capabilities 带回 guard memory，不带回 source 已改写的数据值。

本阶段从这些 capabilities 生成写地址与观察地址的实际比较。Guard 不执行源
stores，不求值源数据 RHS。每个被比较的写地址都由同一已到达的子域许可。
一旦该 BODY 的 scan 接受，所有写与所有已捕获观察均分离，真实 store 定律保证
它们的 raw values 保持，才可以推进下一 column。未接受不许可扫描后续 BODY。

```text
实际 reached reset component; loop(component < 5) leaf
  → 当前子域全部 read/write capabilities at guard entry
  → 真实写地址 × 已捕获 word observations 的比较
  → scan accepts ⇒ 所有 point writes 与所有 observations 分离
  → 实际 BODY 保持 header snapshots
  → inner prefix j+1
```

这里的“全部”限于已到达的这个子域。不能从一次子域检查推出下一 row 的许可，
也不能把尚未证明的 cached outer/child completion 当作检查安全的输入。

## 观察地址不再限定于 pointer temp

[ClightAffineJointObservation.v](../prototype/interface/ClightAffineJointObservation.v)
定义 `clight_word_observer`：实际地址 expression、block/offset 和 captured raw value。
`word_observer_receipt` 将它们绑定到真实表达式求值及原入口 `Mem.loadv Mint32`。
Public-temp frame 运输该表达式求值，load receipt 提供比较需要的观察地址有效性和
alignment。不能用任意逻辑地址或 `p != q` 替代这个 receipt。

代码只使用 address expression；block/offset/value 是证明对象，不是额外 runtime
loads 或 pointer caches。于是同一次扫描可以比较写地址与 `shape`、`shape+1`，
无需再分配 child pointer temp。两项 observations 的生成见
[ClightNestedIndexedObservers.v](../prototype/interface/ClightNestedIndexedObservers.v)：
它消费 ordered capture 已提供的实际 root/child header evaluations，导出 raw receipts
和原两项 observation lists 的精确对应。空 outer 不会提供 child evaluation，不能调用
这个两观察消费者；此前的 outer-empty 短路仍必须保留在完整 guard 中。

当前比较模板面向 aligned Mint32 words。扩展到异宽 chunk、typed pointer stores 或
更一般的依赖地址仍需相应的语言／domain 定律，不能从 descriptor 的 expression 字段
推断这些场景已经得到支持。

## 实际检查与 inner prefix 的生产者

[ClightConstantBodyJointScan.v](../prototype/interface/ClightConstantBodyJointScan.v)
不要求调用者提交一个尚未证明的 `TESTS` 或 `PRESERVE` 回调：

| 端点 | 实际输入 | 实际结论 |
| --- | --- | --- |
| `constant_body_scan_write_binding` | checked leaf metadata、原 constant BODY 完成、权限运输、scan word view、pointer frame | 当前 point 写地址的真实求值与 guard-memory capability |
| `constant_body_joint_scan_execution` | 同一 reached source、numeric math domain、观察 receipts/scope、private controls/flag 的 freshness | 递归 Clight scan 实际正常执行，memory 与 live temps 保持，flag 精确累积全部比较的 Boolean |
| `constant_body_joint_scan_writes_apart` | 同一检查规格接受 | 所有 point writes 与每个 captured observation 的字节分离 |
| `constant_body_joint_scan_preserves_all_sources` | 上述接受、相同 coordinate/parameter view 和 pointer bindings 的任意实际 BODY 执行 | 在该实际 source memory 中保持全部 snapshots；不要求 memory 等于 guard entry |
| `constant_body_joint_scan_inner_advance` | 原 inner prefix、上述接受、header law、scope/writes/freshness 和 model-helper word | 复用语言权限运输及 prefix advance 得到原源下一 inner prefix |

第一次 reached source 是检查的许可；接受后的 preservation 对所有满足同一 view 的
实际 BODY executions 成立。这个量化区分使它可以填入现有 prefix 服务，避免把某一次
source completion 的保持误写成一般的 `expression_body_preserved`。

单个子域 scan 使用原 recursive scan library，拒绝 flag 会继续累积该已许可子域中的
剩余比较。它尚未证明跨 column/row 的实际拒绝短路；下一项用既有 short-circuit
prefix loop 组装这两层，只有接受才推进源 witness。扫描次数不是紧凑条件的成本结论。

## 使用者与责任边界

语言库提供 observer receipt 运输、pointer comparison 的真实语义、private Boolean
积累和 store-load 保持。Affine/domain 库消费 checked leaf、实际 reached source、
numeric domain、pointer/word views，生产具体比较和完整子域覆盖／preservation。
Generic kernel 没有修改，不理解 observations、affine points 或 loaded headers。

当前 source/model metadata、numeric 接受事实、控制名称及 scope/freshness 仍是
调用输入。Factory 后续应从原 AST、checked package 和 typed pool 生产它们。
本文没有把这些静态和入口证据称为已经自动完成的实例接入；language host 仍需
消费原源 progress、fallback、公开出口及实际安装位置，才能给出新 Csem→Asm。

## Figure 2 的实际 BODY fixture

[ClightConstantBodyJointExample.v](../prototype/interface/ClightConstantBodyJointExample.v)
使用适配例的真实 leaf：

```c
output[(row * 16 + column) * 5 + component] = row + column + component;
```

在 `row=column=0` 的入口，从 `reset component` 开始证明完整五次原 store 的实际
Clight 执行。具体 memory 为一个 40-byte allocation，两个 header words 初始化为零。
数据 base=0 与 headers 重叠，joint condition 拒绝；base=8 时，同一 block 的数据
访问与两个 headers 分离，condition 接受。实际 scan 的执行证明消费这份原 BODY
执行与权限，保留 memory/public temps，并给出对应 flag，不只计算一个数学 Boolean。

这个 fixture 没有证明 enclosing two-loaded source 的完整执行、候选的安装或新的
native 路径。它比前阶段 `component=4→5` 的单次 tail store 更完整，但仍只验收
已到达的 BODY 消费者。

## 验证和后续

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make constant-joint-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make constant-joint-validate
```

Audit 继承固定的 constant-model report，核对编译前后原 sources/objects，独立审计
新端点及旧完整 compiler assumptions。30 endpoints（7 language、12 domain、11
fixture）、569 required dependencies、含 inherited material 的 1,064 源摘要审计通过。
新端点最多使用 6 项已有 CompCert global assumptions，无新增公理；kernel 仍闭合，
旧完整 compiler 保持 42 项 assumptions。报告 SHA-256：
`ec30fcaf06fc7c32e2c2249e5a359b508633db935d27ac40086d6b5bad328284`。

`constant-joint-validate`、`constant-model-validate`、`nested-header-validate` 和
`loaded-offset-affine-validate` 均通过。后三项核对已有产物及其绑定，没有重跑
native 矩阵。当前是 inherited build 上的增量 audit，未另验空 build bootstrap；
没有新 compiler、extraction、native 或 timing。

下一连接：用原 inner prefix receipt 填入每个 column 的 actual BODY scan，组装
short-circuit inner loop；这一 row 检查完所有 observations 才推进 outer。随后将
已接受的 two-cache source 运输到完整 canonical model，接候选证书、original AST
factory、typed pool、host、Csem→Asm 与真实 C 的接受／fallback／context 验收。
功能链闭合后继续 compact sufficient conditions、实际工作量／接受域和计时。
