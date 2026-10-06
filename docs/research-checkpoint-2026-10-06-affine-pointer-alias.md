# 非矩形 pointer：源证据到完整只读条件

2026-10-06。延续 [源 package 阶段](research-checkpoint-2026-10-06-affine-pointer-source.md)，并按 [topdown narrative](topdown/paper-narrative.md) 区分 kernel、语言实例和 optimizer/domain。这次交付同一 normalized affine-inner 源 package 的算术、pointer receipt、包络分离与实际源执行连接。完整多面体 goal 保持 active；新候选规则、程序安装、提取与原生执行仍未完成。

## 使用者怎样调用

使用者提供真实源 statement，提出控制／参数 caps、pointer 列表和 window；原 `describe_memory_affine_pointer` 检查这些不受信任的元数据，成功返回 `memory_affine_inner_pointer_package source`。这些检查范围没有因本阶段扩大。

1. 用该 package 的表达式和 header 编译 width tree，成功结果有原机器编码证书。
2. 调用 [compile_affine_inner_pointer_package_envelopes](../prototype/interface/ClightAffineInnerPointerSourceGuard.v)，从同一 package 的真实访问表达式编译 alias tree；不安全的 endpoint 范围使编译返回 `None`。
3. 用 `affine_inner_pointer_source_guard_tree package width alias` 组合两树。先运行 header／范围／width／body 参数检查，接受后才运行 pointer 比较和包络比较。
4. 提交 retained source prefix 的 `source_observations_check` 成功证据和真实 prefix／source 执行。`affine_inner_pointer_source_prefix_domain` 产生实际入口 D；`affine_inner_pointer_source_prefix_guard_available` 证明该完整 guard 可以完成。
5. 消费 `affine_inner_pointer_source_guard_condition`：检查可安全执行、可以完成、入口不变，接受推出 `ready ∧ physical_nonalias`。`affine_inner_pointer_source_guard_execution` 再将同一次接受连接到真实源 Loop 执行和精确公开 i/j/k 出口。

这里的 D 是“真实源有限正常完成，且保留的源读取提供 raw-pointer receipt”。receipt 由源 prefix 的普通读取得到，没有插入 speculative load，没有在 D 中预设 non-alias。未完成或发散源不能仅凭这个 D 使用该定理；新 matcher／placement 尚未安装。

## 关闭的一个表示缺口

实际域仍是 `0<=i<N, 0<=j<U(i,parameters)`。width 证据给出所有行的 `U<=column_cap`，domain 库用 `[N;column_cap]` 覆盖实际点，但不读取这个盒内的额外单元。

旧包络编码要求观察向量的两个 count 都有入口寄存器。静态 column cap 没有这样的源寄存器；不能把它当成一个已有临时变量。新的 [AffineBoxConstants](../prototype/interface/AffineBoxConstants.v) 证明：将第二个变量的系数乘以静态 cap 并加入常数项，得到的 affine expression 与原表达式在 `N::column_cap::parameters` 上的值相同。

[ClightAffineInnerPointerEnvelope](../prototype/interface/ClightAffineInnerPointerEnvelope.v) 对四个包络 endpoint 进行该代入，再复用原 Clight modular affine 求值与有范围证书的 signed comparison。实际寄存器列表为 `bound::geometry_parameters`，其中 geometry parameters 本来包含 bound；重复观察 N 合法，静态 cap 不要求新增寄存器。该服务不要求 `U=i+1`，仍覆盖受原源 checker 支持的一般仿射内层上界。

符号条件保守地要求相关 pointers 为同一个实际 base，再检查包络分离。raw-base 比较的定义性来自源 receipt。不同 base 或包络相交导致 false，不由此断言实际别名，也不把 `p!=q` 当作分离证据。分离结论只作用于实际 ragged source footprint，包含四字节 chunk 与 modular pointer offset 的物理分离。

## 三方责任与四张证书

| 归属 | 本次新增／复用 | 尚需由使用者或下一阶段提供 |
| --- | --- | --- |
| kernel | 未改；继续消费 `sequence_readonly_conditions`，组合第一阶段事实与第二阶段安全域 | 不检查 source AST、指针、访问表达式或候选调度 |
| 语言／IR 实例 | 复用真实 source-load receipt、typed view、表达式确定性、reachable-test 安全；新固定 column 编码复用 Clight affine 比较定理 | 新源控制形状的进展／合法 placement、实际 guarded choice、完整程序运输 |
| optimizer/domain | 常量代入数学证明；同一 package 的访问覆盖、入口范围和宽度到实际 footprint non-alias；实际源 Loop／公开出口连接 | 独立 mapped-domain／dependence 候选证书、候选 encoder 和 validator 两套范围、实际候选与局部保持规则 |

`C_derive` 的覆盖和物理分离现已由本实例消费；`C_guard` 的算术与 alias 部分，以及 D 的源 producer 已绑定同一入口。`C_opt` 的源对应可以消费此次接受结果，但独立候选 certificate 尚未组装。prefix producer 是 `C_host` 所需的一项入口证据，不等于已完成 host 安装。

最难的剩余工作是把候选数学模型、实际 Clight lowering、两套表示范围与公开出口恢复同时绑定这份 source package，然后关闭新控制形状的 source progress／sequence placement。随后才可取得新 Csem→Asm 入口、提取和完整程序的非空接受／真实 alias 回退证据。一般依赖 preload、无限源宿主、性能及同例作者负担仍开放；端点数量和本次新增 570 行 Rocq 源码不作为复用收益或新颖性证据。

## 验证与产物

工具链仍为 CompCert v3.18 `14d616046360a0b2611ebdfc2f98368af402e1f7`、Rocq/Stdlib 9.2.0、OCaml 4.14.1；CompCert 的 VERSION／ASM 文本仍标 3.17。审计命令：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make affine-pointer-alias-proof
```

[report.json](../build/affine-pointer-alias/proof/report.json) 记录 79 个端点（其中 9 个语言端点）、526 项实际依赖、871 份源码摘要。报告 SHA-256：

```text
72fd42220910882727d9ad86060f66bc36854f9262d8a268d08807d47b550eb1
```

CompCert 基线含 35 项假设，domain 基线继承另 7 项 PolCert/VPL 假设；没有新增全局公理。三个新语言编码端点只使用其中 4 项 CompCert 继承假设，source guard／prefix／执行连接使用 6 项；常量代入、package 访问覆盖和 width 数学连接均闭合于全局上下文。独立核对全部报告源码与 `.vo` 摘要，均匹配当前产物。原 `compile_realized_observed_pointer_correct` 也在这个选定闭包内重新核对假设。

该命令编译变更和过期依赖并核对选定依赖闭包；没有请求 `--rebuild`，不描述成整个 CompCert 的 clean rebuild。Python 语法检查和 `git diff --check` 通过。

六个新 fixture 分别核对：实际 source package 可以编译完整 guard、静态 column 的比较可以编译、n=63 的包络接受、n=64 的保守拒绝、不安全 endpoint 编码静态拒绝，以及 n=0 的实际 Clight decision execution 在缺少指针和 body words 时提前拒绝。中间两项是数学 Boolean 计算，不是原生接受路径；空路径是真实 Clight decision theorem。fixture 不算新的 C frontend 绑定或编译器运行。

本次没有提取或 native 执行，旧 compiler／原生结果仍按其冻结 checkpoint 解释。前一 source-stage 报告没有覆盖，本阶段使用独立 `build/affine-pointer-alias/proof` 目录。旧一维 affine-access 源码与原 whole-program compiler 源码未改。
