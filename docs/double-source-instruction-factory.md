# 实际 double 赋值到 typed instruction 的数据接口

本阶段接上 [assignment decoder](double-assignment-source-factory.md) 的地址义务：
从实际 Clight 的 global tensor lvalue 和 I64 仿射下标生成 access 数据，核对实际
program 声明，再构造 layout registry 和 typed memory instruction。原 `mxv`、
`matmul-init` 的四个赋值节点全部通过该接口，并有有限正常执行的双向对应。
这是局部 source/model 服务；完整循环、runtime condition、progress 和安装尚未扩展。
原 corpus 的 nonidentity optimized coverage 仍为1/62。

## 调用方式

[GuardMemoryDoubleSourceInstruction.v](../adapters/compcert-memory/GuardMemoryDoubleSourceInstruction.v)
提供以下数据接口：

```text
checked_double_source_instruction p controls source
  : option double_source_instruction

double_source_instruction_model description
  : memory_value_instruction double_value_expression

double_source_instruction_layouts description : PTree.t (list Z)
double_source_instruction_globals description : list ident
```

`p` 是实际 program，`controls` 是该赋值使用的数学坐标对应的源 I64 temp 列表，
`source` 是选择器找到的实际 `Sassign`。成功只返回普通数据，没有 semantic
callbacks。Assignment decoder 保留原 double 运算树及 integer-literal assignment
cast；access decoder 保留各读写的实际源表达式。Registry 从这些 access 的实际
dimensions 构造，再检查重复 global 名字的 dimensions 一致。

例如，原 `mxv` 的 reduction 是：

```c
y[i + 2] = y[i + 2] + a[i + 2][j + 2] * x[j + 2];
```

以 `controls = [i; j]` 编码后，得到以下数学 access。方括号中的向量是对应
control 列表的系数，`2` 是常数项；表中名字对应实际 AST 的 identifiers。

| access | 仿射坐标 | layout |
| --- | --- | --- |
| write y / read y | `([1;0],2)` | `[100]` |
| read a | `([1;0],2); ([0;1],2)` | `[100;100]` |
| read x | `([0;1],2)` | `[100]` |

值树为 `Read(0) + (Read(1) * Read(2))`，保留实际 IEEE 运算顺序。
`y[i+2]=0` 初始化使用 `[i]`，reads 为空，值来自实际 integer-zero assignment
cast。`matmul-init` 的 initializer 使用 `[i;j]`，reduction 使用 `[i;j;k]`。
初始化的契约因此不会要求尚未赋值的内层 iterator。

## 成功检查与证明前提

[GuardMemoryLongSourceAffine.v](../adapters/compcert-memory/GuardMemoryLongSourceAffine.v)
接受 signed I64 temps/literals、signed I32 literal 到 I64 的 cast、仿射加减和
常量乘法。它重建并比较完整实际 AST，包括类型和操作；无法匹配的 unsigned
类型、属性、非线性乘法等拒绝。系数编码复用既有数学 affine encoder。
执行定理给出 `Vlong (Int64.repr mathematical_value)`，这是模算术对应，不能
用来声称整个源表达式从未 overflow。范围和控制语义仍须由具体源族证明。

[GuardMemoryDoubleSourceAccess.v](../adapters/compcert-memory/GuardMemoryDoubleSourceAccess.v)
重建任意 rank 的 nested-array lvalue，精确核对 array/pointer 类型与原表达式。
Static checker 核对实际 global 声明、正 dimensions 和物理 byte span。
[GuardMemoryDoubleAffineSourceAccess.v](../adapters/compcert-memory/GuardMemoryDoubleAffineSourceAccess.v)
将实际 coordinates 编成 affine rows，再从这些事实建立实际地址 receipt：

| 前提来源 | 提供的事实 |
| --- | --- |
| Static data check | 源 AST 重建、实际 global 类型、dimensions、byte span、registry 一致性。 |
| Language host | 实际 global environment 保持、local 没有遮蔽这些 globals。 |
| Reached source/model state | 对应 I64 temp 值，以及该数学 point 的读写 cells 能在 registry 中解析。解析检查 tensor coordinates 的 bounds。 |
| 原赋值执行 / model action | 实际 load 值、assignment cast、`Mem.store` 成功及最终 memory。 |

`checked_double_source_instruction_receipts` 内部组合这些事实，产生 destination 和
所有 operand 的 lvalue/address receipts。调用者不再逐 leaf 手工提供 receipt 或
固定 layout；但 host state 和 point resolution 仍是该局部服务的前提。它们必须
由完整 source factory 的静态检查、entry guard 和循环 invariant discharge，不能
转交给 marked C 用户。这里只从地址数据得到地址，没有从 metadata 推断 allocation、
读取权限或 destination store permission。

`checked_double_source_instruction_execution_iff` 证明同一 point 下：

```text
actual Sassign finite normal execution
  <-> actual typed INSTR semantics
```

两边保留实际 CompCert memory，source trace 为 `E0`，公开 temps 不变。模型 action
包含实际 load/store 语义。此定理不证明整个 loop 正常完成，也不由它单独推出调度
变换正确；候选仍须通过既有依赖／域 checker。任意 reassociation 不在本接口中。

## 与 narrative 的责任边界

再次 fetch 核对的 narrative 为 `8ce9c8b`，main 的正文一致。
本阶段没有修改 minimal kernel 或 host。Language 提供机器 expression、tensor
地址和 assignment 执行定律；domain producer 从实际 AST 生成数学 access/instruction
数据，消费语言服务；host 仍负责 scope、private resources、progress、placement 和
whole-program simulation。这补的是 `C_opt` 内部的 source/model 桥，尚未新增
`C_derive` 或 `C_guard` 的运行时条件。

Actual-source wrapper 只绑定四个 assignment nodes。Exporter 省略 administrative
skips 的既有边界继续保留，这里没有因此得到完整 raw-region progress。Generic
库没有固定 rank、benchmark 名字或源 global identifiers；fixture 的 identifiers
来自实际导出 AST。

审计数字及全部成功／失败 attempts 见[机器摘要](double-source-instruction-factory.json)。
四库与 actual-source wrapper 共776行、30端点、9 closed，最多6 inherited globals；
231 reachable sources，共绑定8,010文件，无新增公理。四库的22次 attempts 包括
4次成功和18次拒绝，wrapper 首次编译成功。审计检查 reachable proof closure、
继承公理和所有绑定文件的 hashes。没有新增 native 或性能结果。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_double_source_instructions.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/summarize_double_source_instructions.py --validate
```

下一步组合 actual assignment、loop 和 sequence source grammar，建立初始化＋
reduction 的 intermediate-memory 语义、实际 header 许可／稳定性、公开 I64 exits
及 source progress，复用真实 scheduling／validation／codegen 和安装到 Csem→Asm。
`mvt` 的相继 nests、真实 tiling／ISS、原 BT 与完整成本仍是后续验收要求。
