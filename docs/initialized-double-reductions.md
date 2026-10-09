# 从实际初始化＋reduction 到完整内层模型

2026-10-09。本阶段组合[实际 instruction producer](double-source-instruction-factory.md)，
解决原 `mxv`、`matmul-init` 中初始化与 reduction 共享 memory/layout 的缺口。
从实际 canonical Clight body 产生普通描述数据，证明 initializer 后完整内层循环
与真实 PolCert `Loop` 的有限正常执行双向对应，并精确刻画内层 I64 iterator 出口。
外层循环、raw frontend progress、安全入口条件和整程序安装仍需接入；原 corpus
的 nonidentity optimized coverage 保持1/62。

## 数据接口和实际例子

[GuardMemoryDoubleInitializedReductionData.v](../adapters/compcert-memory/GuardMemoryDoubleInitializedReductionData.v)
提供：

```text
checked_double_initialized_reduction p outer_controls source
  : option double_initialized_reduction

double_initialized_reduction_layouts description
double_initialized_reduction_globals description
```

描述记录包含实际 inner iterator/header identifiers、initializer/body statements，
以及两条 checked instructions。Producer 从 source 提取候选形状，然后重建并精确
比较全部 statement，包括 signed-I64 reset、test 和 increment；同时检查实际
header/global declarations、iterator freshness 与合并 registry 的一致性。
不支持的 AST 返回 `None`。它接受以下实际 `mxv` row body：

```c
y[i + 2] = 0;
for (j = 0; j < N; j++)
  y[i + 2] = y[i + 2] + a[i + 2][j + 2] * x[j + 2];
```

Initializer 使用 outer controls `[i]`，body 使用 `[i;j]`；initializer 不读取
尚未初始化的 j。原 `matmul-init` 的对应组件使用 `[i;j]`、`[i;j;k]`。
Generic 库不固定 benchmark 名字、源 identifiers 或 tensor rank；两份 fixtures
绑定的是原输入导出 AST。当前识别器只处理上述 canonical 初始化＋单 assignment
reduction 形状，不已经支持任意 sequence/nest 或原 frontend 的 skip prefixes。

[GuardMemoryDoubleSourceTransport.v](../adapters/compcert-memory/GuardMemoryDoubleSourceTransport.v)
将旧单 instruction 的执行桥扩到经过检查的共同 registry。初始化与 reduction
可以有不同的访问列表，实际 runtime state 仍共享一个地址解释。
[GuardMemoryDoubleSourceLoopModel.v](../adapters/compcert-memory/GuardMemoryDoubleSourceLoopModel.v)
直接构造现有 PolCert AST：

```text
Seq (Instr initializer) (Loop 0 captured_count (Instr reduction))
```

Instruction arguments 根据 outer control 长度生成。Sequence 定律存在一个真实
intermediate memory：initializer 在 initial→middle 上执行，完整 reduction 在
middle→final 上执行。循环 model 没有另外建立一种执行 IR。

## 已证明的对应与事实来源

[GuardMemoryDoubleInitializedReductionSource.v](../adapters/compcert-memory/GuardMemoryDoubleInitializedReductionSource.v)
的 `double_initialized_reduction_source_model` 给出：

```text
actual initializer; initialized inner loop, finite E0 / Out_normal
  <-> real typed Seq/Loop execution with the same final memory
      and after = set inner_iterator (I64 captured_count) entry_temps
```

这里 count 为非负 nat，且不超过 signed-I64 上界。count=0 仍执行 initializer、
设置 inner iterator 为0，再退出；它不是空的整个 outer region。其他 source temps
保持，精确 IEEE expression tree 和 integer-zero assignment cast 沿用旧证明。

| 义务 | 已有生产者／本阶段处理 | 完整 factory 仍需交付 |
| --- | --- | --- |
| Source shape、types、accesses、共同 layouts | Actual AST check 和两个 instruction check 自动生产，重建完整 canonical body。 | 扩到实际 outer loops/sequence 和 raw frontend 结构。 |
| Global symbols、locals 没有遮蔽 | Language 的 program-binding 定律；本阶段从 checked declaration 生产 header symbol。 | 沿实际 program/site 环境运输这些事实；复用 scoped host。 |
| Point 的数学 bounds 和地址解释 | 新的 checked-bounds 服务从实际声明、共同 registry 和 bounds 生产 symbol/cell resolution。Actual fixtures 的 geometry lemmas 证明每个 control 在 `[0,98)` 时访问位于100 extent中。 | 从接受入口和 reached-state invariant 建立这些 bounds，不能要求 marked C 用户逐 point 证明。 |
| I64 controls 与公开 inner exit | Checked assignment frames、signed-I64 loop/control 定律及内部 invariant 自动组合；包括 count0。 | 外层出口、未到达内层 iterator 和完整 source progress。 |
| Header stability | Checked writes 与 header 使用不同 global IDs；language 证明实际 blocks 分离，initializer/reduction 的真实 store 保持原 Mint64 load。 | Header 的原入口 load receipt、安全 capture/range condition 和接受/拒绝状态运输。 |
| Operand loads/store 权限 | Actual source execution 或 typed memory action 包含成功的实际 `Mem.load`／`Mem.store`。 | 未到达 observation 的 safe invocation 须另证；metadata/bounds 不推断权限。 |

[GuardMemoryDoubleSourceResolvedPoints.v](../adapters/compcert-memory/GuardMemoryDoubleSourceResolvedPoints.v)
闭合“实际 coordinate bounds → registry 中的 physical cell”这一项。
它只生产地址，不读取 memory，也不证明访问有权限。Actual source wrapper 的有限
iff 消费数学 bounds，并在内部取得 address resolution；这些仍是后继 factory 的
逻辑前提。两份实际 geometry lemmas 已编译，但这里没有新增 emitted runtime guard。

## Narrative 对照和后续验收

本次重新 fetch 并核对全部远程 heads，narrative 最新可见为 `8ce9c8b`，
`paper-narrative.md` 与 `context-lifting.md` 已与 main 一致。本阶段遵循其责任切分：
kernel 组合局部证书，language 证明实际执行/安全/状态/安装定律，domain 从实际
source 数据组合模型桥。这里补的是 `C_opt` 内部的 source/model 对应；尚未新增
`C_derive` 的完整入口充分性、`C_guard` 的安全机器检查或新 `C_host` 安装实例。
四项名称指证据来源，不是源码用户必须填写的四份证明 record。

下一验收是原 `mxv` 的完整 marked region：外层 finite bridge 与 raw progress、
入口 N 许可/capture/范围、实际 proposal/validator/codegen、typed private resources、
candidate lowering、public exits 和 scoped Csem→Asm，然后原 `matmul-init`。
各 source 扩展随安装交付，不能将本内层对应当作整个 compiler 的完成。
`mvt` 的相继 nests、真实 tiling／ISS、原 BT 及完整成本继续保留在 active goal。
条件代码尺寸、运行时工作量和有用接受域分别验收。

审计结果见[机器摘要](initialized-double-reductions.json)：五库与实际 wrapper
共973行、39端点，13 closed、最多6 inherited globals；241 reachable sources，
共绑定8,105文件，无新增公理。五库18次 attempts 包含5次成功、13次拒绝；
wrapper 第三次成功，前两次失败源、日志与命令均保留。没有新增 native／性能证据。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_initialized_double_reductions.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/summarize_initialized_double_reductions.py --validate
```
