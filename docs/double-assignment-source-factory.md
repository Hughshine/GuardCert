# Double 赋值：从实际语法生产局部模型数据

本页记录 assignment checkpoint；[actual instruction 后继](double-source-instruction-factory.md)
已增加通用 tensor/I64 access producer 和四个实际赋值节点的 typed INSTR 对应。
下文的地址／循环缺口描述属于本 checkpoint。

2026-10-09，再次 fetch 核对 narrative 分支 `8ce9c8b`，正文与 main 一致。
本阶段沿其责任划分处理原 `mxv`、`matmul-init` 暴露的赋值表示缺口。
两者都把整数常量 `0` 赋给 double 数组元素；实际导出的 Clight 保留
`Sassign lhs (Econst_int ... tint)`，转换发生在赋值语义中。原只接受
double RHS 的桥不能直接用于这些初始化。

现在有一个读取实际 assignment AST 的数据接口，以及两方向的局部执行证明。
原两个输入的初始化节点已经绑定到该接口。完整循环、地址 producer 和
编译器安装尚未扩展，nonidentity optimized corpus coverage 仍为1/62。

## 使用方式与实际保证

[GuardMemoryDoubleAssignmentFactory.v](../adapters/compcert-memory/GuardMemoryDoubleAssignmentFactory.v)
提供 `decode_double_assignment source : option double_assignment_descriptor`。
成功结果只有普通数据：

```text
double_assignment_target : actual destination expression
double_assignment_reads  : source operand expressions requiring address receipts
double_assignment_value  : exact double operation tree / literal bit representation
```

它读取源 `Sassign`，检查 destination 的 double 类型，再选择 constant 或
既有 double-expression decoder。Constant 服务支持 signed I32、signed I64
和 F64 literals，使用 CompCert 的 `Float.of_int` / `Float.of_long` 及实际
assignment cast。I64→F64 可能舍入；这里保留机器转换，并未证明任意整数
都能被 double 精确表示。F64 运算树继续保留原操作顺序，不做 reassociation。

[GuardMemoryDoubleAssignmentLiteral.v](../adapters/compcert-memory/GuardMemoryDoubleAssignmentLiteral.v)
证明原 literal assignment 与显式 F64 literal assignment 的全部有限执行
对应，保留 trace、memory、temporaries 和 outcome。该替换是证明中使用的
语言定律；原 fallback AST 仍可保持整数 RHS。

Factory 的 `decoded_double_assignment_source_execution` 从实际 source execution
得到 memory action，以及静默、正常出口和 temps 不变。
`decoded_double_assignment_model_execution` 从同一 action 构造实际原赋值执行。
`decoded_double_assignment_execution_iff` 给出有限正常执行的 iff。

这些定理消费 operand/destination 的实际 lvalue 与物理地址 receipts。语法
decoder 不生产地址、allocation、读取许可或 store permission。Literal
初始化没有 memory reads，但仍需要合法 destination；成功 memory action
包含实际 `Mem.store` 成功的证据。

Double expression 中保留为 read leaf 的表达式，还必须通过后继 address
producer。Temp operands、未知 casts 等可能取得语法描述符，却不属于当前
memory-only instruction 的可用 source family；完整 factory 必须生产对应
receipt 或安全拒绝，不能把 descriptor 当作完整 SCoP/model certificate。

## 三方的证明责任

| 提供者 | 本阶段提供或仍需提供的内容 |
| --- | --- |
| Framework kernel | 保持局部 guard/candidate 证书组合；不读取 assignment AST、IEEE 值或地址。 |
| Language library | 实际 literal casts、expression determinacy、load/store 和有限 assignment 执行定律。新 constant normalization 复用原 memory action 服务。 |
| Domain/source factory | 用实际语法生产 descriptor；后继还须从 layout、I64 indices 与 reached source state 生产地址 receipts，组合 Loop source/model、前提、guard 和真实候选。 |
| Host/site producer | 沿用实际 program scope、private resource、progress 与 selected installation；本阶段没有新 compiler endpoint。 |

这里的 receipt premises 是库之间的内部接口，不是要求 marked C 用户填写
semantic callbacks。完整源族的 checked factory 必须自动 discharge 它们。
此次没有合成新的 runtime condition；它补的是 `C_opt` 中的源赋值／模型对应。

## 原输入绑定与验证范围

使用冻结 exporter，直接导出先前 probe 绑定的原 `mxv`、`matmul-init` C；
除已记录的 scop markers 外无新增 source adaptation，保留 double arrays 和
I64 source counters。每个 marked region 含两个 assignment nodes，本次分别
闭合其一个 integer-zero initializer 的 decode 和执行 iff。Exporter 省略
administrative skips 的边界继续记录；这里绑定 assignment nodes，不宣称
得到完整 raw-region progress 或 loop bridge。

新增两库模块及 actual-source wrapper 共319行、17个审计端点、2 closed，
最多6 inherited globals；134 reachable sources，共绑定7,911文件，无新增公理。
Literal proof 的两次拒绝、一次成功与 factory 的成功均保留；actual-source
首个整目标计算未返回，主动中断并保留日志／metadata，后继 symbolic binding
编译成功。[机器摘要](double-assignment-source-factory.json)是完整 proof report
的核对投影，没有新 native、性能或 whole-program 覆盖结果。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_double_assignment_factory.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/summarize_double_assignment_factory.py --validate
```

下一项是实际 global tensor lvalue／I64 affine index 的数据 producer，再把
assignment、嵌套与 sequence source grammar 组合到原循环模型。`mxv` 的
初始化＋内层 reduction、`matmul-init` 的初始化＋三层计算，以及 `mvt` 的
两个相继 loop nests，是具体的后继验收输入。各扩展仍须走原 scheduler／
validator／codegen、安全 guard、公开出口、progress 和 Csem→Asm 安装。
真实 tiling／ISS、其他顺序 phases、原 BT 与完整成本继续属于整个 goal。
