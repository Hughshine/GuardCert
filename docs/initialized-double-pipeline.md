# 原始初始化循环：安全入口与真实候选 pipeline

本页保留 standalone checkpoint；后继的[实际 factory 与整程序安装](initialized-double-installation.md)
已完成两例 lowering／public restore／Csem→Asm 和原 C native 验收。

2026-10-09。本阶段将原 `mxv`、`matmul-init` 的完整 literal Clight source
接到实际 header capture、范围条件和真实 PolCert/Pluto pipeline。原执行在证明中
许可 header 读取；检查接受后产生 count 与 source/model 所需数值事实。实际
候选通过调度验证、prepared codegen 和最终候选检查后，在该 count 上保持最终
memory。两个案例尚未接到 candidate lowering、公开出口恢复和 scoped Csem→Asm。
原 corpus 的 installed nonidentity coverage 仍为1/62。

这承接[完整 initialized nests](initialized-double-nests.md)。旧检查点的入口
load/range 是逻辑前提；本阶段为两例生产它们。C 用户不需要填写数值或局部证明，
但完整 compiler factory 仍须检查实际 scope、分配 private resources 并完成安装。

## 入口条件如何获得许可与事实

[GuardMemoryDoubleInitializedEntry.v](../adapters/compcert-memory/GuardMemoryDoubleInitializedEntry.v)
消费 actual AST checker 返回的普通 descriptor，复用已有
`memory_long_range_capture header cache flag limit`：

```text
checked original region + actual header binding + original normal execution
  -> entry header load is defined
  -> compact I64 range capture executes, preserving memory
  -> flag is Boolean
  -> acceptance establishes 0 <= count <= limit and exact I32 cache
```

许可来自原 outer test 的执行，不是运行时先执行一次 source。Generic service
要求至少一层 outer loop、`0 <= limit <= Int.max_signed`，以及两个不同的 private
slots。实际两例使用 limit98、数组 extent100 与 padding2；接受范围通过此前的
geometry 服务建立所有 reached-point resolution，原 I64 source controls 不改变。

检查只写 private cache/flag，公开状态与 memory 保持。另一个定理从 private slots
与实际 source/public footprint 的分离，运输原 source execution 到 prepared entry。
接受与拒绝均有 fallback execution 和相同最终 memory/public temps；拒绝不推出
条件的逻辑否定，也不要求 cache 在拒绝时代表有效 count。

当前入口契约的起点是原 region 的有限 `E0 / Out_normal` 执行。它不是任意入口状态
上的 total-safety 定理，也不是本族 guard 在 open/diverging context 中的完整安装
证明。此前独立 source protocol 已有；完整 host 接线还须生产所需 region guarantee。
地址 bounds 不推断 allocation 或 load/store permission。

## 接入已有 Loop 与真实调度

[GuardMemoryDoublePipelineTransport.v](../adapters/compcert-memory/GuardMemoryDoublePipelineTransport.v)
在已有 source `DoubleAssignmentLoop` 与 generative pipeline `DoubleAssignmentIRs.Loop`
之间做结构转换。所有 expression、test、Loop/Instr/Seq/Guard 构造均保留；相同
typed instructions 和有限 execution 双向对应。它没有引入第二套执行 IR。

[GuardMemoryDoubleInitializedPipeline.v](../adapters/compcert-memory/GuardMemoryDoubleInitializedPipeline.v)
从已检查 descriptor、outer IDs 和实际 layout registry 构造 request。参数是同一个
实际 global N；两例的请求由完整原 source 数据计算得到，没有手写目标循环。

旧 double exporter 拒绝 `DoubleBits`，因而不能导出原 integer-zero→double
initializer。[literal 后继](../adapters/compcert-memory/GuardMemoryDoubleLiteralPrepared.v)
在 OpenScop 数据中保留 CompCert IEEE literal；native serializer 可以输出这些
有限数值，nonfinite 文本 literal 保守拒绝。候选 importer 始终保留原 typed
instruction，Pluto 返回的 textual C body 不作为新的执行语义导入。

真实 native 尝试随后发现两个表示问题：不同 statement depth 的 schedule 在前方
补零，破坏了共同坐标；importer 的另一路径混用了 parameter count 与 domain
dimension。旧路径的四次 `mxv` 尝试全部拒绝，`matmul-init` identity 诊断中断，
原始文件、日志与中断分类保留。

[uniform 后继](../adapters/compcert-memory/GuardMemoryDoubleUniformPrepared.v)
在 schedule 尾部补零到共同维数，并按实际 parameter count 导入所有 scattering
rows，再复用已有 canonicalization。导入仍保留原 instructions、domains、accesses
和 point witnesses。候选必须经过原 typed affine validator、prepared codegen，
最后重新 extraction、domain alignment 与双向 dependence validation；没有通过
绕过 checker 获得接受。

实际接口为：

```text
double_initialized_pipeline_request outer_ids checked_descriptor
checked_double_uniform_prepared_loop_progress schedule swaps request
```

`schedule` 是不受信任的 OpenScop producer。`swaps` 是不受信任的相邻坐标交换
见证，最终 checker 核对其充分性。任一步失败都拒绝 candidate。实际 wrapper
将 accepted capture 的 count 接到最终 generated Loop；source-user 不提供 header
load/range 或 point-resolution callbacks。

## 真实候选效果与拒绝

Standalone extracted probe 对两个原 source requests 调用实际 Pluto。它构造并验证
Loop candidate，不执行 original/generated C 或 assembly。

| 案例与路线 | Phase/codegen | 最终结果 | 实际候选 |
| --- | --- | --- | --- |
| mxv identity，空见证 | 接受 | 接受 | 保持 source 执行顺序，增加 codegen guards/结构。 |
| mxv affine，空见证或 swap1 | 接受 | 接受 | 初始化与 reduction 分成两段。 |
| mxv affine，swap0 | 接受 | 拒绝 | 见证不能建立最终对应。 |
| matmul-init identity，空见证 | 接受 | 接受 | 保持 source 执行顺序。 |
| matmul-init affine，空见证或 swap0 | 接受 | 拒绝 | 尚未建立最终坐标对应。 |
| matmul-init affine，swap1 | 接受 | 接受 | 初始化/reduction 分段，reduction 为 i/k/j。 |
| 两例的 reverse、malformed、external refuse | 拒绝 | 拒绝 | 不安装候选。 |

共14次：5接受、9拒绝、0超时。Identity 的 AST/schedule padding 变化不计为
优化效果；affine 的 fission 与 i/k/j 来自保存的实际 candidate。每个被接受的
candidate 都保留原 double instructions，并通过最终 checker。这里没有新的
guard-cost、完整调用性能或 installed optimized-case 结论。

## 责任划分与下一步

本阶段沿 `topdown/research-positioning@8ce9c8b` 的澄清推进：

| 责任 | 本阶段交付 | 尚需完整 factory 交付 |
| --- | --- | --- |
| Framework | 复用局部证书组合，kernel 不变。 | 消费实际 language/domain certificates。 |
| Language instance | 实际 load/capture 定律、private/public frame、source transport、两种已有 Loop 的 execution transport。 | Actual typed allocation、candidate Clight execution、公开 I64 exit 恢复、host guarantee 和安装。 |
| Optimizer/domain | Actual descriptor→request、共同 scattering 坐标、checked import/validation/codegen、captured count→candidate execution。 | 连接 candidate bounds/lowering、实际 site/static receipts 与完整程序 compiler；继续 tiling/ISS 等真实顺序阶段。 |

`C_opt`／`C_derive`／`C_guard`／`C_host` 表示证据来源，不是让源码用户填四份
record。原执行、static metadata、capture/range、state transport 分别生产适用事实。
Finite candidate execution 不单独建立 progress/divergence 或整程序 correctness。

下一项直接将原 `mxv` 的接受候选 lower 到实际 Clight，恢复原 public I64 controls，
接 actual typed resources 与既有 scoped host，再验收原 C 的安装/回退及 Csem→Asm。
同一路径随后用于 `matmul-init`。其他原案例、相继 nests、BT、sequential phases
和完整成本继续在 active goal 中。

## 验证与复现

五库与三份 actual wrappers 共1,052行、29个新 audited endpoints，2 closed，
最多14 inherited globals；最后 audit 的 reachable closure 为293 sources。两个
proof audits 分别绑定8,359／8,392文件，native aggregate 绑定10,541文件，无新增
公理。11次 generic-library attempts 为5成功／6失败；7次 wrapper attempts 为
3成功／2失败／2显式中断。两次失败 native builds 和旧坐标诊断均保留。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_initialized_double_uniform_pipeline.py --validate
python3 scripts/validate_initialized_double_pipeline.py --validate
python3 scripts/summarize_initialized_double_pipeline.py --validate
```

[机器摘要](initialized-double-pipeline.json)给出冻结 reports、hashes 和逐项结果。
成功 sources/objects/builds 不重写。Whole-program coverage 保持1/62，整个 goal
保持 active。
