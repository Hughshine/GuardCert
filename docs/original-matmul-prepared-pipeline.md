# 原 matmul：实际 double 调度、验证与 prepared codegen

同一原 matmul 已实际通过 extractor、OpenScop、Pluto、importer、typed validator
和 PolCert prepared codegen。Pluto 将原 i/j/k 改为 i/k/j，检查接受，生成的
Loop 保留原 IEEE double instruction。**尚未安装原 matmul C 优化**：入口
producer、安全 guard、固定参数下的源／候选连接、Clight lowering、progress
和 selected Csem→Asm 仍待完成。原 corpus 新增优化案例保持零。

## 真实输入与调用

复用[完整原源 bridge](original-matmul-full-nest.md)和实际 pipeline Loop 实例。
`OriginalMatmulPrepared.original_matmul_pipeline_request` 使用同一 exported
Clight 的 identifiers 和 `original_matmul_site`；没有另写目标循环或改变
double 数组／运算树。模型执行环境为 `[M;N;K]`；具名 parameter context
按 Loop 的约定使用反向的 `[K;N;M]`。

`original_matmul_request_source_execution` 从同一实际 selected region 的
完成执行构造这个 wrapped Loop 的执行，并保留原公开出口。Global registry
的 non-alias 由已证明的 symbol／layout 定律取得。Static、layout、条件式
header loads 和小范围仍是逻辑前提，没有新的自动 entry producer。
`original_matmul_request_exportable` 用 Rocq 计算证明实际 request 的 extractor
和 OpenScop exporter 都成功。

```text
实际 selected source 已证的三层 Loop
    → DoubleAssignmentExtractor.extractor
    → export_double_model
    → Pluto 提供 OpenScop 调度数据
    → DP.from_openscop_like_source
    → DoubleAssignmentValidator.validate
    → DoubleAssignmentPrepare.prepared_codegen
    → generated typed Loop
```

新 `GuardMemoryDoublePrepared` 提供带显式 untrusted callback 的 phase／Loop
入口，复用既有 affine expression／access 导出函数。Importer 保留原 instruction
和 accesses；callback 只提出数据。实际执行采用 typed validator 和 codegen，
而不是从 Pluto 生成的 C 获取执行语义。Exporter 当前拒绝 `DoubleBits`；
原 matmul 的 RHS 没有这类字面量。其他原案例需要的 literals／source／phase
扩展仍是待完成项。

## 实际结果

| Probe 模式 | 实际结果 | 证据 |
| --- | --- | --- |
| identity | 接受 | 原调度；codegen 加入参数正域 guard，原 double instruction 保留。 |
| affine | 接受 | Pluto 日志 `T(S1): (i_0, i_2, i_1)`；导入调度和 generated Loop 为 i/k/j。 |
| reverse | 拒绝 | 对实际返回的 schedule 逆转 iterator 系数；import 成功，原依赖 validator 路径拒绝。 |
| malformed | 拒绝 | 返回的 statement 集合被损坏，importer 拒绝。 |
| refuse | 拒绝 | 外部 producer 显式返回 Err，不运行 validator／codegen。 |

五项均只调用一次 scheduler callback，返回时无 alarm。这里的拒绝是 pipeline
返回 None，还没有安装后的 C runtime fallback 实验。Identity 不算优化效果。

Affine generated Loop 的 body arguments 为 `[v2;v0;v1]`：在 i/k/j 环境下
仍以 `[i;j;k]` 执行同一 C(i,j) 更新。它没有 reassociation 或改变每个输出
所依赖的 k 顺序。此处验证的是实际模型调度和候选生成，没有测量完整程序收益。

首个 native probe 的二次诊断导出失败：Pluto 返回 dense array IDs，而已有
writer 按 source sparse IDs 查表，产生 `Not_found`。原 build／源／失败目录
保持冻结。后继 probe 保存原返回文件与实际 callback 数据的二进制 receipt，
不再把 returned IDs 错当 source IDs 重写。最终验收另重现首个 probe 的
identity 失败，取得 exit code 2；它作为第六项预期失败保留。

## 证明边界与下一连接

四个新查询端点中，一个 closed，单端点最多十二 inherited globals，无新增
公理。新 adapter 为 135 行；audit 跟随 224 reachable sources，绑定 7,217
文件；两次成功、一次拒绝的 proof attempts 保留。Native 验收绑定 8,295
文件和六项调用记录。

`checked_double_prepared_loop_correct` 的方向是 **generated wrapped Loop
执行 → source wrapped Loop 执行**。Wrapped semantics 包含一个参数环境的
存在量化；现有 `InitEnv` 对该状态实例只规定长度。该结果不能单独替代
在同一实际 captured M/N/K 下的 conditional source/candidate bridge。最终
factory 必须把生成候选检查并连接到真实 checked parameters、Clight execution
和 public exits，再满足所用 host 的 progress 与安装要求。

因此本阶段交付 `C_opt` 的真实 typed proposal／validation／codegen 路径，
以及实际 source 到其输入的证明；完整 `C_opt`、`C_guard` 和 installation
尚未交付。Kernel、condition library 和 language host 的责任不由这个
backward Loop theorem 自动完成。源码用户仍只给 marked C 与策略，不承担
未完成的入口事实或语义 callback。

下一实现接 metadata／safe conditional capture、候选 Clight lowering及
固定参数证书，再复用 selected host／backend。Tiling、其他顺序阶段、全部
原 PolCert／CGO17 cases 和完整调用成本继续保留在总目标中。

## 冻结检查点与复现

机器摘要见[original-matmul-prepared-pipeline.json](original-matmul-prepared-pipeline.json)。

- Proof：`build/original-matmul/prepared-proof-v1/report.json`，SHA-256
  `bb9b91cc2f6b2385ccfd6d6330cc5803f856abf7793274f8e11ae994d29e1126`。
- Actual source：`build/original-matmul/source-prepared-v1/report.json`，SHA-256
  `7250a1be5a874a883342bac001e7eda2388e3ec14dd6c3cbfffe2cbbd0d8811b`。
- Native：`build/original-matmul/prepared-native-check-v1/report.json`，SHA-256
  `70bfaf01846864b716c663f3076703be02a89895de809a9374e6c88cb20016e0`。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/compile_matmul_prepared.py GuardMemoryDoublePrepared --attempt NAME
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/prove_original_matmul_prepared.py --attempt NAME
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_original_matmul_prepared.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/verify_original_matmul_prepared.py --validate
python3 scripts/summarize_original_matmul_prepared.py --validate
```

首建 audit、native verification 和 summary 不带 `--validate`。原 probe 用
`build_matmul_prepared_probe.py --attempt actual-source-double-extraction-v1`；
后继用 `build_matmul_prepared_receipt_probe.py --attempt dense-array-return-receipt-v2`。
Native helper 固定这两份成功 build 和既有 pinned Pluto，记录全部 argv、
stdout／stderr、scheduler inputs／outputs、模型／generated Loop 和预期失败。
运行时长仅作诊断；这些不是新的 C／Asm 执行或 speedup。
