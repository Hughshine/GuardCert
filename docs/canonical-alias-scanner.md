# Canonical alias 的实际 Clight scanner

2026-10-08。本阶段在已冻结的
[domain specification](canonical-alias-condition.md)之上，证明静态生成的
Clight 语句执行，关闭 machine bounds、canonical coordinates、pointer tests
和累积 Boolean flag 的语言编码义务。Kernel、candidate checker 和 host
contract 保持。Factory/compiler 安装和新 native/cost 尚未完成。

## 代码与使用接口

`canonical_affine_scan_statement dimensions positions limits left right bounds
scalars flag accesses` 返回一个 Clight statement。Counts/point lists 是证明
中的数学 witnesses，生成 AST 仅引用寄存器和静态 access templates：

```text
每轴 limits[k] := max(0, 2 * bounds[k] - 1)
for positions in rectangle(limits):
    delta[k] := positions[k] - (bounds[k] - 1)
    left[k]  := max(0, delta[k])
    right[k] := max(0, -delta[k])
    flag := flag && actual_affine_address_tests(left, right)
```

实际坐标 assignments 使用条件分支，不创建 `delta` 临时变量；实际
address tests 复用已有 Clight pointer equality 服务。Scanner 接收一个
已初始化的 Boolean flag，并累积结果；它不负责最外层条件分派。

在二维 2×3 例中，limits 是 3×5。Position `(2,3)` 表示 difference
`(1,1)`，生成 left=`(1,1)`、right=`(0,0)`，对应 domain 证明中的 canonical
pair。所有 generated points 在原 source box，原 source receipts 许可地址
比较。空 count 生成零 bound，rectangle 跳过 body；rank=0 使用已有
rectangle 的单个 empty-coordinate point 语义。

这些枚举域来自 specification，本阶段没有新的动态工作计数或复杂度
定理。当前扫描仍在 flag 为 false 后继续遍历；未实现 early refusal。

## 调用者需要提供什么

低层 `canonical_affine_scan_execution` 消费以下事实：

- 原 entry 的 layout/dimension view，source count/scalar word bindings。
- 每个 count 满足 `canonical_count_range`：非负、signed range，且
  `2*count-1 <= Int.max_signed`。
- 与 rank 一致的 positions/limits/left/right 列表；NoDup 与各私有资源相对
  source ports、live set 和 flag 的 freshness。
- 原 box 中各 access template 的 entry-memory `Readable` receipts。
- 原 entry 与实际检查入口在 bounds/read ports/live 上一致，实际 flag 为
  `memory_boolean_word accepted`。

它返回一份**真实 Clight execution**：有限、`E0`、`Out_normal`，memory
完全不变，bounds/read ports/live 保持，最终 flag 精确等于
`accepted && canonical_alias_check ... counts`。私有坐标和 controls 可以
改变；额外控制状态以当前值 frame，不要求与原源入口中未定义的 scratch
相等。因此应接带 private entry relation 的证书接口，而不是完整状态相等的
`readonly_condition`。

该执行定理不要求 uniform templates，因为它对任意传入 templates 执行
新 specification。**把接受结果用于原 candidate 的 nonalias 前提时**，须
消费 domain 的静态 `canonical_alias_templates_check` 与 source execution，
使用 `canonical_alias_source_exact` / `canonical_alias_source_nonalias`。
Safe execution 和 semantic sufficiency 是两项证明。

Receipts 是内部低层 theorem 的义务，尚未成为新的源码用户 callback API。
现有 domain 已证明从 source-model execution 生产 canonical receipts；下一
factory 必须实际运输原 header/numeric setup 的结果并自动调用这些服务，
不能把未接线的前提描述为已经自动生产。

## 责任与证明分解

| 模块 | 语言服务 | 端点数 |
| --- | --- | --- |
| [GuardMemoryCanonicalWord.v](../adapters/compcert-memory/GuardMemoryCanonicalWord.v) | 实际整数减法/比较、bound expression、单轴 bound 和坐标 statement | 8 |
| [GuardMemoryCanonicalPrepare.v](../adapters/compcert-memory/GuardMemoryCanonicalPrepare.v) | 任意 rank 的 bounds/coordinates execution，freshness 与 protected-state frame | 4 |
| [GuardMemoryCanonicalTests.v](../adapters/compcert-memory/GuardMemoryCanonicalTests.v) | 原许可的 pointer tests、实际 flag 更新、当前 private controls 的 frame | 1 |
| [GuardMemoryCanonicalScan.v](../adapters/compcert-memory/GuardMemoryCanonicalScan.v) | 完整 static rectangle scanner 执行及最终 Boolean/public frame | 1 |

Domain 库负责 coverage/alias 充分性，Clight 服务负责安全执行和运输，factory
负责实际 producer 接线及 region guarantee，language host 负责 installation。
`C_host` 的局部分派规律和整程序安装不是同一项证明。Kernel 无需知道 affine
maps、pointer blocks 或 cursor syntax。

## 审计与后续验收

独立 audit 查询四个新模块的 14 端点：4 closed、最多 6 项旧 globals，692
可达 source/object/helper/output bindings。冻结 parent 的 670 bindings 只核对
hash；历史 proof audits 未重跑。全部 globals 属于既有 42-global baseline，
无新增 axiom/admission；actual execution 使用已有 `external_functions_sem` /
`inline_assembly_sem`，不是新增语言公理。

报告：`build/canonical-encoder/proof-v1/report.json`，SHA-256
`cff492b3ac5bce0e8eab904b803b22dd077daf84256505770d1dd9c969166a37`。
成功源码/对象与独立查询均绑定；所有失败 snapshots/logs 保留。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_canonical_encoder.py --validate
```

`compile_canonical_encoder_sources.py` 只编译缺失对象，并保留成功对象。
新环境仍依赖前阶段 CompCert/PolCert proof prerequisites；这不是 fresh-build
完整 artifact。

下一步接 checked typed allocation、eligibility 和 factory：source setup 自动
生产 ranges/receipts，实际 scanner exit 接原 candidate/region contract，再
消费 selected compiler/backend。不匹配的 templates 或 range 静态条件应保留
原 scanner；runtime refusal 保留原 source。验证相同 native/context/full-output
矩阵后，再做新的完整配对成本。当前运行 compiler 仍使用旧 pair scan，完整
OLO/general affine 目标保持 active。
