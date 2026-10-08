# Canonical difference alias 条件：域服务证明

2026-10-08。基于 [完整调用成本](word-nested-store-complete-cost.md)的负面结果，
本阶段实现减少 alias 比较域的基础服务，并证明它对应实际 CompCert locations。
它仍是 **Boolean specification/domain 服务**；真实 Clight scanner、factory、
compiler 和新的完整成本尚未接入。当前运行 compiler 仍使用原 point-pair scan。
完整 goal 保持 active。

## 原问题与可检查子集

原条件对 source 矩形域中的所有 point pairs，检查所有静态 access template
pairs。对于 n×m 域，point-pair 空间有 `(n*m)^2` 个成员。最新 8×8 row
diagnostic 仍执行 71,234 次完整 guard tests，其中仅 15 次是 numeric setup。

新服务的 eligibility checker 为 `canonical_alias_templates_check accesses`：
所有 access templates 的 **完整 affine coordinate maps** 必须严格相同。
Pointer root identifiers 可以不同，也可以指向同一 allocation 的不同 slices。
Checker 比较实际 affine syntax，并证明通过蕴含 maps 相同；不是由调用者
口头保证。它支持任意维、任意整数 affine coefficients/constant、稳定 scalar
参数及现有动态 tensor dimensions。非矩形 domain、不同 maps/relative-offset
templates 尚不属于此子集。模板不匹配时应保留原 scanner；这个 compiler
fallback 接入仍待实现。

## 一个 2×3 walk-through

令 A/B 的相同 access map 为 `i*16+j`。选原 pair
`a=(1,2), b=(0,1)`，坐标差为 `(1,1)`。它的 canonical pair 为
`c=(1,1), d=(0,0)`：每轴将正差放到 c，负差的绝对值放到 d。
两者都在原 2×3 source 域中。

在数学地址表示中，两组 offset 差都是 17 words：`18-1=17-0`。CompCert
的实际地址还包含各 pointer root 的 block 和 modular byte offset。
`canonical_alias_difference_exact` 证明两组地址 equality/inequality 判断相同，
包括同 block slices、不同 blocks 和 pointer offset wrap；runtime 不执行
跨 pointer 相减或排序。原 source 对 c/d 的真实读写提供有效且 aligned 的
地址许可，可复用已有 Clight pointer-equality 服务。

每轴 count=n 时，位置 q 遍历 `[0,max(0,2*n-1))`，表示差 `q-(n-1)`。
Canonical left/right 分别为 `max(0,差)`、`max(0,-差)`。因此 2×3 的数学
差值空间为 3×5=15，原 pair 空间为 36；8×8 为 15×15=225，对应原 4,096。
这些数字描述 spec 的枚举域，不是已经实测的 Clight/assembly 工作或收益。
重复 templates 仍会在每个位置执行其检查，单独去重尚未实现。

Count=0 的新 bound 为 0，仍是空域；rank=0 的域是一个 empty-coordinate
point。没有为差值位置引入一个 negative loop bound。Machine-int bound
计算及 canonical coordinate assignments 的安全求值仍需证明；不能把此处
Z 上的函数直接称为已编码的 runtime condition。

## 接口与已提供的证明

| 服务/端点 | 输入义务 | 框架实例提供的结论 |
| --- | --- | --- |
| `canonical_difference_points` | 非负 counts；position 在差值域 | 两个 canonical points 均在原域 |
| `canonical_difference_coverage` | 任意两个原域 points | 有差值域 position，canonical pair 与原 pair 的坐标差相同 |
| `canonical_affine_difference` | 两组参数向量各自等长，坐标差相同 | 相同 affine map 的输出坐标差相同；稳定 scalar tails 可相消 |
| `canonical_alias_templates_sound` | 静态 checker=true | 实际 template maps 相同 |
| `canonical_alias_difference_exact` | 同 maps、相同差、四个 actual locations 都有定义 | 两个实际 CompCert alias checks 结果相同 |
| `canonical_alias_check_exact` | 上述 checker；所有 source points/templates 可 resolve | compact Boolean spec 精确等于原 point-pair Boolean spec |
| `canonical_alias_source_receipts` | 现有 memory source-model execution；position 在差值域 | 两个 canonical points 的源许可可搬回 check-entry memory |
| `canonical_alias_source_exact` | 原 source-model execution、非负 counts、静态 eligibility | 不另要 resolve callback，直接导出 Boolean 精确性 |
| `canonical_alias_source_nonalias` | 原 source-model execution、layout/dimension view、eligibility、新 spec=true | 原来的 source-footprint restricted `locations_nonalias` |

模板严格相同是保守的 eligibility subset；在这个子集中，Boolean 结果精确
相同，接受域没有因为换 spec 而缩小。这个结论的定义性前提来自真实原源
许可；不推广到任意 locator 或 undefined source state。

两个新模块：

- [GuardMemoryCanonicalDifference.v](../adapters/compcert-memory/GuardMemoryCanonicalDifference.v)：
  坐标覆盖与 affine 差值。九个端点均闭合。
- [GuardMemoryCanonicalAlias.v](../adapters/compcert-memory/GuardMemoryCanonicalAlias.v)：
  静态 eligibility、Horner tensor index、实际 modular pointer offset/alias 对应，
  source permissions 和原 nonalias 前提。十一端点；其中八个闭合，三个
  source-model 端点使用既有四项 globals。

最后三个端点的 globals 为 `Classical_Prop.classic`、
`FunctionalExtensionality.functional_extensionality_dep`、
`ClassicalDedekindReals.sig_not_dec` 和 `sig_forall_dec`；均在冻结 compiler 的
42-global baseline 中。没有新增 Axiom/Parameter/Admitted。

## 原 source 的许可如何进入这个库

本库接受已证明的 memory source-model execution，不自行假设 loaded bounds
稳定。真实 loaded compiler 的既有 outer header guard 先证明 captured H/K
对应 source，内层 numeric/layout/box setup 再生产 model execution 和许可。
新 spec 可以消费该结果；不能在这些 guards 之前提前访问 child/arrays。
后续 factory 接入应运输同一个结果，并从 actual scan exit 接回原 candidate。

| 提供方 | 本阶段/下一阶段责任 |
| --- | --- |
| Domain 库 | 本阶段已生产 eligibility、coverage、actual alias Boolean 对应及接受→原 C_opt 的 nonalias 前提 |
| Clight 条件服务 | 下一阶段定义静态 scanner AST，证明 bound/coordinate machine arithmetic、逐点 comparison 的安全、完整 flag execution 和 private/public transport |
| Factory/优化实例 | 沿用原 loaded source/header/setup guarantee，自动 checked fresh typed resources；新 spec 接实际 guard exit、原 candidate 和 region guarantee |
| 语言 host | 沿用原源 progress、scope、placement、private declarations、normal boundary 和 Csem→Asm；本阶段未改变其 contract |
| Kernel | 继续组合局部 guarded 证书，不加入 affine 或 CompCert memory 语义 |
| 支持族源码用户 | 继续只给 marked C 和策略；无 hidden same-block 假设、execution/resolve callback 或局部证明 |

一般 affine source/scalar、完整 OLO 联合能力和作者负担保留在 active goal。
此服务不是最弱条件、一般 Presburger synthesize 或 arbitrary-language encoder。
它展示从常见子集的 domain 证明复用原 candidate 前提，接语言执行服务的接口。

## 验证、复核与下一步

独立 Rocq audit：20 endpoints、17 closed、最多 4 项既有 globals，670 个
可达 source/object/helper/output bindings。冻结 parent report 的 1,380 个
bindings 只核对 hash，不重跑历史审计；仅编译新模块和新 Audit.v。全部
失败尝试的 source snapshots/logs 保留在 `build/canonical-difference/source-build/`。

报告：`build/canonical-difference/proof-v1/report.json`，SHA-256
`7e43accd7f19017582233d03d5173ee7d1eeccffabb3123d2537297c732f9416`。

本 workspace 只读复核：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_canonical_alias.py --validate
```

新 helper `compile_canonical_alias_sources.py` 只编译缺失的新模块，并保留已有
成功 objects。新环境仍需要前阶段 CompCert/PolCert/loaded proof checkpoints。
本轮没有新 C/Asm execution、machine scanner、installed compiler 或 timing。

下一项是 actual Clight encoder，再接 memo factory/front end/extracted compiler；
不改原 C_opt/candidate/host。验收相同 accepted/refused/empty/context 矩阵和
完整 memory/public outputs，随后新 source/old/memo/canonical 配对完整成本。
若 eligibility 拒绝，复用原扫描；若运行 condition 拒绝，保留原 source fallback。
