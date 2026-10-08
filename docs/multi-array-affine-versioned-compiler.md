# 多数组 affine：实际检查出口、数据接口与整程序定理

日期：2026-10-08。前置为 `77e32f1` 的
[actual affine scan](multi-array-affine-access-scan.md)。本阶段关闭同一泛化扫描的
actual-exit／candidate／restore／fallback 连接，生产局部 region guarantee，并接
selected Clight host 和新的 Csem→Asm 定理。新族的真实 C 驱动和机器运行仍需验收。

## 使用方式

优化实现者给出两种不受信任的数据提案函数：

```text
describe : Clight.statement -> option multi_tensor_region_description
propose  : list Loop.instr -> option tensor_generated_candidate
```

Description 包含 dimensions、稳定 scalar identifiers、assignment/access/value
metadata、cap 和静态 profile。Factory 核对实际源 AST，不信任描述中的对应关系。
Candidate 含实际生成的 Loop 和 mapped/tiling witnesses；既有完整候选 checker
核对源／候选模型及依赖，并将接受的实际 Loop 降低为 Clight。

使用者调用：

```text
check_multi_tensor_affine_region live typed_pool describe propose source
    -> imp (option Clight.statement)

compile_selected_multi_tensor_affine_regions
    chosen_labels describe propose private_count Csyntax_program
    -> imp (res Asm.program)
```

资源 allocator 先选两个 source-rank cursor vectors 和 Boolean flag，再从剩余
typed pool 配对 candidate counter／bound slots。当前配对服务要求剩余 slots
可成对且均为 int32；资源不合要求会静态拒绝。整程序入口用规范化程序的
`program_temps` 自动计算 live，并生成 fresh declarations。源码使用者不提供
NonAlias、setup、source/model 或 simulation callback。

这里的 `describe`／`propose` 是优化实现者的接口。最终 C 用户的目标接口仍是
标注 C 与 phase／tile 选项；本阶段尚未将这个新族连接到该 C 驱动。外部候选
和手写 Loop 可以测试接口，不能代替真实 polyhedral pipeline 的主工作流。

## 实际完整语句

生成的语句依次执行：

```text
safe numeric/layout/box/profile setup
  refused  -> original source AST
  accepted -> initialize private flag and run affine point-pair scan
                refused  -> original source AST
                accepted -> checked candidate; public iterator restoration
```

Setup 只读公开状态。Scan 只更新自己的私有 temporaries，不写 memory，也不
读取数组元素的值；地址比较的许可来自原源的实际执行。其 AST 在编译时固定，
runtime counts、scalars、dimensions 和 pointer bindings 决定实际遍历与地址。

扫描改变私有状态，因此候选不能套用检查入口的执行定理。新 exit 服务运输
source/bound/scalar/dimension bindings，以及 actual footprint 上的 restricted
locator separation。它只要求相应公开 temps 一致，不要求整个 temp environment
或无关 registry entries 相等。随后用原候选证明构造实际 checked-exit 执行，
恢复 source iterators，并保持原 final memory 和任意请求的 caller-live 观察。
Alias refusal 也从同一实际出口执行原 AST。

## 提供的证明

`multi_tensor_affine_package_full_execution` 从任意实际原源的正常完成执行与
候选 checker 接受，导出完整 versioned statement 的正常完成执行、相同 final
memory 和 caller-live temp agreement。它没有要求入口 numeric/layout/box
或 NonAlias 已成立；这些动态义务由完整检查的接受分支生产。

`check_multi_tensor_affine_package_full_contract` 将该执行证明转换为已有
`PrivateRegion.projected_region_contract`。语言的 big-step→small-step bridge
给出同一 continuation 的目标执行；原源的 public scope 和进展仍是 host 的责任。

`compile_selected_multi_tensor_affine_regions_correct` 对任何描述／候选提案函数、
private count、原 Csyntax program 和成功输出 Asm program，证明
`backward_simulation (Csem.semantics source) (Asm.semantics target)`。
证明组合 SimplExpr、SimplLocals、selected host 与 CompCert verified backend。
该定理允许静态拒绝所有区域，因此必须另验实际 native frontend 和安装成功。

Selected host 重用现有 occurrence-sensitive label traversal、projected region
simulation 与 table selector，只采用 source factory 同一份
`structured_progress_supported`。它核对 private pool、源进展和 target label-free
要求；不标注的相同 AST occurrence 不会因此被选择。没有修改既有 host contract
或增加通用 contextual-closure 公理。

## 三方责任与困难位置

| 责任方 | 本阶段实际承担的内容 |
| --- | --- |
| Framework kernel | 既有局部 guarded correctness 与证书组合接口保持；不识别 C、pointer 或 polyhedral schedule |
| Clight language/host | temp/frame 与受限 locator 运输、原 AST 出口执行、small-step bridge、源 progress、fresh typed declarations、selected placement、完整程序 simulation 与 backend 连接 |
| Domain/optimizer | checked actual source package、setup 推导、访问 footprint 与 scan 接受充分性、候选模型／依赖 checker、restore 连接、数据 producer 与局部 guarantee |

语言 host 接受的是优化实例产出的局部保证；不能把其整程序定理描述成 generic
kernel 自带任意 context lifting。也不能把数据提案函数对成功输出的正确性
量化，描述成通用 assumption extraction 或最低成本 guard synthesis。

独立审计查询五个新模块的 20 个端点：8 个闭合，完整 compiler 仍为旧 42 项
globals，零新增公理；183 个文件绑定加已验证 parent closure。报告为
[proof/report.json](../build/multi-tensor-affine-versioned/proof/report.json)，SHA-256
`5e599ede01148f0c6718aa4dd5b50d198b05f2b7a52624cfa06ef7d2a001ce79`。
旧成功模块、proof objects 和报告保持，失败编译日志也保留。

提取后的 full factory 已运行九项检查：identity 与三种真实 Pluto／per-statement
prepared-codegen proposal 接受；依赖反转、缺失 candidate store、耗尽 scan pool
和错误 source description 拒绝；另核对同一实际 source 的两个 marked sites
安装完整目标、一个 identical unmarked site 保留。三种 tile mask 为 `[2,3,2]`、
`[1,3,2]`、`[1,1,1]`，均沿真实模型提取、affine／tiling 验证与生成代码路线，
再由新 full factory 重检完整 candidate。

[extracted-factory-v2/report.json](../build/multi-tensor-affine-versioned/extracted-factory-v2/report.json)
绑定 1,200 个文件，SHA-256
`2a5e8d1220495ad2daf50f829874a5ccec379705a914a9a4ddf846e2544971a3`。
Source AST／普通 metadata 来自已有独立 renamed 两-store fixture，候选由真实
pipeline 生成；Main 不要求手写 pipeline target。原模型、转换模型、逐 statement
codegen、完整 generated candidate 与 validator 结果保留在三个独立 phase directories。
Identity／dependence-reversal fixtures 仍作为 checker regression 单独记录。

这是提取后的 checker／full statement producer 和 selected statement host 的
执行；没有执行 emitted Clight guard/candidate、完整 C 编译器或 Asm，不声称
runtime 接受／回退已实测。首次 harness 的 OCaml constructor syntax 错误在
`extracted-factory-v1` 保留，成功后继在 v2，旧 proof objects 没有重建。

## Narrative 核对与下一验收

本次 fetch 的 `origin/topdown/research-positioning` 为
`12419c1e1e3da450bf378742a2fb4e204e51e060`；
[paper narrative](topdown/paper-narrative.md) 和
[context lifting](topdown/context-lifting.md) 与 main 正文一致，没有新的未同步差异。
其 kernel cutoff、三方责任与真实 annotated pipeline 指令继续约束计划。

下一项直接接同族 marked C frontend、自动 source metadata、真实 scheduler／
codegen、当前 full factory 与 selected compiler，验收未标注 exclusion、多 site、
static refusal、runtime setup／alias fallback、公开出口和 continuation。提取
factory 或证明整程序定理都不能单独替代这个运行链。

随后将两次 store 的 loaded 原源逐条推进接到同一族：原到达前缀许可下一
header／point，并证明 stores 保持所有已捕获观察后再推进。不能从尚待证明的
完整 cached rectangle 执行许可自身检查。Coordinate-only scalars 的可观察性
gate、一般 affine domain／recurrence、紧凑充分条件、实际检查成本与 OLO benchmark
可用性继续在完整 active goal；不为接口形式先重构 kernel 或 host clause algebra。
