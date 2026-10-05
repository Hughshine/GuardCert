# 带分支证据的只读前缀扫描

2026-10-05。本设施解决条件合成中的一种常见结构：一个检查建立当前点的访问依据，当前点的性质检查通过后才取得下一点的依据，活动前缀结束则直接接受。它不选择 source／candidate，也不解释整数、内存、alias 或循环语义。当前实际使用者是 indexed memory-bound 循环的参数稳定性检查。

## 使用者怎样接入

[ReadonlyPrefixScan.v](../prototype/interface/ReadonlyPrefixScan.v) 的 `readonly_prefix_spec H Cursor` 接受如下接口：

| 字段 | 使用者提交的内容 |
| --- | --- |
| `prefix_next` | 下一点的索引；索引可表示迭代、访问或运算位置 |
| `prefix_invariant`，记为 `W(c,s)` | 在入口状态 s 上，当前检查及推进证明所需的事实 |
| `prefix_active_probe`／`prefix_active` | 实际活动检查及其逻辑含义 |
| `prefix_activity_certificate` | 在 W 下检查安全、可完成、只读；true 建立活动，false 建立不活动 |
| `prefix_point_probe`／`prefix_point_property`，记为 Q | 实际当前点检查及其接受性质 |
| `prefix_point_certificate` | 在 W 且活动下安全、可完成、只读；接受建立 Q 和下一点的 W |

语言另提供常量检查、分支组合构造和实际执行／安全定律。`synthesize_prefix_scan A B SPEC fuel cursor` 生成：

```text
scan(0,c) = accept
scan(k+1,c) =
  if active_probe(c) then
    if point_probe(c) then scan(k,next(c)) else refuse
  else accept
```

`synthesized_prefix_scan_condition` 返回可直接交给 guarded rewrite 的 `readonly_condition`。它证明所有可达检查安全、检查有完成执行、真实出口仍是同一入口，并且接受蕴含递归的前缀性质。当前位置活动时，该性质要求 Q 及剩余扫描性质；当前位置不活动时没有后续义务。

fuel 用尽只说明这个有界前缀已检查。证明它覆盖变换所需的全部访问，仍需使用者提供上界／覆盖定理。结束检查还须有明确的不活动证据；非连续实例域中的一个空点不能自动被解释为后面全部为空。一般仿射域的枚举和覆盖也不是这个核心接口自动提供的。

W 是原入口上的逻辑断言，可包含存在性的源执行／权限 witness。运行时不计算 W，不执行源片段取得 witness；推进 W 是证明操作。cursor 决定被生成的检查位置，fuel 限制生成器的递归；这个原型没有引入动态 guard 循环。

## 拒绝不能当成否定

[ReadonlyBranching.v](../prototype/interface/ReadonlyBranching.v) 增加 `readonly_classifier H D T F probe`：安全、可用、状态不变分别有证明，两个结果各有 T／F 的语义证书。T 和 F 不必互为逻辑补集。

普通 `readonly_condition H D P probe` 只证明接受蕴含 P。`condition_classifier` 将它转换成 true 建立 P、false 只建立 True 的 classifier，明确不赋予拒绝负面含义。前缀扫描的活动检查单独提供 false 建立“不活动”的证书；当前点检查拒绝时直接回退，不依赖其否定。

`branch_readonly_conditions` 接受这个 classifier，以及分别在 `D and T`／`D and F` 上有证书的两个检查，生成按结果分派的检查并证明相同最终前提。它允许“false 分支成功”，而既有顺序阶段组合把第一次 false 固定解释为拒绝。这两种设施共同消费原有只读核；没有从任意 Rocq `Prop` 自动产生代码。

[ClightReadonlyBranching.v](../prototype/interface/ClightReadonlyBranching.v) 使用真实 `decision_bind` 实例化分支代数，并提供普通表达式 classifier 构造器。两个分支的证据必须由实际表达式求值证明；volatile、事件、故障和发散不能被“状态相同”掩盖。

## 实际循环怎样使用

[ClightIndexedPrefixScan.v](../prototype/interface/ClightIndexedPrefixScan.v) 为以下 source 建立 prefix spec：

```c
for (; i < (int)*bound; ++i)
  out[i] = (unsigned)i + 1U;
```

cursor 是数学点 k。活动检查是入口的 `k < (int)*bound`，点检查是实际 `out+k != bound`。W 包含：当前实际 source temps／memory、仍读取入口 bound 的证明、当前位置的真实剩余源执行，以及当前 word 权限可运输回原入口的证明。它没有包含后续点全部有效或整个 footprint 已分离的假设。

`indexed_prefix_point` 从当前实际活动源执行提取一个 store，获得该点的权限并在入口执行指针比较。只有比较通过，实际 store 的 load 不变性才能保持 bound 值，源剩余执行才能成为下一点的 W。实际 guard 全程在入口内存求值。alias 时源可以改变 bound 并提前结束，因此不能事先用入口 bound 假定全部后续地址都可访问。

[ClightIndexedBoundStagedGuard.v](../prototype/interface/ClightIndexedBoundStagedGuard.v) 先检查 `i==0` 与 `0<*bound<=cap`，从实际源执行导出 W(0)，再消费通用扫描证书。`indexed_prefix_scan_sound` 把递归前缀性质连接到循环全部活动 word 的分离要求。编译入口使用这份新组合证书，其局部稳定性／候选执行和完整 Csem→Asm 证明保持原契约。

`indexed_bound_generated_tree` 是编译规则实际调用的生成器，内部调用通用 `synthesize_prefix_scan`。`indexed_prefix_syntax` 和 `indexed_bound_generated_syntax` 机械证明新合成器生成的扫描及完整条件与原手写树相同，包括活动结束后的提前接受和 alias 后的拒绝。对应证书适用于实际调用语义与观察；构造时固定的宿主参数是被擦除的证明信息。因此这项迁移应保持生成代码；原生摘要回归用于核对提取／编译路径。

## 证据与边界

复现使用 `make interface-proof`、`make interface-clight-proof`、`make interface-compiler-proof` 和 `make interface-native-suite`。本阶段语言无关接口 49 个端点闭合证明；Clight 适配层 59 个端点不超过既有六项基线；完整编译层 209 个端点通过假设审计，没有新增全局公理。十五种提取配置全部重建并通过原生回归；相对 `2b5f26a` 的 23 份既有报告，源码／生成 Clight 摘要全部相同。indexed 上界独立／统一入口各保持 1079 次调用／2154 行输出，包含三元素数组中上界 8 改为 3 后安全回退的用例。

实际提取产物 `build/compcert-interface-indexed-bound/extraction/ReadonlyPrefixScan.ml` 的 spec 只保留 `prefix_next`、`prefix_active_probe`、`prefix_point_probe` 三个生成代码字段。`ClightIndexedPrefixScan.ml` 没有源执行、权限或 load-stability 查询；`ClightIndexedBoundStagedGuard.ml` 实际调用 `synthesize_prefix_scan`。这核对了本实现的证明信息擦除，仍沿用 Rocq 提取及 OCaml／工具链的既有信任边界。

这次设施提炼没有扩大 indexed 模板的接受域，也没有降低 O(cap) 比较成本或 17 个候选出口的代码复制。它复用已有只读条件和源执行证明，不能据此提出新颖性或性能结论。动态多维 memory-bound／stride、多个依赖 preload、一般无界／仿射检查，以及旧 affine／tiling 路线迁移，仍属于 [主线验收](optimistic-loop-acceptance.md) 的未完成工作。

## 两层实际扫描的组合

[动态内存上界矩形](clight-loaded-rectangle-case.md)又在实际提取入口中嵌套使用这个生成器：内层检查当前行的活动列，外层消费整行接受性质并推进真实源 tail。当前行完整访问来自源执行；未来行访问依据只在当前行 non-alias 后建立。核没有新增矩形、指针或 load 语义。动态尺寸的独立／统一编译入口各通过 6,248 次调用，完整编译接口现为 242 个端点，十六种配置全部重建回归通过。检查树会复制后续代码，实例已设置规模预算，尚需有证明的共享出口或廉价足迹检查。
