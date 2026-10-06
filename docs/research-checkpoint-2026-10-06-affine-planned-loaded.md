# 独立 bound pointer：顺序检查 plan、实际编译和运行

本阶段基于 `d43b929`，完成[上一阶段](research-checkpoint-2026-10-06-affine-dynamic-loaded.md)的 guard lowering、提取和独立 bound pointer 运行验收。再次 fetch 后，topdown 仍为 `7d94d810685a691efbf07df734f5fad8abfb4724`；本地 paper narrative 与远端正文字节一致。最小 kernel 不变，检查表示／处理是上层库，完整程序安装由 Clight host 提供。完整 goal 保持 active。

## 使用者怎样接入

源实例仍是二维 affine 内层循环、真实数组读写、每次外层测试重新读取的 signed memory bound。用户或不受信任工具选择源片段，提出 mapped／tiling／schedule 候选；checked source package 与原候选 checker 分别验证真实源／模型对应和域／依赖保持。bound 不必属于 body 的 pointer 列表。当前实例复用源已有的 public snapshot，不插入 private snapshot。

完整条件仍是 `preparation && bound_stability && candidate_guard`。它的安全性、全部实际源写足迹覆盖和接受后的 bound 保持，全部复用上一阶段的证明。此次改变的是条件的可执行表示：

```text
PlanDecision answer
PlanTest expression yes no
PlanAnd first second
```

`PlanAnd` 只在 first 接受后执行 second。`check_plan_tree` 把它解释成旧 decision tree，作为证明规格；`check_plan_code` 直接生成顺序 Clight，不经此展开函数。实际 lowering 使用一个 fresh private Boolean：每个完成的子 plan 都先写 result，外层短路和最终分派再读它。初始 result 可以未定义；表达式、源分支、候选分支和 public live 集合都不能使用它。内存完全不变，只有 private temp 被写。readonly 的逻辑条件与使用 private 状态的实际实现由语言证明连接。

这里不是要求新的优化作者重新证明一份完整变换正确性。作者已有的 `C_opt`、条件推导／编码和 source package 可继续使用；其额外接入工作是构造 plan 并证明其规格与已有条件对应。检查实现和分支运输由语言库提供。当前 affine 使用者已经实际消费这些接口。

| 责任 | 本次交付与实际消费 |
| --- | --- |
| 最小 semantic kernel | 没有修改；既有局部条件／候选组合证明继续使用 |
| Clight 检查实现库 | [ClightCheckPlan](../prototype/interface/ClightCheckPlan.v)：plan/tree 精确运行对应、实际顺序代码执行、初始化和 private writes；[ClightCheckPlanFrame](../prototype/interface/ClightCheckPlanFrame.v)：资源反射检查、分支执行运输、精确 memory 和公开 temp frame |
| Domain／优化接入 | [ClightAffineLoadedCheckPlan](../prototype/interface/ClightAffineLoadedCheckPlan.v)：实际逐行／逐点 plan，规格等于原完整 guard；[ClightAffinePlannedLoadedRewrite](../prototype/interface/ClightAffinePlannedLoadedRewrite.v)：复用旧 condition 和 candidate theorem，不重证它们 |
| 候选／位置证据 | [ClightAffinePlannedLoadedCandidates](../prototype/interface/ClightAffinePlannedLoadedCandidates.v)：复用实际 source matcher 和三类 checker；reserve pool 的第一个 temp 为 Boolean，剩余 temps 用于候选 counters；freshness／frameability 失败时静态拒绝 |
| Clight host／backend | [ClightGuardedAffinePlannedLoadedCompiler](../prototype/interface/ClightGuardedAffinePlannedLoadedCompiler.v)：复用原 source progress、private pool、sequence/table 安装和 CompCert backend，取得新 Csem→Asm backward simulation |

`check_plan_guarded_normal_execution` 运输已完成的正常、无事件分支执行，保存全部最终 memory 和所选 live temps。反射 checker 接受 structured skip／assign／set／if／sequence／loop／break／continue，拒绝 calls、labels、return、switch。这不是一般发散或任意控制出口的新语言协议。源完成域 D 不预置未来 bound 稳定性；语言 progress 仍独立于 bound 保持。原 prefix receipts、quiet suffix 和保守的全部源 temps live 集合保持。

## 检查规模和默认 cap

同一个 column cap=3、每点一个写探针的 fixture：原 tree 在 outer fuel=1／2／3 时有 7／35／147 个测试；新实际 Clight code 有 11／22／33 个 if，fuel=64 时有 704 个 if。第三行和 64 行只统计 syntax，该小 package 的 row cap 是 2，不能当作其执行 coverage。

逐行／逐点的 continuation 现在只出现一次，稳定性 plan 的 AST 随 row×column cap 增长；仍是按 cap 展开的检查，尚未生成运行时嵌套 scan loops。计数不证明运行成本下降，也不保证检查对任意输入规模都适合。

真实 C 另验证了匹配驱动默认值的 64×64 caps：候选确实安装、机器探针确实走重排路径，整个函数的 Clight AST 有 12,518 个 if（含其他 guard／candidate／fallback），pretty-printed 函数为 6,064,194 字节。文本还包含深层缩进，不能将其当作 AST 节点数或最终机器大小。此配置仍有明显的展开代码成本；guard 循环化／符号足迹优化和独立 P4 测量继续必要。

初次将 column cap 误设为 128，该源在默认 extent=8192 下被 source checker 拒绝，没有安装。驱动实际默认是 64×64；纠正后通过上述验收。没有把拒绝当作能处理 64×128 的运行结果。

## 完整 C 运行和机器路径

[源 fixture](../examples/native_affine_planned_loaded.c)保留实际 prefix loads、公开 i／j／k／snapshot、suffix stores 和 caller context。独立 Python 模型与 GCC 原程序先核对完整输出，再与新 compiler 的机器程序比较。

六个新编译配置：mapped、schedule、2×3 tiling、4×1 tiling、默认 cap 的 mapped，以及错误域候选。每个运行 37 个输入，共 222 次配置内调用。覆盖零次循环、负 bound、非零 start、cap 超出、不同 blocks 的 bound、同 block 不同 offset、第一／第二行写中 bound、真实 body alias 和不同 body base。错误域候选没有安装，仍完成原程序。全部数组、公开出口、retained load 和 caller prefix／suffix 一致。

十三个 GDB 探针绑定到本次二进制：

| 情形 | 实际 guard／程序行为 |
| --- | --- |
| bound 位于独立 block | 检查源顺序的六个实际写点；mapped 写入 `p[32], p[160], p[97]`，确认候选重排 |
| bound 是同 block 的 `p[31]` | 同样接受，不能简化为 bound 与数组 base 不同 |
| bound 是 `p[32]` | guard 只比较 `[32]`，回到 loaded 源；写 bound=-1 后公开出口为 i=j=k=1 |
| bound 是 `p[97]` | guard 比较 `[32,96,97]` 后停止，回到 loaded 源；写 bound=-1 后公开出口为 i=j=k=2 |
| 小数组只有 33 个写单元 | 只有第一行的实际写 cell 合法；guard 比较 `[32]` 后拒绝，后续 row 比较指令没有执行；公开出口和完整小数组均一致 |
| shifted body alias | 保留源写顺序 `p[32], p[97], p[160]` 和正确值；不执行有依赖的重排 |
| preparation cap 拒绝 | 不执行任何 bound 地址比较，保留源执行 |
| schedule、4×1 tiling、默认 caps | 分别观察到重排写顺序；另核对 tiling 的 bound 拒绝和错误候选的原执行 |

guard 比较探针从实际反汇编定位全部十个 bound-comparison sites，核对 cell／机器寄存器地址及到达顺序，不只观察最后结果。其记录仅针对 mapped、cap=4 的当前 x86-64 ABI／寄存器模式；其他配置的探针核对分支写入顺序和公开出口，不能把该探针脚本宣称成可移植语言证明。

当前 body alias 快捷条件仍保守要求相同 base 加逻辑 offset 分离。最初用两个独立 body 数组时，输出一致但候选没有运行；改成满足该已有条件的 body 后确认接受。额外保留了不同 body base 的原执行探针。新增 bound 检查支持不同 blocks，不等于一般不同 body base 的 alias 检查已经完成。2×3 tiling 有真实安装和完整输出证据；用来区分重排路径的 tiling 探针是 4×1。

## 审计和复现

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make affine-planned-loaded-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make affine-planned-loaded-native
python3 scripts/validate_affine_planned_loaded.py
```

native 验收包含 GDB ptrace；本阶段在允许 ptrace 的执行环境运行。编译器在独立 `build/affine-planned-loaded/compiler` 中构建，提取根入口是 `ClightGuardedAffinePlannedLoadedCompiler.compile_guarded_affine_planned_loaded`。builder 核对提取代码未包含递归 `check_plan_tree`；不是运行时先构造大 tree 再重新压缩。

证明审计通过 119 个端点，其中 33 个语言端点；587 个选定依赖、931 份 source 摘要。新文件全部实际编译，本阶段是增量闭包核对，未清理重编整个 587 文件闭包。readonly prefix library 无全局假设；端点无新增全局公理，四个 compiler theorems 均继承原 42 项基线。proof audit 仅证明与核对 `.v`／`.vo`，其 native/extraction 字段不是运行验收；后两者见单独 builder/native/validation 报告。

| 产物 | SHA-256 |
| --- | --- |
| `build/affine-planned-loaded/proof/report.json` | `cf27379da4980a96eb24b93fc90810a3df4a612cbb37fa3c2c48026dd0936f5c` |
| `build/affine-planned-loaded/compiler/.guard-build.json` | `df8764a46a21a3195797ee3a6de4eb97cd3da14b968f630a9e3624c41bc483cd` |
| `build/affine-planned-loaded/native/report.json` | `3395916e9ab61f0d43fde2e6a4b22160ac7df5ad78da0f90350754af31ad316c` |
| `build/affine-planned-loaded/validation.json` | `c380d09c7cc1748cb3384a13daaef2ed9d173fdd51cb55e9fb3b48a894fab1c5` |

旧 loaded/cached 两套 validator 重新核对 source／objects／compiler-stamp 通过，旧 1,650／891 调用矩阵未重执行。其结果不计入此次独立 bound 的 222 调用。

## 下一阶段

本次关闭独立 bound 的实际运行缺口。下一项优先是在原源没有 public snapshot 时插入 fresh private bound snapshot：必须由到达的原 header 推出该读取安全，保存 original-entry 事实并证明 private/public 运输，失败仍用真正 loaded 源；不能将任意 body pointer 的 preload 当作安全。多个依赖读取需要各自的合法顺序、可用性和 stores 稳定性证据。

并行维护的验收是 guard scan 循环化／符号足迹、一般深层 affine 源、不同 body base 的物理 alias、P4 性能和同例 related-work／作者证明负担比较。没有用此次端点数、文件数、AST 计数或运行成功作为 novelty、盈利性或总 proof burden 下降的证据。
