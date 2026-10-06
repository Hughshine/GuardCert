# 非矩形 pointer 使用者：从候选提案到完整程序

2026-10-06。沿 [topdown narrative](topdown/paper-narrative.md)，本实例把真实 affine-inner pointer 源、独立候选证书、运行时条件和 CompCert 宿主接入同一编译入口。框架不发现优化假设；源域、足迹、条件推导和候选对应由这个 domain 使用者实现。完整研究 goal 继续 active。

## 使用者提供什么

[ClightAffineInnerPointerCandidates](../prototype/interface/ClightAffineInnerPointerCandidates.v) 暴露两个不受信任回调：

| 回调 | 输入／输出 | 谁验证 |
| --- | --- | --- |
| `affine_inner_pointer_profiler` | 真实源 statement → row/column caps、header/body 参数 caps、pointer 列表、window | `describe_affine_inner_pointer_at` 核对实际 AST、用途、freshness、地址编码和范围 |
| `affine_inner_pointer_proposer` | checked source 的真实 Loop、context、instructions、geometry caps 和 width 编码 → candidate Loop 或 schedules、坐标映射、两套 ranges | 原 mapped-domain／dependence checker；实际 Clight candidate lowerer；运行时分别检查 validator 和 encoder ranges |

两个回调都可以保守返回 `None`。profile 的 cap 是一项待检查的限制，不能作为所有输入天然满足的事实。源选择、候选搜索和盈利性仍由使用者决定。实际 compiler 检查失败时保留原源；动态条件 false 时也执行完整原循环。

`affine_inner_pointer_request_of` 提供实际 `memory_affine_inner_pointer_region_model`，没有以矩形替代非矩形源。request 的 context 包含源 header/body 几何和 RHS 标量；后者允许负数。候选提案携带 `MemoryNested.A.interval` 和 `MemoryFramedNested.N.A.interval` 两种范围，分别绑定数学验证器和机器编码器。两种表示目前分开检查，不能因为字段名称相近就假定已经相互推出。

## 一个完整 walkthrough

源 C 的核心为：

```c
rp = *p; rq = *q;
for (; i < n; ++i) {
  k = i + 1;
  for (j = 0; j < k; ++j)
    p[32 + 64*i + j] = q[4096 + 64*i + j] + a;
}
```

1. 使用者提出 row/column cap 64、window 8192。源 checker 从实际 Clight AST 取得 `k=i+1` 和真实读写，不接受替代的增量或不完整 pointer registry。`propose_affine_inner_pointer_profile` 是便利提案生成器，返回结果仍须经过 checker。
2. 优化方提出列优先候选：`0<=j<n`、`j<=i<n`，指令参数仍为源 `[i;j;n;a]`，附坐标 swap witness。`check_affine_inner_pointer_model` 核对实际源／目标域、指令、参数、访问和依赖，得到 `C_opt`。guard 本身不能使不合法候选成立。
3. domain 库复用源推导的 header/first-body word 证据、所有行的宽度、实际 ragged footprint 和 affine 包络。入口条件建立源／候选对应需要的范围和物理 non-alias，这是 `C_derive`。
4. `affine_inner_pointer_candidate_guard_condition` 先检查源 header、参数、width，再比较有源 receipt 的 pointer 和包络，最后检查两套 candidate ranges。它证明 reachable tests 安全、检查可完成且只读，以及接受 sound，这是 `C_guard`。n<=0 提前回退；a 的负值不因类型证据被排除。
5. `affine_inner_pointer_candidate_execution` 消费独立候选证书和接受事实，得到真实候选／restore 的执行：**完整最终内存相同，公开 temps 一致**。例如初始 j/k 为 77/91 时，空路径保留原出口；非空候选恢复源最后 i/j/k。
6. retained source prefix 提供 raw-base 比较许可。`affine_inner_pointer_observed_candidate_contract` 与实际 normalized source/suffix 的运输服务建立 local contract。原 `sequence_progress_supported` 在具体 affine-inner fixture 上返回 true；私有寄存器和 source placement 由已有语言 host 核对。
7. [compile_affine_inner_pointer_correct](../prototype/interface/ClightAffineInnerPointerCompiler.v) 对成功编译给出 `Csem.semantics source` 到 `Asm.semantics target` 的 backward simulation。它量化两个 proposer，并消费真实检查结果；不是一个只包装预先证明常量候选的入口。

这条 local contract 的参数类型证据使用有限正常源完成和实际 prefix receipt。全程序保证来自另行消费的 Clight source progress、scope/freshness 和小步 host 定理，不能从该 big-step 条件单独推出。受限源内部没有 call、return、goto；普通外围程序上下文由宿主处理。

## 三方和四张证书

| 责任 | 本阶段工作 | 可复用／仍需提供 |
| --- | --- | --- |
| kernel | 未改；readonly condition sequencing 组合安全域及接受事实 | 不解释 pointers、affine 域、调度或 CompCert AST |
| 语言／IR | 复用只读分派、prefix receipt、typed/range 原语、完整内存／temp 运输、sequence contracts/progress、private pool 和 CompCert backend | 同一 host 安装新 table，不重新证明程序上下文；新源控制形状必须通过其 checker |
| optimizer/domain | 绑定同一 package 的完整 context、width-model、两套 candidate ranges、独立 `C_opt`、实际 lowering/restore、normalized source checker 和 compiler factory | 源域/访问/前提的对应继续由实例承担；提案生成和盈利性不可信 |

`C_opt` 由原 checker 产生；`C_derive` 由源/footprint/范围库产生；`C_guard` 由机器原语、实例 D 和 kernel sequencing 组合；`C_host` 由实际 readonly 分派、source-prefix contract、进展／作用域／私有资源和程序 simulation 建立。源/候选 correspondence 与 public exit restore 属于 domain 对该语言服务的使用，不能标作核自动提供。

一次 pass 的多个 table entries 使用同一安装定理。任意有限次证书化 rewrite 的组合是原框架已有能力；本阶段没有新增无限优化搜索的终止保证，也未把多次函数调用当作重复 rewrite 的证明。

## 实际 schedule generation 的表示问题

生成器直接输出的参数检查可能包含数学常量 `2147483648`，或者 `-a`；这些不一定能安全编码成 Clight signed32 操作。`j<2*i+1` 的列优先下界还可能带 `(j+1)/2`，原 affine extractor 不直接接受这种候选边界。

`propose_affine_inner_candidate_normalization` 是 **不受信任的候选整理器**：提出删除只依赖入口参数的生成检查，使用已有 interval 分析给除法边界提供一个覆盖范围，把真实上下界转为经 division clearing 的 affine body 条件。整理后的整个 candidate 重新通过原域／依赖 checker，再进行实际机器 lowering。checker 不接受则源保留。它没有一个可绕过 checker 的 normalization-correct 公理，也不等于框架提供了通用最弱条件或最优 residualization。

这条路径已经实际生成并核对三角域 `j<i+1` 和另一个域 `j<2*i+1` 的列优先候选。后者的粗范围循环可能执行额外控制迭代，guard 外没有额外数组读取；性能没有测量。直接提交原始 ceiling-bound candidate 仍被拒绝，这个边界作为独立配置保留。

## 运行与边界

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make affine-pointer-compiler-native
```

机器路径探针需要运行环境允许 GDB `ptrace`。入口、提取、六个原生配置、完整 buffer/public state 与五个 linked-machine 探针的证据见 [阶段记录](research-checkpoint-2026-10-06-affine-pointer-compiler.md)。本入口采用 direct readonly tree；符号条件不接受就回原源，没有新 ragged pointer scan 或 shared lowering。

源支持两层 register-valued affine-inner 上界、源 checker 支持的 affine 地址和 scalar integer body。一般深层 affine 域、该 pointer package 的 quotient/tiling 证书、多个有依赖 preload，以及条件读取与参数稳定性仍是后继目标。当前实例没有取得通用 Presburger projection、收益测量或与近邻的同例作者证明负担结果。
