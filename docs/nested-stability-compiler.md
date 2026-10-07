# 同值稳定性条件：复用候选与 host 的完整编译路径

2026-10-07，接续 [same-word model producer](nested-word-model.md)。本阶段将该
条件装进实际 physical guard、multi-array adapter、typed factory 和独立提取入口。
旧 nested frontend 编译器、源码矩阵与报告保留。最小 kernel 未改。

## 使用者如何使用

实际 source 仍由既有 `ncs_frontend_proposer` 描述，候选仍由既有
`affine_candidate_proposer` 提出。两者只提供编译时数据：source shape、参数、
私有名字、affine package、candidate 和 validation evidence。Factory 检查实际
AST、pool 分配、package 和候选；没有让使用者填入 source/model 对应或
guard-correctness 语义回调。

新增入口
[compile_ncs_stability_regions](../prototype/interface/ClightGuardedNestedStabilityCompiler.v)
使用相同 descriptor／candidate 格式。Domain 自动从 BODY 提议第一个 literal
store 的 word，再由 `check_constant_word_statement` 检查全部 typed BODY。提议
不构成证据：不同常量的 stores、未支持语法均不能取得 same-word 资格。
无法分类的 BODY 使用原完整 stability guard，具有 AST 相等的 fixture。

例如原 C：

```c
for (; row < shape[0] + 1; row++)
  for (column = 0; column < shape[1] + 1; column++)
    for (component = 0; component < 5; component++)
      a[80 * row + 5 * column + component] = 1;
```

在实际源许可的双 capture、row／positive／numeric gates 和 helper 初始化后：

```text
if root_cache == Int.add(w, root_delta)
   && child_cache == Int.add(w, child_delta):
    stability_result := true
else:
    原 stability scan
if stability_result:
    原 candidate dependency/alias check
if 完整 check 接受:
    candidate
else:
    原 C 对应的 source AST
```

例中 `w=1`、两个 delta 都为 1，因此比较的是 computed caches 是否等于 2。
若 `shape[0]=shape[1]=1`，BODY 即使覆盖 header 单元，也只写回同值；保持
来自实际 store 的 value guarantee，不来自 non-alias。不同 raw word 使短条件
不成立时，仍有机会通过原 scan；原 scan 拒绝时执行真正原源。

## 证明责任及最困难的连接

三方责任和四条逻辑链仍按 [narrative](topdown/paper-narrative.md) 区分：

| 归属／环节 | 本次交付与复用 |
|---|---|
| 语言服务 | 已有 Mint32 同值 store 保持、typed BODY/control checker、安全缓存比较、private/public frame 和源 execution transport |
| Domain `C_derive` | 新 word proposal 的静态检查；实际 BODY 保持双 header；由 cache equality 的 modular cancellation 得到 raw words 相等；沿 cached/canonical bridge 交付模型 |
| `C_guard` | 新 actual physical guard receipt；短条件失败保持扫描入口完全不变；接受交付 canonical execution 及实际 check-exit ports frame；随后复用 alias-only check |
| 优化方 `C_opt` | 原 candidate proposer／verified validator／Clight lowering 与 `ncs_multi_local_certificate` 直接复用，没有复制候选正确性证明 |
| Kernel | 原 `guardify_preservation` 消费新 guard certificate 与原 preservation certificate；未增加语法、alias 或 schedule 知识 |
| 语言 `C_host` 与整程序安装 | 已有 materialized guarded choice、frontend source transport、projected region contract、expression region host、fresh pool 与 CompCert backend 复用；新 entry 的 Csem→Asm theorem 单独证明 |

关键困难不是两个比较的 Boolean 计算，而是比较结果必须建立实际模型合法性：
同值 memory guarantee 不能自动提供 pointer-binding frame、读取许可、源码
progress 或 source/model 对应。新 producer 消费原 checked site、capture／numeric
receipts，实际生产完整 subloop 的观察保持，再取得原公开出口对应的 canonical
execution。该模型的私有入口可能与实际 guard exit 不同；adapter 明确证明 ports
frame，并将 execution 运输到 alias check 的真实入口。

检查安全的局部证明域仍是原源 silent normal completion。语言 region host 另行
提供实际原 AST 的 progress／控制／placement 合同；不能把上述有限执行 lemma
单独称作任意上下文正确性。完整 compiler theorem 是成功编译结果的
`Csem.semantics` 到 `Asm.semantics` backward simulation。

## 验证范围与测量

独立 proof audit 编译 597 required dependencies，绑定 896 source digests，查询
19 endpoints。Kernel 闭合；compiler 沿独立查询的既有 42-global baseline，零
新增 global axiom。新 compiler 已提取、OCaml 构建并执行。

新矩阵使用既有七函数的 119 输入，再加八个 constant-store 输入。六配置共
762 full assembly calls，逐次核对 A 的 6,144 words、B／C 各 2,048 words、双
headers、三个公开 counters 和前后 markers。三配置另有 381 instrumented Clight
dispatch calls。错误候选、依赖冲突、条件未满足、未定义 BODY inputs、两次
rewrite 及 surrounding return 等旧路径仍被覆盖。

旧 binary 的 SHA 与既有 stamp 核对后，在同一新 C source 上另执行 127 assembly
calls 和 127 Clight dispatch calls。Interchange 的 old/new fast dispatch 为
49→51，runtime refusal 为 77→75；新增两个 header/data 同值 alias 输入，没有
丢失既有接受。这是矩阵内的接受对照，不是任意输入全集的覆盖计数。

四个 GDB probes 观察未修改汇编，两个 header layouts 分别为 `shape=a` 和
`shape=a+5`。禁用优化的 watched writes 为 `4,9,80`，interchange 为 `4,80,9`，
写入值都为 1，公开出口都为 `(2,2,5)`。Watch cells 避开原本即为 1 的 header，
使 write watchpoints 能观测实际值变化。此小域的 2×3 tiling 不改变这组三点
写序；其接受由独立 Clight dispatch 核对，不借该 probe 声称区分 tiling 路径。

另有 old/new 各十次 instrumented Clight 检查工作量对照：

| 输入：raw root/child，header layout | 旧 header 地址比较 | 新 header 地址比较 | 新 cache equality |
|---|---:|---:|---:|
| 1／1，独立 header | 40 | 0 | 2 |
| 1／1，shape=a | 10 | 0 | 2 |
| 1／1，shape=a+5 | 20 | 0 | 2 |
| 2／1，独立 header | 60 | 60 | 1 |
| 2／2，独立 header | 90 | 90 | 1 |

旧 scan 在完整五次 store BODY 的 probes 之后检查拒绝，故 alias 时仍比较
10／20 次；不是每个 point 或第一项 comparison 失败后立刻停止。诊断插桩由 GCC
执行，不作为新增 verified pass，也不是 assembly 指令计数或完整 guard work。
仍有 numeric／capture／alias 等其他工作，没有计时或 profitability 结论。
新代码包含两份备用 scan AST；同源 interchange 函数从 613 增至 762 bytes。
代码大小也须单列，不能以比较数下降推导代码缩小。

## 重现与后续验收

已安装 pinned toolchain 与恢复的依赖下：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/nested_stability.mk native
python3 scripts/probe_nested_stability.py
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/nested_stability.mk validate
```

独立 makefile 保持前阶段 source-only reproduction 的根 Makefile 摘要不变。
Probes 需要 GDB ptrace 权限；不修改目标 assembly。报告各自绑定 sources、
compiler、helpers 和 artifacts，旧报告不作为新 proof audit 输入。旧 binary 仅为
运行对照产物；该对照不声称重新提取旧 compiler。报告摘要见本次 checkpoint。

按 narrative 的三个 guard 维度，本阶段已有一条紧凑稳定性充分条件、矩阵接受
对照和局部检查工作量；完整 guard／program timing、一般投影或范围／footprint
条件、代码 factoring、作者责任与手工工作量对照仍待完成。源范围仍是既有固定
layout 三轴 frontend；其他 affine source classes、动态布局／delinearization 和
完整 BT 的适配仍待继续，完整多面体目标保持 active。
