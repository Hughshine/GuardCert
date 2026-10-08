# Conditional loaded affine：实际 C、紧凑分派与完整程序验收

2026-10-08，接续 [checked source factory](affine-snapshot-installation.md)。
原 `i<*N; K=i+*M` 现在通过提取编译器进入真实 Pluto／prepared codegen、
完整候选检查和既有 selected CompCert 安装。顺序 check plan 使用两个
私有缓存与一个 Boolean，保持原 condition 规格和 source/model/candidate
证明。六配置通过 1,584 Asm／1,584 Clight 全输出与公开 continuation；
同一 binary 的 word 400／400、recursive affine 480／480、旧 private-loaded
270／270 回归通过。完整目标保持 active，接受域和收益边界见下文。

## 实际源与变换

两个标注函数分别使用 `K=i+*M` 和 `K=2*i+*M`，第三个函数不标注。
它们的原代码包含 `rq=*q; rp=*p`、真实数组读写和如下 loop：

```c
for (; i < *N; ++i) {
  K = i + *M;                 /* 另一函数用 2*i + *M */
  for (j = 0; j < K; ++j)
    p[32 + 64*i + j] = q[4096 + 64*i + j] + a;
}
```

源 C 没有手写 N/M cache、guard、证明 callback 或 surrogate rectangle。
Original loaded source 是安装 key；已证 normalization 处理实际 frontend
grouping。Factory 自动描述其缓存 affine model，并交付 grammar/shape/
protected-port/freshness 证据。实际 target 顺序执行：

```text
保留原 rq/rp 读取
Ncache := *N
原首次 outer 比较 active 时才 Mcache := *M
顺序 numeric preparation / N-M stability / nonalias / candidate ranges
Boolean true：运行已检查实际 candidate，恢复公开 i/j/K
Boolean false：运行原 repeated-load loop
保留原 suffix、公开记录及真实 memory continuation
```

Capture 与 Boolean 改变私有 temps；memory/public/trace/control 由语言
transport 定律保持。Readonly condition 描述捕获后的逻辑 check entry，
实际 check-plan lowering 另证明 private-state transport，不能把它称为
保持完整 entry state 的 readonly statement。条件拒绝不推出前提的否定。

## Source/model 证明方向与前提来源

按 narrative `c4b1395` 的澄清，当前安装路径有以下具体证明链。表中的
execution transport 都保留各自前提与方向，不称为独立双向 equivalence。

| 桥或契约 | 实际定理与边界 |
| --- | --- |
| 原 repeated-load source → 安全 capture 后的原 source | [ClightAffineSnapshotSourceInputs.v](../prototype/interface/ClightAffineSnapshotSourceInputs.v) 的 `affine_snapshot_capture_source_inputs` 从给定原完成执行得到实际 capture 执行、root/conditional-child receipts 和公开状态关系；没有先执行一次 source 的 runtime 步骤。 |
| 原 loaded source → stable cached source | [ClightAffineSnapshotCandidateExecution.v](../prototype/interface/ClightAffineSnapshotCandidateExecution.v) 的 `affine_snapshot_checked_cached_execution` 消费 preparation 与 point preservation，产生相同具体 final memory 和 temps 的 cached 执行；quiet determinacy 对齐给定原出口。 |
| Cached Clight → source Loop | [GuardMemoryAffineInnerPointerRegionSource.v](../adapters/compcert-memory/GuardMemoryAffineInnerPointerRegionSource.v) 的 `memory_affine_inner_pointer_region_source_under_ranges` 消费 checked header/width/ranges，恢复 Loop 执行及原 i/j/K 出口公式。这是 concrete-to-model 方向，不是 parsing 或双向等价。 |
| Source Loop → candidate Loop → lowered Clight | [GuardMemoryAffinePointerCandidate.v](../adapters/compcert-memory/GuardMemoryAffinePointerCandidate.v) 的 `memory_parametric_model_compiled_pointer_candidate` 消费 candidate certificate、两套 bounds 和 footprint-restricted nonalias，将给定 model 执行运输到同一 candidate 的实际编译代码执行，保留 final memory。 |
| Candidate Clight → 公开出口恢复 | 同文件的 `memory_parametric_pointer_candidate_restore` 消费 source decoder 的出口公式，实际执行 restore，得到与原出口的 `temp_agree live`。上述三段由 `affine_inner_pointer_candidate_execution` 组合。 |
| 捕获／检查／选中 branch → region guarantee | `affine_snapshot_planned_captured_candidate_execution` 消费旧 guarded 执行与 plan/tree correspondence，运输私有 flag；`check_affine_snapshot_planned_source_sound` 将普通检查的接受结果转为含原 prefix/suffix 的 `projected_region_contract`。 |
| Region guarantee → Csem→Asm | `compile_selected_snapshot_planned_regions_correct` 消费 compiler 成功结果，实例化语言的 selected installation/backend 证明；实际 site 仍核对 scope、资源和 progress。Kernel 的局部组合结论不单独承担这一步。 |

前提分三种来源。静态 source/capture/resource/candidate checkers 生产语法、
形状、freshness、typed pool 和候选证书；实际 guard、capture 和 transport
定理生产动态 ranges、stability、nonalias 及其入口关系；给定原 source
执行是证明语义保持的起点，并用于恢复 reached-read/write receipts。
Proof 中的 `READY`、`CACHED` 或 `MODEL` 不等于用户应另提供一个假设，也不
意味着各有一个 emitted test。Checked factory 必须在其实际使用位置生产
这些事实；源码用户继续只给支持族的原标注 C、profile 和策略。

## 直接 tree 失败与已验证的 plan 连接

首先固定旧 registry 的
[ClightSelectedSnapshotPolyhedralCompiler.v](../prototype/interface/ClightSelectedSnapshotPolyhedralCompiler.v)
已编译并提取。原直接 tree 路径完成真实 candidate whole-check
`valid=true / alarm-free=true`，随后编译进程收到 SIGKILL，未产出 Asm 或
Clight dump。失败输入与 phase/check 证据已保存；没有 runtime 输出，
也没有把 SIGKILL 单独解释为已测出的 memory 根因。

直接 tree 的 continuation/fallback 在多个路径中展开。后继复用已有
`clight_check_plan`／private Boolean lowering，将每项 conjunction 顺序
执行。三项 plan/tree correspondence 定理证明它保留原完整 condition
规格；编译器直接生成 plan code，不物化完整 specification tree。
原 numeric/stability、具体原执行到 cached execution、polyhedral candidate
checker、实际 codegen 和公开恢复定理保持。相同原 C／configured caps
随后完成编译与完整运行验收；这是可用性证据，尚无统计编译时间或收益结论。

| 新连接 | 证明与具体责任 |
| --- | --- |
| [ClightAffineSnapshotCheckPlan.v](../prototype/interface/ClightAffineSnapshotCheckPlan.v) | 复用旧单 observer 的 row plan，依次组合 N/M，按源活动性短路；plan flattening 等于原实际 condition tree。Kernel 和前提语义不变。 |
| [ClightAffineSnapshotPlannedRewrite.v](../prototype/interface/ClightAffineSnapshotPlannedRewrite.v) | 消费原实际 capture/guard/candidate 执行，复用 `check_plan_guarded_normal_execution` 运输私有 Boolean 与实际 branch/public exit，交付 finite region contract。 |
| [ClightAffineSnapshotPlannedCandidates.v](../prototype/interface/ClightAffineSnapshotPlannedCandidates.v) | Typed result、frameable branches 和 fresh result reads/public scope 都由普通检查生产；原 mapped／tiling／schedule checker和 lowering 绑定同一 candidate。Counter pool 使用最大偶数前缀，未配对尾项不用。 |
| [ClightAffineSnapshotPlannedRegionBuilders.v](../prototype/interface/ClightAffineSnapshotPlannedRegionBuilders.v) | 从真实 frontend source 注册新的 guarantee，沿用 normalization 与 selected site 的原 progress/scope/resource 责任。 |
| [ClightSelectedSnapshotPlannedCompiler.v](../prototype/interface/ClightSelectedSnapshotPlannedCompiler.v) | 在 Rocq 入口内固定旧 word／recursive affine／private-loaded registry 并扩展新 factory。源码用户 callbacks 仅给普通 profile/proposal；完整 Csem→Asm 直接应用共用 selected compiler theorem。 |

新 plan 阶段五模块 432 行、15 endpoints、1 closed、1,850 bindings、至多
旧 baseline 42 globals，无新增公理。此前 registry-only wrapper 30 行／
1 endpoint／1,844 bindings；新增长度和模块数不作为新颖性或作者时间证据。
前阶段 37 endpoints 的 source/condition/candidate 链由冻结 report继承。

## 真实生成、安装与运行矩阵

Ordinary [request adapter](../prototype/interface/native/GuardAffineSnapshotPipelineCandidate.ml)
复用实际 signed-affine proposer，把 checked nonrectangular Loop 及小范围
提案送入 Pluto／prepared codegen，返回原 proposal 数据。独立 factory
检查原 source/model、actual candidate、validator/encoder bounds 和依赖。
Schedule 模式不带 `--identity`。本 tier 配置 row cap 4、column cap 8、
geometry cap 4、logical extent 8192；这些是已测试配置，不是框架最大值。

| 配置 | 实际安装 | Asm／Clight calls | 实际 candidate／runtime fallback |
| --- | --- | --- | --- |
| tile | 两函数各一处；unmarked 函数无替换 | 264／264 | 30／146 |
| schedule | 两函数各一处；unmarked 函数无替换 | 264／264 | 30／146 |
| unannotated | 0 | 264／264 | 0／0，原程序 |
| disabled | 0 | 264／264 | 0／0，原程序 |
| scheduler failure | 0 | 264／264 | 0／0，静态拒绝后原程序 |
| oracle resource refusal | 0 | 264／264 | 0／0，静态拒绝后原程序 |

每正常模式有六次 scheduler/candidate attempts，source-model hashes 只有
两个：selected discovery 试到同一 region 的不同 sequence candidates。
六次 attempt 不等于六处 installed site；dump 核对的是两次实际 captures
及其 candidate/fallback dispatch。没有把重复提案当作新优化功能。

[Fixture 与独立 word model](../scripts/snapshot_polyhedral_fixtures.py)的
每次输出包含两个 9,600-element arrays 的每一项、公开 i/j/K/rp/rq/
snapshot/context 及最终 N/M words。未插桩 Asm、独立 model、`-fwrapv`
reference 三者匹配；另对 emitted Clight 插入 branch counters，既比较
相同全输出，也确认具体接受/回退。插桩 Clight 不代替 Asm 测试或定理。

矩阵实际包含：

- 独立 N/M cells、同数组中稳定 cells、共享 N/M cell，以及 M 指向真实
  RHS cell 的接受路径。
- N 指向实际 store cell而改变 outer 次数，M 指向 store cell而改变后续
  child widths：检查拒绝，原 repeated-load 执行仍给相同全输出。
- 不同 p/q allocations、移位造成 data alias 的旧 guard 拒绝。
- Empty/negative outer 且 M 为 null：source 不到达 M，capture/guard路径
  不新增非法读取；公开 j/K 的原值保持。
- 首个 child empty 而后续非空、profile/cap 拒绝、非零起点、header
  wrapping 和 RHS wrapping；candidate/fallback 接口保持公开控制与原 memory。

正常 tile/schedule 的 Clight source 分别为 175,338／170,707 bytes，Asm
为 56,598／55,211 bytes，均包含完整 fixture/harness。这是原始文件大小，
不是 isolated guard size、动态 guard work 或完整调用成本测量。

## 同一 compiler 的旧族回归

Binary：`build/snapshot-polyhedral-plan/compiler-v1/ccomp`；SHA-256：
`8a7bf41bd5e78c1fa7568dab759b574caf2057c574b2e7d793f4afb54b140243`。
同 binary 另完成 word 四配置 400／400，recursive affine tile/schedule
480／480，以及旧 private-loaded tile/schedule 270／270 Asm/Clight calls。
Recursive affine 仍包括原真实 rank-three 与同函数多 marked regions；
这不把新二维 N/M model 泛化为 recursive loaded-word 联合模型。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_snapshot_polyhedral_plan.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/native_snapshot_plan.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/native_snapshot_plan_regression.py
```

Reports 与 SHA-256：

| Report | SHA-256 |
| --- | --- |
| `snapshot-polyhedral-pipeline/proof-v1` | `de05e9b4dd816cf92c88ee702f018c6a4f1d8b82d0b709d1c30f67631b29b009` |
| `snapshot-polyhedral-plan/proof-v1` | `661e6b94d0d86fd306adfa4811cf1ecd27f6cee28e144951df289fd773fb152a` |
| `snapshot-polyhedral-plan/native-v1` | `a609f9afec3a22593fb070f174e5c9bea2903c171897a5ccafc9a7be33fcc106` |
| `snapshot-polyhedral-plan/regression-v1` | `fe738a716494fe9c7aa660f4cb526a3ed91435bcf35345218c439bbfa35b1237` |

Reports 位于 `build/`，绑定实际 reachable source/object closure、原父
proof、helpers、compiler/driver/parser/extraction/native sources、真实
Pluto binary与各次完整输入/输出/phase artifacts。Plan 的五次 proof builds
均通过，成功输入冻结；原 tree compiler 的失败与两个 harness错误也保存
diagnostic snapshots。第一个 harness误把六次 candidate attempts要求成
两次，Asm全输出已通过；第二个只在 loop header找 loaded comparison，
漏掉 `for(;1;...)` body里的真实 fallback，Asm/Clight 全输出均已通过。
修正诊断后六配置完整验收通过。这些 harness错误不作为误编译证据。

## 尚未完成的完整目标

本阶段落实了原 loaded-affine 二维族的实际 source/model/candidate 与
program connection。首个 child 必须 positive 的旧 preparation条件仍使
first-empty-child 后续非空保守回退；旧 envelope 对 distinct allocations
也仍回退。Value-preserving header aliases、一般 recursive loaded domains、
scalar/chunk覆盖、OLO原例的进一步功能与完整 guard/candidate成本继续验收。

下一优先项是从实际后续 first reached body 生产 scalar/geometry/permission
前提，扩展 first-empty-child 接受域；不能为了接受这些输入，假定未到达的
leaf/RHS已定义，也不能要求用户提供 cached completion。随后改进 alias
sufficient conditions与完整调用成本。此次 compact plan解决代码生成展开；
运行时仍逐点扫描，不据此宣称 guard 紧凑、收益已证或整个目标完成。
