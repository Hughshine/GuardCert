# 原 matmul：完整三层源循环、条件化 header 前提与公开出口

本阶段完成同一原 matmul selected region 的完整三层 Clight↔typed PolCert
Loop 有限执行对应。最终 CompCert memory 和所有 temps 的出口精确保留。
入口前提按到达路径区分 M／N／K 的读取。**尚未安装完整 matmul 优化**：
安全 capture／guard、实际 typed pipeline、candidate Clight lowering、site
producer 和 selected Csem→Asm 仍待完成，原案例新增优化数仍为零。

## 原程序与已完成链

复用[原 typed bridge](original-matmul-typed-bridge.md)冻结的完整 exported
Clight 和[内层循环证明](original-matmul-inner-loop.md)。原 C 的 double 运算
树、100×100 nested global arrays、padding 2、I64 i／j／k 与 I32 literals
保留；没有用整数 fixture 替换计算或更换 dimensions。

```text
真实 f_main 中选出的完整三层 region
       ↕ 原初始化／header load／break／increment 的有限执行
嵌套 counted_iterations（真实 CompCert memory actions）
       ↕ 仿射访问与实际 global registry 的对应
typed PolCert 三层 Loop
```

`OriginalMatmulNest.original_selected_nest_exact` 用 Rocq reflexivity 核对实际
selected region 的完整 AST。`original_full_nest_typed_model` 直接作用于
该 region，双向连接真实 statement execution 与完整三层 model，并刻画
精确公开出口。它不要求初始 i／j／k 已有值，初始 absent／Vundef 状态也会
按原初始化和到达路径保留或覆盖。

Model 的参数环境是 `[M;N;K]`。外层 `Var 0` 是 M；插入 i 后，中层
`Var 2` 是 N；再插入 j 后，内层 `Var 4` 是 K。Body 以
`[k;j;i;M;N;K]` 解释原三个访问坐标，保留每次 IEEE 运算树及原 k 顺序。
Proof 中的 `counted_iterations` 沿用既有关系，没有增加第二套 optimizer IR。

实际 typed pipeline 还有一个 Rocq 接口差异：`DoubleAssignmentLoop` 与
`DoubleAssignmentIRs.Loop` 的 AST 来自不同 functor instances，不能直接赋值。
已重现并保存该 type rejection。新增 `GuardMemoryDoubleMatmulPipelineLoop`
用实际 `DoubleAssignmentIRs.Loop` constructors 构造同一三层 model，证明
两个实例的 body／inner／middle／nest 执行双向对应，保持同一 instruction
和真实 runtime state。`OriginalMatmulPipeline.original_full_nest_pipeline_model`
把实际 selected source 接到这个 pipeline 实例；这不是通用 AST coercion，
也不是一次新的 scheduler／codegen 调用。机器摘要见
[original-matmul-pipeline-loop.json](original-matmul-pipeline-loop.json)。

## 条件化的入口事实

完整 source invariant 的可读性字段为：

```text
load(M) = M_word
M > 0             -> load(N) = N_word
M > 0 and N > 0   -> load(K) = K_word
```

因此 M=0 不要求 N／K load；M>0、N=0 不要求 K load。N 和 K 的 global
binding／声明等静态事实仍是接口前提，它们与一次 runtime read 的 definedness
不同。当前没有新 emitted capture 或 guard，这些条件式 load 前提不是
一个已安装的可执行检查，也没有许可外层为空时提前读 N／K。

每个实际 C action 只 store 到 C 的 global block。静态 symbols 及 C 与
M／N／K identifiers 不同，推出 blocks 分离；由真实 `Mem.store` 保持三种
header observations，再推广到所有内层／中层 physical iterations。该
frame 不依赖提前读取 header，也不需要逐个 body entry 来假设稳定性。

当某层确实活动时，源 loop 的当前 I64 word、数学坐标范围和该层 invariant
自动建立下一级入口，直到旧 assignment 的实际地址 receipts。Runtime
body reads 继续从原 assignment execution 恢复，而不是在检查时先执行源程序。

本阶段 scope 是非负、有 signed I64／padding／地址界限的 M／N／K；固定
原 AST 的对应端点使用每维至多 98 的充分范围。负 bound 的 zero trip 与
更一般 affine domains 仍需接入，不能据此移出总目标。有限执行 iff 消费
一侧已有完成执行，没有交付 total progress 或 divergence 结论。

## 精确公开出口

| 原路径 | 最终 memory | 公开 temps |
| --- | --- | --- |
| M=0 | 与入口相同 | i=0，原 j／k 保留 |
| M>0，N=0 | 与入口相同 | i=M，j=0，原 k 保留 |
| M>0，N>0，K=0 | 与入口相同 | i=M，j=N，k=0 |
| M>0，N>0，K>0 | 原按 i/j/k 顺序的 double actions 结果 | i=M，j=N，k=K |

所有其他 temps 精确保留。出口公式以 `PTree.set` 和维数 zero/nonzero
分支定义，双向定理保留整个 temp_env，不只证明三个 lookup。
`original_outer_empty_exit` 和 `original_middle_empty_exit` 还在实际 AST
identifiers 上核对空路径公式。候选 lowering 之后必须恢复同样的出口；
本阶段的 source exit 不是已证的候选安装。

## 证明责任与剩余接口

| 新模块／层 | 输入责任 | 提供的证明 |
| --- | --- | --- |
| `GuardMemoryLongLoopSettle`，language library | 实际 header、body 双向执行／settle、normal、当前 iterator frame、body／increment invariant | 初始化与完整有限 I64 loop ↔ physical iterations＋精确 temps exit；允许 body 改内层计数器 |
| `GuardMemoryDoubleNestControl`，language/domain 实例 | 原源模板、static bindings、C 与 headers 分离 | actual normal／write frames、真实 store 保持 header loads、nested physical actions 与公开出口定义 |
| `GuardMemoryDoubleMatmulNest`，optimizer/domain | 静态 globals、非负范围、按到达路径的入口 loads | 原 j/k 和 i/j/k loops 的双向 physical correspondence；实例化所有 settle／frame／invariant 义务 |
| `GuardMemoryDoubleMatmulNestModel`，optimizer/domain | 同一 source/static facts 及 layout certificate | physical nested execution ↔完整 typed Loop；合成 source↔Loop 与公开出口 |
| `GuardMemoryDoubleMatmulPipelineLoop`，optimizer adapter | 同一具体 double instruction／state 与三层 shape | source bridge 的 Loop↔实际 POLIRS pipeline Loop；不同 AST 实例的执行对应 |
| `OriginalMatmulNest`，具体 site | 实际 selected region、适用 static／conditional entry facts | AST 精确匹配；完整真实 region 的 source/model bridge；固定 identifier 差异及小范围 I64 事实 discharge |

Kernel 和既有 whole-program host 均未变。Generic settled-loop 的参数是
language/transformation 作者的证明接口；原 matmul 实例已经 discharge
body/frame/settle 责任。最终标注 C 用户仍只给源码与策略选项，不能接收这些
语义 callbacks 或入口事实作为未完成的使用要求。

这完成了 narrative `C_opt` 中的 source/model 链，并提供 `C_derive` 的
loop invariants→reached local obligations 部分。Candidate validation／lowering
仍须补上另一端；`C_guard` 必须安全生产入口条件；site/factory 则生产
metadata、scope、typing、resources 和所需 progress，再接 `C_host` 与
全程序 installation。Source/model iff 本身不代替上述责任。

下一实现继续原 matmul 的入口 metadata／条件 bound capture producer，与
真实 typed scheduling／tiling／codegen、candidate Clight lowering 和安全
guard 共同接入，再复用 selected compiler 交付 Csem→Asm、native 接受／
回退及全成本。其余 62 原 cases、原 BT 与其他顺序路线继续保留。

## 审计与复现

四个新模块共 567 行；独立查询 23 个端点，其中八个 closed；单端点最多
使用六个 inherited globals，无新增公理。跟随 215 reachable sources，
连同父 checkpoints、实际 AST、helpers 与尝试绑定 7,148 个文件。五次
成功和 12 次拒绝保留；旧成功源／objects／helpers 未覆盖。

Proof checkpoint：`build/original-matmul/nest-proof-v1/report.json`，SHA-256
`80f3f2184572fcaf29664fdaa58533080e4fe133b892a6f4760c70cfbca4f84a`。
Actual source checkpoint：`build/original-matmul/source-nest-v1/report.json`，
SHA-256 `5aae683286a6f6303b5e0297feff4b89015513f52b8adeb13f6ddc8c021102f8`。
机器摘要见[original-matmul-full-nest.json](original-matmul-full-nest.json)。
`build/` 下完整 objects／AST／logs 不随 Git 提交。

Pipeline Loop 后继单模块 99 行、四端点／一 closed，最多六 inherited globals，
无新增公理；跟随 221 reachable sources，绑定 7,186 files。两次成功、两次
proof 拒绝，以及另一次预期 AST type rejection 保留。检查点为
`build/original-matmul/pipeline-loop-proof-v1/report.json`，SHA-256
`070a3d197560268de736db86ec178ac8bbdc0a0e31e2d789551dd5507a32229f`；
实际 selected-source pipeline bridge 的报告为
`build/original-matmul/source-pipeline-loop-v1/report.json`，SHA-256
`09abd7e2d415361af51392a536ca1a154e8b463988f7c6b436d63f3a2bbd649b`。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/compile_matmul_nest_sources.py MODULE --attempt NAME
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/prove_original_matmul_nest.py --attempt NAME
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_original_matmul_nest.py --validate
python3 scripts/summarize_original_matmul_nest.py --validate
```

先建立旧 inner-loop checkpoint，再依次编译本表四模块，生成 actual region
proof；首建 audit／summary 不带 `--validate`。成功目录冻结。本阶段无新的
extracted compiler、native 比较或性能／成本结论。

Pipeline 类型后继在上述 full-nest checkpoint 之后编译：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/compile_matmul_pipeline_loop.py GuardMemoryDoubleMatmulPipelineLoop --attempt NAME
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/prove_original_matmul_pipeline_loop.py --attempt NAME
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/probe_matmul_loop_instance.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_original_matmul_pipeline_loop.py --validate
python3 scripts/summarize_original_matmul_pipeline_loop.py --validate
```

首次创建 pipeline audit 前，不带 `--validate` 运行 diagnostic probe 和 audit。
Probe 预期 Rocq 拒绝直接跨实例传 AST；正向连接由已通过的 adapter theorem
提供。该复现 helper 检查已有冻结 diagnostic source／log 的相同结果。
