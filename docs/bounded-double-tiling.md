# 在已证明的入口条件下验证实际候选

2026-10-09，重新 fetch narrative，远端可见提交仍为 `8ce9c8b`，
`paper-narrative.md` 与 main 正文一致。本后继落实其证书链与三方责任：
入口条件不仅决定运行时选哪个分支，也能限制候选验证必须成立的语义域。
完整 goal 保持 active。

## 这一步解决了什么

[前一版本](generated-point-recovery.md)已安装原 polynomial 的真实 skew tiling，
但其 final checker 要求所有参数处成立。生成器因此用很宽的 affine enclosure
代替 quotient/min/max bounds，再用 membership guards 过滤；原 `n=4096`
完整调用对同 compiler 未标记版慢 193.740 倍。

实际 source factory 已从声明的 footprints 导出充分 limit，安全 capture 在接受时
证明 `0 <= n <= limit` 并精确编码 model 参数。新证明让 final checker 消费这个
已取得的事实，而不是忽略它，也不是直接将一个量化所有参数的定理截断。

对数学 Loop 定义

```text
R(n) = (0 <= n && n <= limit)
assume_R(body) = Guard(R, body)

validate(assume_R(source), assume_R(actual_candidate)) succeeds
+ actual capture proves R(n)
+ original source execution yields source Loop execution at n
------------------------------------------------------------
actual_candidate executes at n with the required final state
```

`R` 是验证用的模型限制，没有作为额外 check 插入运行时程序。运行时事实来自
原本已经证明的 capture。最终降低的是未包裹 `assume_R` 的 actual candidate。
Source/candidate 的 wrapped-domain 检查仍覆盖域、坐标和真实 memory dependences。
范围以外的候选不必正确，因为 guard 拒绝时执行原 source。

## 实际接口与证明消费

优化实现者仍可提供任意不受信任的 `phase`、`adapt` 和有限 coordinate choices。
新 domain 服务
[checked_double_bounded_tiled_prepared_loop_progress](../adapters/compcert-memory/GuardMemoryDoubleBoundedTiledPrepared.v)
先运行原 checked phases 和 prepared codegen，取得真实 raw Loop 与 witnesses，
再调用 `adapt limit raw`，并对实际最终候选作范围内检查。
`_at` 定理消费 checker 成功、参数长度、non-alias、范围事实及 source Loop 执行，
推出该候选在同一参数和初始状态的执行。它不假定 raw→adapted 等价。

支持族的源码用户仍只给标记 C 和策略数据，内部前提由 factory 生产。责任如下：

| 层 | 本例提供／消费的内容 |
| --- | --- |
| 通用服务 | `PolCertLoopGuardFor.guard_execution` 给数学 Guard 的语义；新 `DoubleAssumption.guard_execution` 实例实际用于解除模型包裹 |
| Domain／optimizer | 模型范围 test、wrapped extraction／最终 tiling validation、固定参数 candidate progress；native 仅提议 interval bounds 和 point predicates |
| Clight 语言与 concrete factory | 原 source 许可 header read，实际 capture 的 range／conversion／state transport，source→Loop，checked lowering、公开 I64 exits、原 source fallback及 fresh frame |
| Clight host／compiler | 当前 intermediate program 上的 region guarantee／placement 与安装，有限 pass composition 和 Csem→Asm |

模型 Guard 的复用是一个明确的通用服务消费点；Clight guarded-execution 证明仍
直接展开真实 branch execution，没有改成调用 generic `guardify` composition。
不能把这两种复用混为一谈。Minimal kernel 与 host 定律不变；这不是普遍的
assumption extractor，也不是任意 Presburger predicate 或多参数 capture 的新 API。

两个实际 lowering 定理为
[checked_double_bounded_tiled_reduction_guarded_execution](../adapters/compcert-memory/GuardMemoryDoubleReductionBoundedTiledLowering.v)
和
[checked_double_initialized_bounded_tiled_guarded_execution](../adapters/compcert-memory/GuardMemoryDoubleInitializedBoundedTiledLowering.v)。
它们从真实 capture 的 `count` 和 `count <= limit` 取得范围，接入旧 candidate
execution／exit restoration。两个 factory 内部 discharge 这些义务。

[compile_selected_bounded_tiled_stable_program_correct](../prototype/interface/BoundedDoubleTiledStableCompiler.v)
给原 source `Csyntax.program` 的 Csem→Asm backward simulation，沿用 CompCert
的 parsing／assembly／linking 边界。空表保持 program，后续 pass 重新检查当前
intermediate program。八个新模块共 863 行，19 个 queried endpoints，1 个 closed，
最大 42 inherited globals，502 reachable sources，无新增 global assumption。
两次初始 proof failure、成功后继、source snapshots 和 object digests均保留。

## 不受信任的紧界限提议与首次拒绝

Native 先从真实 Loop 去掉 affine singletons、恢复 innermost point translation，
再用 arbitrary-precision interval arithmetic 提议 quotient 外循环的常数 enclosure。
它优先保留 lower／upper leaves 中仿射差为正常数的 tile-local ranges，并在实际
instruction arguments 上提议 `0 <= coordinate < n`，保留原 raw Guards。
这些算法没有 exactness／minimality／充分性证明；最终 checker 是 authority。

第一次 native build 的每个 point predicate 都以 `TConstantTest true` 收尾。
该节点的数学语义为真，但原 `ExtractorFrontend.wf_affine_test`／`test_to_aff`
仅接受 LE、EQ 和 And；候选因而拒绝。关闭 bounds adaptation 时旧候选仍安装，
说明新范围证明接线可用。首次 profile 两例输出匹配却零安装，20 context tests
仅 10 项通过预期，7 public／legacy tests 仅旧 affine 一项通过。
所有失败 sources／builds／reports冻结保留。

[命名后继](../adapters/compcert-memory/native/GuardSelectedDoubleBoundedPointCoordinatesV2.ml)
去掉不受支持的 sentinel，保留相同 point-box 条件。原 polynomial 的实际候选为：

```text
guard n >= 1
for qsum in [0,257)
  for qi in [0,129)
    for i in [32*qi,32*qi+32)
      for j in [-i+32*qsum,-i+32*qsum+32)
        if 0<=i<n && 0<=j<n
          original double instruction(i,j)
```

257／129 从实际 raw expressions 和 factory limit 4098 提议，未按 benchmark
名字或当前 `n=4096` 硬编码。保留 Pluto 的 `(i+j,i)` scheduling、skew tiles
和原 IEEE expression tree；同一 span 前面的初始化 loop 仍按 source 执行。
错缩 bound、删掉 point-domain predicate、错 coordinate／witness 的提议最终
拒绝，并保留原输出。

## 完整输入、上下文和成本

同一新 build 完整尝试 62 原例＋两份公开 initializer adaptations，默认 tile 32，
无 private／witness override：60 raw＋2 adapted 输出匹配原 GCC，corcol3／pca
仍为既知 frontend refusal，零 compiler timeout／native mismatch。
仍为 14/62 安装 30 sites；本次没有扩大案例覆盖。45 个已编译原例没有 tiling
phase，tricky3 调用后缺 tiled point space。Polynomial 编译 2.599 秒、tce
146.784 秒为 partly concurrent diagnostics，不是受控 compile-time 比较。

20 polynomial、14 reduction、20 initialized、7 public／legacy checks 全通过。
覆盖动态正／零／负 header、多 marked、相同 unmarked neighbor、改名／改维度、
资源与错误提议拒绝及公开 iterator exits。三次 debugger 在 unchanged assembly
观察正数／零进入 candidate、负数进入 fallback，没有改 guard 或插入计数。
All-unit mvt／matmul 各通过，mixed-unit mvt 通过。

Proper rank-three matmul `(1,32,32)` 仍因 `generated coordinate order outside
unit completion` 拒绝，fallback 输出匹配。实际 raw point arguments 为
`(v4,v0,v1)`，当前 completer 按源轴顺序期待 `(v4,v1,v0)`；这指出 unit completion
与 tile 内重排组合的具体提议限制，不能据此减少 functional target。

所有上述命令结束后，优化版复用保存的 unchanged assembly，未标记同源版由同
compiler／flags 编译且零 sites。一次 warmup，随后七次交替完整调用全部匹配 GCC：

| 版本 | Wall median |
| --- | ---: |
| 原 polynomial，范围内检查＋紧界限提议 | 0.031044 秒 |
| 同 compiler 未标记 source | 0.013714 秒 |
| Optimized／unmarked | 2.263590 倍 |

这是 complete call，含 startup、initialization、region 和 digest；未控制 CPU
affinity／外部 host load，未隔离 guard 成本。相较此前记录，严重宽枚举退化已缓解，
但仍慢于 source，成本验收失败；跨次记录不作为受控 speedup 实验。

当前仍用 source-derived cap 的常数外界，小 `n` 可以枚举远多于实际工作。
这不是 runtime-dependent quotient/min/max 的精确降低，也未新增 machine division
服务。下一步须让 domain 表示／验证与语言的实际 floor／ceil／min/max 执行相连，
测量完整调用与输入接受域，并修复 mixed-unit 重排。其余 source structures、
ISS／two-level 等 sequential phases、原 BT、LLVM／SPEC与 larger tiers继续必需。

[固定摘要](bounded-double-tiling.json)绑定本次 proof、builds、完整语料、contexts、
paths、失败记录与成本；它同时绑定前一阶段，不将回退算作优化支持：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/summarize_bounded_double_tiling.py --validate
```
