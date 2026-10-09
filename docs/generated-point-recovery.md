# 真实 polynomial：候选安装通过，完整调用成本失败

2026-10-09，再次 fetch narrative，远端可见版本仍为 `8ce9c8b`；
`paper-narrative.md` 和 `context-lifting.md` 与 main 正文一致。本后继继续其责任
划分：kernel 消费局部证书，language 负责实际检查／执行／安装，domain 负责
source/model、充分条件和最终候选。源码用户仍给标记 C 和策略数据。

## 当前结果

同一个 compiler build，自动 affine scheduling → tile 32 → intra-tile scheduling，
无 private／witness override，完整尝试 62 原例和两份公开 initializer adaptations：

| 结果 | 原例 | 两份 adaptations |
| --- | ---: | ---: |
| 编译、链接、native 输出匹配原 GCC | 60 | 2 |
| 既知 frontend refusal：corcol3／pca | 2 | 0 |
| Compiler timeout／native mismatch | 0 | 0 |
| 安装至少一处优化 | 14 | 0 |

14 个安装案例为 dct、fusion6、fusion7、gemver、matmul-init、matmul-seq、
matmul-seq3、multi-loop-param、mvt、mxv、mxv-seq、mxv-seq3、polynomial、tce，
共 30 sites。此前完整默认 build 为 13/62、29 sites，并保留 polynomial 的
600 秒 timeout。本次 polynomial 编译约 2.720 秒，tce 约 134.943 秒；两者是
该次运行的诊断，测试曾并行，不据此推断受控 compile-time speedup。
45 个已编译原例没有 tiling-phase call；tricky3 调用后因缺 tiled point space
拒绝，没有 raw candidate。安装计数不等于运行时接受域、完整配置覆盖或收益。

## 两个 blocker 与对应修复

原 polynomial 保留 `n=4096`、double 数组、I64 控制和原 IEEE 表达式树：

```c
for (long long i = 0; i < n; ++i)
  for (long long j = 0; j < n; ++j)
    c[i+j+2] = c[i+j+2] + a[i+2]*b[j+2];
```

同一标记 span 中前面的 `c[i+2]=0` 循环仍按原程序执行。没有用小尺寸或整数
fixture 替代原 benchmark。小尺寸动态 header 仅用于独立 context tests。

第一处 blocker 在 prepared codegen 的 AST generation。Exact-duplicate policy
未修复它；[GuardMemoryRayOracle.ml](../adapters/compcert-memory/native/GuardMemoryRayOracle.ml)
改为提议保留同方向最强的 normalized halfspace 和不同 equalities，始终只
返回已有 input certificates。原 emptiness search、限制和 LCF 检查不变。
`CstrD.assume_correct` 只要求 overapproximation；原 `ExactCs.fromCs` 的反向
inclusion 检查和 `fromCs_correct` 仍给 canonization 的精确性。没有为 native
最强约束策略增加 exactness／minimality 公理或证明。

Ray-only build 完成 raw codegen，约 2.232 秒编译并匹配原输出，但最终 checker
拒绝安装：这时执行的是源回退，不能报告优化支持。该失败保留独立 report。

第二处是实际 raw Loop 的坐标表示。Pluto 的中间 schedule 为 `(i+j,i)`；tile
坐标为 `floor((i+j)/32)` 和 `floor(i/32)`，最终 tile 内顺序为 `(i,i+j)`。
Raw codegen 又保留了一个 `j=(i+j)-i` 的单次循环。原 syntactic singleton
cleanup 不识别结合方式不同但仿射相等的上下界。

[GuardSelectedDoublePointCoordinates.ml](../adapters/compcert-memory/native/GuardSelectedDoublePointCoordinates.ml)
从实际 instruction arguments 推导 affine 形式，做两种不受信任提议：

1. 当 `upper-lower=1` 的 affine 规范式成立，代入 binder 并去掉该 singleton。
2. 对最内层 point argument `t+offset`，平移 loop binder、上下界、guards 和
   instruction arguments，恢复源 point 坐标。

本例 raw depth 从五降为四，参数由 `(i,t-i)` 恢复为 `(i,j)`。真正的 skew
tile 条件与调度保留，未改成 identity scheduling，也未手写目标循环。
保存 `raw-generated.loop`、`point-normalized.loop`、`completed.loop` 和
`generated.loop`，分别记录提议和最终检查对象。当前仅实现 innermost affine
translation；没有宣称任意 unimodular recovery 或 mixed-unit completion。

## 正确性 authority 与条件责任

新 native adapter 是既有 theorem 量化的任意 `adapt` 数据回调：

- [checked_double_reindexed_tiled_prepared_loop_progress_at](../adapters/compcert-memory/GuardMemoryDoubleReindexedTiledPrepared.v)
  消费实际最终 checker 的成功，而不是 native 的局部等价性声明。
- [validated_double_reindexed_tiling_loops_at](../adapters/compcert-memory/GuardMemoryDoubleReindexedTiling.v)
  连接最终提取表示、实际依赖验证及 captured 参数处的 forward progress。
- [checked_double_reindexed_tiled_reduction_guarded_execution](../adapters/compcert-memory/GuardMemoryDoubleReductionReindexedTiledLowering.v)
  复用原源 capture/model、实际 Clight lowering、公开 I64 exits 和回退运输。
- [compile_selected_initialized_tiled_stable_program_correct](../prototype/interface/InitializedDoubleTiledStableCompiler.v)
  仍给当前 Csyntax source 的 Csem→Asm backward simulation。

未增加语义 proof module、公理、kernel 或 host 定律；不假定 raw→adapted
等价性。该具体路线仍直接构造 Clight branch execution，不能把 unchanged
kernel 或 imports 当作直接调用 generic kernel composition theorem 的证据。

本例原 declared footprints 经 factory 静态检查产生充分界限 4098，真实 runtime
capture 检查 `0<=n<=4098` 后精确转到 model parameter。原源执行许可 header
观察；static metadata 和既有 globals/frame 证明供给 binding、不同数组 block
与 header stability。没有要求 C 用户声明这些事实，也没有新增 runtime alias
test。此实例的静态分离能力不能冒充任意 pointer alias 的已支持条件。

## Context、拒绝和公开出口

16 类 polynomial context tests 的有效后继均通过：关闭 point normalization、
错坐标、错 witness、malformed 和 scheduler refusal、private 不足、unmarked、
动态正／零／负 header、多 marked、marked＋相同 unmarked neighbor、公开
iterator 和实际改名／改维度。Wrong-coordinate 提议最终拒绝，native 原输出
匹配，说明 representation proposer 没有替代 final checker。

Public context 的正数 64 留下 `(i,j)=(64,64)`；零和负数留下 `(0,23)`。
三次 debugger 观察使用 unchanged assembly：正数和零进入 candidate，负数进入
fallback，各一处。它们是实际 block-entry 证据，未向 guard 插入计数代码。
最初改名脚本误改 escaped newline，15/16 通过；只对失败项改正生成器并重跑。
失败 report 与 fresh successor 同时保留。

另有 14 项 reduction contexts、20 项 initialized contexts、7 项 public／legacy
回归通过。Mvt 和 sequential matmul 的 all-unit tiles 各通过；mvt 的 `(1,32)`
也通过。给三维 matmul 错传两项 sizes 的失败保留；修正为 `(1,32,32)` 后仍因
`generated coordinate order outside unit completion` 拒绝。这个真实配置缺口
不被 all-unit 或普通 tile 32 成功覆盖。

## 完整调用成本：必须解决的退化

所有上述进程结束后，用同一 compiler 和 flags 重新编译未标记原 source，优化版
使用已保存、未修改 assembly。每版一次 warmup，再交替七次完整调用；全部输出
匹配原 GCC，调用含 startup、initialization、region 和 digest：

| 版本 | Wall median |
| --- | ---: |
| 安装的原 polynomial | 2.671250 秒 |
| 同 compiler 未标记 source | 0.013788 秒 |
| Optimized／unmarked | 193.740 倍 |

未做 CPU affinity／外部 host-load 控制，也未隔离 guard 成本；这是一个原案例
的完整调用测量，不是整个 benchmark 集的收益结论。前一测量只有 dump flag
差异，单独保留；上表采用修正后 flags 一致的 `cost-v2`。两次都显示严重退化。

源码中已经可以定位一个机制：旧 `upper_enclosure` 将 `floor(e/d)` 放宽为
`e+1`，例如 quotient 外循环枚举至 `2*n+31`，并用 membership guards 过滤。
正确性由 final checker 保证，但宽枚举与大量冗余 membership tests 会增加工作。
测量尚未把两者分别计时；不能把全部退化都归给 entry guard。

下一优先是**可检查的紧凑 quotient／min/max bound lowering**：domain 负责
数学界限／提取表示与候选 correspondence，language 负责 machine division 的
定义性、floor 约定、范围、实际 loop execution 和 private frame，再复用实际
candidate progress、public exits 和 Csem→Asm。不得直接用 runtime `limit` 将
当前量化所有参数的 final checker 常数截断。Kernel 不应了解 C division。
这是需要新增的具体可复用服务，不是扩大 kernel 或只调预算。

完整 goal 保持 active。继续 mixed-unit、实际 source structure、ISS 等 sequential
phases、原 BT、LLVM/SPEC、larger tiers，以及条件尺寸／接受域和完整成本。
本次关闭原 polynomial 的 raw-generation／安装 blocker，成本验收明确失败。

[固定摘要](generated-point-recovery.json)绑定 18 份 reports、19,246 文件：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/summarize_generated_point_recovery.py --validate
```
