# Canonical alias：完整调用成本

2026-10-08。本测量使用已冻结的
[canonical compiler／native 证据](canonical-alias-compiler.md)，不新增语义
定理或一般 affine 覆盖。同一 marked C、三个 profiles、九输入，比较
disabled source、前一 readonly-probe compiler（memo）和新 canonical scan。
实际两轴 Pluto 与 2×3 prepared tiling 候选继续由原 checker 验证。

**结果：新 scan 明显降低旧版本成本，但这些小例子仍没有优于 source。**
2×3 接受调用相对 memo 降低 38.01%–45.37%，8×8 降低 91.15%–93.01%；
相对 source 仍为 6.34–7.24 倍和 14.29–20.17 倍。部分 bypass／refusal
的观测 median 也升高；不声称统计显著性或代表性 workload 收益。

## 测量包含什么

三 profiles 是固定 stride 的 row、column 和 parameter stride 的 row。
九输入覆盖 2×3／8×8 接受、RHS modular wrap、array alias refusal、start
refusal、header alias refusal、count 超 cap、outer empty 和 child empty。
本实验输入来自已验证的双 loaded 矩形源族，默认 cap 8。

准备阶段先核对三个 repetition counts 下的 243 次未插桩 Asm full outputs，
以及 81 次独立 printed-Clight 调用。Oracle 检查全部 1,024 arena words、
公开 exits 和初始 iterators；重复调用只 reset headers，数组值按 word
semantics 改变，闭式 oracle 另与一至四次顺序源执行核对。

AMD Ryzen 7 7800X3D／WSL2，CPU affinity 0，C `clock()` process CPU time。
30 个随机配对 rounds，seed 20261008，每轮包含全部 81 profile/input/mode
batches，每 batch 使用新 process 和一次 warmup。各 mode 独立校准
repetitions，target CPU time 0.1 s，协议最低 0.05 s；最短实测 batch 为
0.098923 s。全部 2,430 batches 保留，没有丢弃 observations／outliers。

Timer 包含每次 header reset、capture、全部 header/setup/alias guards、
candidate 或 fallback 以及 public restoration；初始化、打印和验证不在
timer 内。Timed code 为未插桩 CompCert assembly，独立 Clight 诊断不计入
CPU 结果。所有 warmup/final full outputs 都核对通过。没有 core isolation、
confidence interval、workload frequencies 或 proof/extraction setup 成本。

## 配对结果

每个值是 30 rounds 中逐轮 new/source 比值的 median，不是两个 median
耗时的商。较小更快；全部九输入／三个 profiles 仍大于 source。

| 输入 | Row | Column | Row，parameter stride |
| --- | ---: | ---: | ---: |
| 2×3 接受 | 6.340 | 6.390 | 7.245 |
| 8×8 接受 | 14.706 | 14.293 | 20.168 |
| RHS word wrap | 7.374 | 7.411 | 7.626 |
| Array alias refusal | 4.713 | 4.997 | 6.673 |
| Start refusal | 1.017 | 1.025 | 1.314 |
| Header alias refusal | 1.107 | 1.120 | 1.091 |
| Count 超 cap | 1.580 | 1.600 | 2.258 |
| Outer empty | 1.307 | 1.306 | 1.300 |
| Child empty | 1.485 | 1.496 | 1.454 |

以下是同一新测量中 canonical/memo 的 median paired ratio；没有拿
旧冻结实验的 ns 与新实验直接相除。

| 输入 | Row | Column | Row，parameter stride |
| --- | ---: | ---: | ---: |
| 2×3 接受 | 0.546 | 0.563 | 0.620 |
| 8×8 接受 | 0.070 | 0.076 | 0.088 |
| RHS word wrap | 0.598 | 0.609 | 0.653 |
| Array alias refusal | 0.451 | 0.497 | 0.607 |
| Start refusal | 0.997 | 1.000 | 1.000 |
| Header alias refusal | 1.010 | 1.005 | 1.000 |
| Count 超 cap | 1.002 | 0.944 | 0.986 |
| Outer empty | 0.985 | 1.001 | 0.991 |
| Child empty | 1.001 | 0.920 | 1.028 |

Raw 精度和所有 observations 在 report／samples 中保留。Row-variable
child-empty 的观测 median 比 memo 高 2.84%；row header-alias refusal 高
1.04%。这些 bypass 未执行新 alias body，不能将小幅差异解释为单独某项
guard 的 CPU 成本。生成代码／寄存器分配／布局也可能改变。

图表 `paper/figures/canonical-alias-cost.pdf` 比较 memo 和 canonical 相对
source 的 ratios，显示逐轮 paired-ratio IQR；IQR 是描述区间，不是 CI。

## 独立动态工作与代码尺寸

Clight 诊断在实际完整 guard 内计数 `if` evaluations，并核对 complete
outputs 和分派路径。Setup 两版本保持 15 tests；parameter stride 为 17。
以下为 row 的完整 guard tests，不是 assembly operation 或 CPU attribution：

| 输入 | Memo | Canonical |
| --- | ---: | ---: |
| 2×3 接受 | 720 | 361 |
| 8×8 接受 | 71,234 | 4,741 |
| RHS word wrap | 737 | 368 |
| Array alias refusal | 720 | 361 |
| Start refusal | 3 | 3 |
| Header alias refusal | 14 | 14 |
| Count 超 cap | 93 | 93 |
| Outer empty | 6 | 6 |
| Child empty | 19 | 19 |

数学差值空间 15／225 不等于 361／4,741 个实际 tests；循环、坐标准备、
template-pair tests 和原 header/setup 都计入完整 guard。Alias false 后
仍继续扫描，未实现 early refusal。

Linked kernel function bytes（`nm -S`）：

| Profile | Source | Memo | Canonical |
| --- | ---: | ---: | ---: |
| Row | 113 | 1,344 | 1,349 |
| Column | 113 | 1,329 | 1,353 |
| Row，parameter stride | 122 | 1,471 | 1,543 |

新 guard 减少工作，没有减少本例的代码尺寸。编译 wall time 是单次已构建
compiler 的调用，约 source 0.032 s、固定 stride 两优化器 1.82 s、
parameter stride memo／canonical 2.52／2.42 s；没有重复分布或 compile-time
收益结论。

## 证据与复现边界

Preparation report：`build/multi-word-nested-canonical/cost-prepared-v1/report.json`，
SHA-256 `fbf55d17c604ec59b6e97c9487cd7a95ac91db990a879ba90b4fc9d7bb84335c`。
Timing report：`build/multi-word-nested-canonical/cost-v1/report.json`，SHA-256
`3ef038e3df1a3e05fbd558c69a62e042bb6dc13a2ab1234f6fcdf52b34c2b01a`。
Plot report：`build/multi-word-nested-canonical/cost-plot-v1/report.json`，SHA-256
`da553a1c45b13091c31d5baad57456f9c6b01943fcbaeb9827fad7b580bcd36d`。
`samples.jsonl`、全部 calibration/warmup/final outputs、prepared sources、
原 assembly、diagnostic C／results 与 helper hashes 都绑定。父 proof/native
报告核对 hash，不重跑历史 experiments；成功 artifacts 不覆盖。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/prepare_word_nested_canonical_cost.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/measure_word_nested_canonical_cost.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/plot_word_nested_canonical_cost.py --validate
```

这是既有 toolchain／prerequisites 上的冻结 checkpoint 验证，不是 fresh-build
artifact。新的 timing／plot 需要新 work／asset path，不能覆盖此报告或旧
memo experiment。

## 下一项验收

优先减少重复／同 root 的常量 tests 和 false 后的扫描，证明所采用的
exactness 或充分性，并从原源许可实际读取；同时考虑便宜的 header
stability 条件。新实现必须接实际 scan exit、candidate/fallback、公出口
和编译器，并重新测完整调用。跨 allocation 的 pointer ordering 可能无
定义，不能直接换成通用 pointer interval check。

当前实际 alias 服务更便宜，但没有达到本源族的盈利性；一般参数化／
非矩形 affine 域、更多 scalars/chunks、完整 OLO 联合能力、条件服务的
实例作者负担与代表性 workload 验收继续属于完整 goal。
