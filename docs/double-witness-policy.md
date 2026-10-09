# 原语料对照与 checked witness-policy 后继

2026-10-09。本次按 [narrative 的验收澄清](narrative-corpus-review-2026-10-09.md)
先跑完整原案例，再解决实际拒绝。Fixed summary：
[double-witness-policy.json](double-witness-policy.json)，SHA-256
`968d810f645b09dcd09263e4c1462bc569d949a45d4e37264d30773892b16b88`。
摘要验证 18,561 个绑定；它不是完整目标已完成的报告。

## 实际输入和结果

使用固定 PolCert revision `ca1ae3199c816594bab9d51eb77309a0d17527aa`
的全部 62 原 harness，保留 I64 controls、原 double／scalar 运算、数组维度和
原始小输入。`corcol3`／`pca` 的初始化适配单独记录，不替换 raw originals。
Reuse 的 GCC reference 来自冻结的首轮报告，未重新生成 reference。

| 对照 | 编译／运行结果 | Actual affine 安装 |
| --- | --- | --- |
| 先前 choices compiler；unmarked／identity／affine | 64 source variants × 3 = 192 配置；186 native matches，6 raw frontend refusals | 11/62 原案例，21 个 guarded sites |
| 新 witness policy；affine | 64 配置；60 raw 和 2 disclosed adaptations 匹配 GCC；2 raw frontend refusals | 14/62 原案例，30 个 guarded sites |

新策略没有丢失先前安装。46 个可编译 raw originals 在 affine 模式完全
回退：44 个没有调用 scheduler，`dct`／`polynomial` 已调用但最终没安装。
前 44 个的具体内部 static checker 尚未逐个定位，不能一概归因于 frontend。
两项 disclosed adaptations 仍没有安装优化。

Installation、nonidentity 和性能分别记账。完整对照新识别 `gemver` 第二
nest 的 j/i 交换；连同前阶段的 `matmul`、`mxv`、`matmul-init`、`mvt`，
以及下述三个新策略案例，共有 8/62 个原案例具备实际非恒等变换证据。
其余安装不因此计入优化效果。`mxv` 的效果包含 initializer/reduction fission；
统计不限于 schedule matrix 与源矩阵不同。

## 解除的实际 blocker

| 原案例 | 原策略的 affine 结果 | 新策略安装的实际候选 |
| --- | --- | --- |
| `matmul-seq` | 两个提议均没有合适 coordinate witness | 两个 i/j/k → i/k/j |
| `matmul-seq3` | 三个提议均拒绝 | 三个 i/j/k → i/k/j |
| `tce` | 四个五层提议均拒绝 | 四个 nest 的坐标 3／4 交换 |

旧纯 assignment 路线只尝试 `[]`／`[0]`；上述实际 candidates 分别需要
`[1]` 和 `[3]`。新不受信任 policy 默认尝试
`[[]; [0]; [1]; [2]; [3]; [4]]`，每次仍调用原 extracted factory。
完全相同的 OpenScop proposal 复用缓存，增加尝试不重复调用 Pluto。
这是有限、保守的搜索，不覆盖 compound permutations、一般 skew 或 tiling。
Legacy／initialized 的独立见证策略尚未改动。

摘要另核对 actual emitted accepted Clight 的 private loop order 与 store
coordinates，比较原 identity 配置。该文本诊断不是独立语义证明；正确性
来自最终 checker、actual lowering 和完整 compiler theorem。特别是 `tce`
保持原 IEEE 运算树，未使用 floating-point reassociation。

## 接口与证明边界

新 native driver 继续调用
`ReductionDoubleChoicesCompiler.compile_selected_reduction_choices_program`；
对应 `..._correct` 已量化任意有限 choices。Source/candidate、footprint、
safe capture、private/public frame、精确退出和 scoped 安装仍由原 factory／
language services 生产。没有新 Rocq theorem 或 axioms；继承最大 42 globals。
源码用户仍给 `#pragma scop`／`#pragma endscop` 和普通策略数据。

重建：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/build_double_witness_policy_compiler.py --attempt new-name
```

已提取 compiler：`build/double-witness-policy/compiler-attempts/native-v1/ccomp`。
`GUARDCERT_DOUBLE_WITNESS_AXES` 控制相邻交换搜索范围（0..32，默认 6）；
范围缩小可以漏掉优化，但不能绕过 checker。其余 scheduler／private-count
配置沿用 [纯 assignment compiler](reduction-double-installation.md)。

## Context、回退与路径

18 项 focused checks 均通过，覆盖三个新案例的缺见证／缩小搜索／外部拒绝，
以及 `matmul-seq` 的真实动态界限、public exits、private refusal、两个 marked
区域和相同 unmarked 邻居。两个 marked 区域安装四处，复用两次实际 external
calls；保留 unmarked 邻居时只安装两处。

初始 public `(i,j,k)=(17,23,29)`：正界限退出为 `(96,96,96)`；零／负界限
为 `(0,23,29)`。三个 debugger runs 在未修改汇编上观测普通／零输入的
两次 candidate entry，负输入的两次 fallback entry。首次 sandbox ptrace
失败及其 rejected report 保留，之后在获准的执行环境中完成观测。
Native observation 是原 modeled scalar／array digest 加 public controls，
不是对任意完整 C 状态的独立比较。

本阶段不报告收益或 isolated guard cost。语料和 focused checks 的 wall time
仅为诊断，测试期间存在其他运行；尚没有较大 tiers、受控完整调用或顺序
PolCert 配置的效果比较。真实 double tiling、额外源结构、原 BT 和 LLVM／SPEC
仍未完成；完整 goal active。

复核固定证据：

```sh
python3 scripts/summarize_double_witness_policy.py --validate
```
