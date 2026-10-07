# Loaded affine guard：复用已接受事实，删除重复检查

2026-10-06。接续 [loaded multi native](research-checkpoint-2026-10-06-loaded-affine-multi-native.md)。
沿 narrative `226ba94` 开始处理实际 guard 可用性；完整目标保持 active。

## 实际改变与验证责任

原组合执行 capture／numeric／稳定性扫描，接受后运行旧多数组 guard；后者又执行一份
numeric／first-path probe，之后才检查 alias。本阶段删除第二份 numeric probe。
稳定性拒绝时保留原 repeated-load fallback；接受才取得 cached-source receipt，
运输已接受事实后运行原 alias scan，仍使用原 candidate P／local proof／语言 host。
Source completion 不预置未来稳定性，kernel 和 whole-program entrypoint 不变。
现行 checked factory 自动构造 residual code，metadata 使用者不增加手写证明或语义回调。

[AffineNestGuardFactTransport](../prototype/affine-nest/AffineNestGuardFactTransport.v)证明 first-path flag
只依赖 earlier coordinates、参数和当前 header。Child controls 可以尚未初始化或在前一
private scan 中改变；probe 按 canonical dependencies 初始化它们。运输不要求所有 statement
temps 相等，再复用 numeric interval flag frame，取得完整 numeric flag 的运输。
两个端点均闭合于全局上下文。

[AffineNestAliasOnlyGuard](../prototype/affine-nest/AffineNestAliasOnlyGuard.v)的实际 code 仅含旧 alias
scan。在真实 source receipt、numeric 已接受和 result=true 下，执行正常完成、memory 不变、
public frame 保持，结果仍是旧 `affine_multi_guard_flag`。证明中使用旧 numeric guard 定理取得
mathematical domain，不会在提取 code 中重新执行 numeric 检查。

[当前 producer](../prototype/interface/ClightLoadedAffineMultiGuard.v)用实际 captured word 的唯一性
和 protected ports 的 frame 运输事实，再消费 alias-only 执行。语言提供 frame 与 entry relation；
domain 关闭 dependency／机器 flag／实际 scan 的证明；kernel 继续组合证书。
此为具体 residualization，不是通用前提发现器或最小 guard 合成。
同 block 接受、self-alias 拒绝和原 fallback 的 Rocq fixture 已更新；域仍为有限正常源完成，
不扩称任意局部 divergence 等价。

## 当前验证与代码规模

独立 audit 通过 **35 端点／694 递归依赖／1,023 源摘要**，新增两个 fact-transport 和一个
alias-only 端点，其余为现行 producer／host／fixtures。Compiler 与旧 deep／当前 cursor 回归
保持原 42 项假设。Scan、旧 materialized 与当前 cursor source/object bindings 保持；
旧 loaded multi 的 guard 与 fixture source 两处变化，前一报告不重写。

独立提取消费同一 `compile_loaded_affine_multi_regions` 完整 Csem→Asm 定理。
六配置全部重新编译并运行，各 104 调用，共 **624 次**，完整 arrays／公开出口／实际 bound
与 word 模型及 GCC 参考一致。静态安装集合与冻结基线相同，错误候选及资源耗尽保持源。
新 **208 次** Clight 路径调用和 **21 个**未修改汇编探针通过；候选重排、tiling、两次 rewrite、
同 block slices、alias fallback 和短源拒绝顺序保持。旧矩阵不累计为本次结果。

| interchange 完整函数 | Clight if 数 | Clight bytes | linked machine bytes |
| --- | --- | --- | --- |
| 三轴 accumulator | 56→41 | 7,698→6,269 | 896→782 |
| 三数组 | 77→62 | 13,221→11,482 | 2,061→1,936 |
| 同函数两次 rewrite | 88→64 | 9,886→7,798 | 1,119→940 |
| 两 word 短源 | 36→28 | 3,918→3,342 | 295→276 |

这些数含 guard、候选与 fallback，不是 guard 单独大小。Tiling 的下降另见 native report。
循环数量没有减少，没有计时或性能收益结论。

## 独立观测检查工作

[工作量探针](../scripts/probe_loaded_affine_guard_work.py)在旧／新 interchange binary 的函数入口
暂停，计数两个生成函数内的 64-bit register-register compare instructions，在第一次真实
output store 后停止。四个 probes 核对独立模型工作量及首 store 值。
这是选定函数的 pointer-comparison 工作，不是完整指令数、周期、时间或收益。

| 固定输入：46 source points | 旧比较次数 | 新比较次数 | 对应工作 |
| --- | --- | --- | --- |
| 单数组 accumulator | 46 | 46 | 每 point 的 write-vs-bound |
| 三数组 | 6,394 | 6,394 | 46 次稳定性＋3 个跨指针 access pairs 各 46² 次 |

重复 numeric 删除没有减少这些地址比较；numeric 使用的其它指令不在此计数内。
Read/read pairs 也被旧强 `NonAlias` 契约要求，是可改进的算法／证明选择。
一般 compact footprint／projection、扩大 useful acceptance 和独立计时仍待完成。

## OLO 具体源覆盖与下一项

[Figure 2 适配](olo-figure2-coverage.md)及其模型新增两个模式共 **16 次** native 调用，
原三层行为保持，包含 alias 改变 shape、一 word 空外层和加一回绕。
两模式的 `bt_excerpt` emitted body 完全相同，没有安装 guard／candidate。
当前 main grammar 不能描述 load＋1 根和 loaded child 的组合，明确记录
`optimizer_coverage = not-supported`，不以不优化的运行称 OLO 通过。

适配是 fixed flat Mint32 layout 和替换 body，非完整 NPB BT。原 kernel 的优化／性能／
人工工作未评估。下一步同时推进 compact sufficient conditions 与 checked expression-header／
dependent child 覆盖，不通过手工缓存原 source bound 消除困难行为。

## 产物与复现

| 产物 | SHA-256 |
| --- | --- |
| `build/loaded-affine-multi-reduced/proof/report.json` | `cba146e6ddb318a1653ae2e488eb74a2a0b28741c428a6ee9c92b95f6d8a248e` |
| `build/loaded-affine-multi-reduced/compiler/.guard-build.json` | `3d87e5695b509d038a72c81ee3d41885891910ec6870cc0b5057b4024af0d950` |
| `build/loaded-affine-multi-reduced/native/report.json` | `fec12a67f1efa8db241d144d8bdbbabc082d79e714394caf92df567f84ced0cc` |
| `build/loaded-affine-multi-reduced/native/path-report.json` | `70a8158e48e494f18f8036ef94b2e4b8cad1c49c05cb979417232769736af97d` |
| `build/loaded-affine-multi-reduced/guard-work/report.json` | `ba32432fdec899b0dfb57b6e7bd0ecc8bc9a0d7594de9bcfbe7450f20808ca9a` |
| `build/loaded-affine-multi-reduced/olo-figure2/report.json` | `eda299b62ee8c09b08ea54b6fc067f1b52b7f58209ded1a12b52f48761fc8b98` |

在已有继承 proof／冻结 native 基线与 toolchain 下：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make loaded-affine-multi-native
make loaded-affine-multi-validate
```

Make 当前入口使用独立 reduced 产物；旧 build／报告／binary 不覆盖。
验证核对当前 source/object、提取 driver/native modules、compiler、C、Clight、assembly、binary、
输出和 probes 的摘要；旧对照仅使用已核对 native artifacts，旧 proof/object 是历史绑定。
CompCert v3.18、Rocq／Stdlib 9.2 保持，无新增全局公理。
