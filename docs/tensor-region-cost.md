# Tensor：紧凑检查与完整调用成本

本轮对已闭合的 [tensor compiler](tensor-region-compiler.md) 测量实际 Horner RMW
源。同一个 compiler 的 disabled、identity、interchange 和2×3 tile，使用相同
源、默认 cap32／stride<1000 profile、target 与 backend 配置。历史 proof/native
reports保持，不把计时或插桩当作新的普遍正确性证明。

## 协议

30轮、8输入、4配置，共960个 fresh-process batches；seed20261007，CPU0，C
`clock()` process CPU time，目标每批100ms，实际全部至少99.452ms。
环境为 AMD Ryzen 7 7800X3D／WSL2 Linux5.15。正式计时与 proof、extraction、
native compilation 或 paper build 不重叠。被计时的 CompCert 汇编没有插桩，
保留实际 `tensor_single` call boundary、guard、分派、candidate／fallback 和
public counters／context marker 写回。

每个 batch 在计时外初始化6,144个 words，先 warmup 一次，计时后按真实调用
次数计算全部预期 words、public counters 和 markers。RMW 在反复调用中累积，
按 word32 模型处理溢出；不把数组重置放入每次调用的时间。两个完整结果摘要、
CPU ticks、校准样本、raw batches 和配对比值保留。测试 profile、热缓存和重复
输入是本实验的范围，不是实际 workload 的接受频率。

## 完整调用结果

下表为 median ns/call，IQR及每轮配对比值在 report 中。
输入依次列 `start,n,ld,columns,components,alpha`。

| 输入 | 接受 | Source | Identity | Interchange | Tile2×3 |
| --- | --- | ---: | ---: | ---: | ---: |
| 0,3,31,2,5,7 | 是 | 23.7 | 24.5 | 27.6 | 29.7 |
| 0,31,31,31,5,7 | 是 | 3,039.8 | 3,093.6 | 3,497.0 | 3,268.6 |
| 0,15,63,15,5,MAX | 是 | 719.0 | 756.5 | 876.6 | 759.5 |
| 0,2,31,32,5,-2 | 否，坐标覆盖 | 206.7 | 190.9 | 190.5 | 198.6 |
| 1,31,31,31,5,7 | 否，root非零 | 2,951.7 | 2,719.7 | 2,706.0 | 2,841.1 |
| 0,0,1001,99,99,MAX；null output | 否，outer空 | 3.1 | 3.3 | 3.3 | 3.7 |
| 0,31,31,31,0,7 | 否，inner空 | 459.1 | 488.3 | 471.6 | 807.5 |
| 0,1,1001,2,5,7 | 否，stride profile | 11.0 | 11.1 | 11.0 | 11.5 |

三个接受输入的 interchange 配对成本为 source 的1.164／1.144／1.220倍；
tile为1.248／1.077／1.058倍。当前源本身按行连续访问，没有在这些输入观察到
重排收益。Identity 接近 source，也不等于“guard只有两者相减那么贵”。几个
回退版本比 source快；版本化同时改变 backend／code layout，差值不能解释为
纯 guard 成本。所有 slowdown 和这些例外均保留。

这里没有代表性 benchmark 收益、confidence intervals、break-even 或原 BT
性能结果。后继应测试使重排有利的实际地址／遍历次序，并沿用相同证明服务，
同时推进 source grammar／loaded-bound 的功能覆盖。

## 检查工作与代码分开记录

另对实际打印 Clight 的 guard prefix 作 GCC diagnostics，停止在最终分派前。
Prefix保留源在 guard 之前的 temp 初始化和 `tensor_pre += 7`，核对数组完整
不变、pre107／post200。这些是诊断程序的结果，不是生产汇编操作数。

三个配置逐项相同。实际 prefix没有 loop扫描，也没有 input-array load：

| 对应输入 | 源迭代点数 | Prefix条件判断 | 接受 |
| --- | ---: | ---: | --- |
| small | 30 | 39 | 是 |
| dense | 4,805 | 39 | 是 |
| strided／wrapped | 1,125 | 39 | 是 |
| coordinate refusal | 320 | 31 | 否 |
| nonzero root | 4,650 | 1 | 否 |
| empty outer | 0 | 2 | 否 |
| empty inner | 0 | 6 | 否 |
| stride profile | 10 | 21 | 否 |

这说明当前具体 guard 没有 pointwise 工作；39次源级判断中包含常量条件和
重复 profile事实，backend可能消解其中一些。它不证明任意 affine guard 都是
常数成本，或每个判断对应一个机器 branch。

Single-region linked function bytes为 source218、identity622、interchange624、
tile870。一次已构建 compiler 的 warm program compilation 约为0.064／0.032／
3.220／8.080秒，link另列；不含 proof/extraction。没有用这些时间推断一般
编译复杂度或把 code size 当作 runtime cost。

## 绑定与复核

报告 `build/tensor-region-factory/cost/report.json`：
`80459c66b80689c1b348677a17330d46d2c4453558765d5e2e629a2c3ba9bc49`。
Raw batches `samples.jsonl`：
`4b6445566d331685af2261940470f226713fd2a07a43aa26f7b17072560ea4b9`。

报告绑定原 proof/native、完整 compiler stamp、源、toolchain lock、四份assembly／
binary／dump／logs、diagnostic artifacts 和全部 helper。生产脚本拒绝覆盖既有
timing report；数组和markers预期按本次重复次数独立生成。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_tensor_region_cost.py --validate
```

[证明责任清单](tensor-proof-ownership.md)记录自动生产与尚需实现的证明，
[OLO 对照](olo-tensor-comparison.md)记录本实验与论文验收之间的功能缺口。
