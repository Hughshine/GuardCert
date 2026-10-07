# 按列访问 tensor：完整调用与检查工作

此实验使用[两种坐标次序的完整 compiler](tensor-coordinate-order.md)，测量其中
`((j*ld)+i)*5+k` 的单 region 函数。Source 循环次序仍为 `i/j/k`；interchange
改为 `j/i/k`。它复用原 tensor 整程序定理和原生矩阵，不修改 kernel 或证明。
前一[按行访问实验](tensor-region-cost.md)的所有负结果和 artifacts 保持。

## 单独的 profile 与协议

本轮明确设置 count cap32、`stride<2048`，而不是前一实验的 `stride<1000`。
该 profile 仍由数据 checker 和 safe guard compiler 核对，允许 `ld=1024` 的输入。
Disabled／identity／interchange／tile2×3 都使用这一 compiler／配置／source。
不能用不同源和 profile 的两轮差值测量收益。

30轮、8输入、4配置，共960 fresh-process CPU batches；seed20261007，CPU0，
C `clock()` process CPU time。每批目标100ms，实际最短92.829ms；正式计时与
proof、extraction、compiler/native/paper build不重叠。运行的是未插桩 CompCert
assembly，保留实际 function call、guard、dispatch、candidate／fallback、公开
iterator 恢复和 pre/post 写回。

每批在计时外初始化160,000个 words、warmup一次并输出完整结果。计时之后，
按该批真实调用次数独立生成全部160,000个预期 words、公开 counters 和 markers，
逐项核对，再记录结果摘要。RMW 不在每次调用重置；word32 溢出和坐标重叠的
重复访问按实际地址 multiplicity 计算。校准、全部 raw samples、IQR 和每轮配对
比值保持，没有删除 slowdown。缓存预期结果只减少 Python 核对工作，不进入被
计时的 C 程序。

环境仍为 AMD Ryzen7 7800X3D／WSL2 Linux5.15／GCC11.4，热重复输入。`ld=1024`
的布局用于测试较大跨行间隔；没有硬件计数器证据将成本差异归因于特定 cache
层或事件。这不是原 BT／Polly benchmark、真实 workload 频率或 break-even 实验。

## 完整调用结果

下表为 median ns/call。括号后的输入顺序是 `start,n,ld,columns,components,alpha`。

| 输入 | 接受 | Source | Identity | Interchange | Tile2×3 |
| --- | --- | ---: | ---: | ---: | ---: |
| small：0,3,31,2,5,7 | 是 | 22.9 | 24.2 | 24.0 | 29.1 |
| dense：0,31,31,31,5,7 | 是 | 3,069.8 | 3,059.6 | 3,042.8 | 3,249.9 |
| 大stride／wrap：0,31,1024,31,5,MAX | 是 | 4,054.2 | 3,975.5 | 3,108.1 | 3,639.3 |
| coordinate：0,32,31,2,5,-2 | 否 | 210.2 | 198.4 | 197.3 | 196.4 |
| 非零root：1,31,31,31,5,7 | 否 | 2,961.5 | 2,755.7 | 2,763.2 | 2,747.1 |
| outer空／null：0,0,1001,99,99,MAX | 否 | 3.1 | 3.2 | 3.3 | 3.7 |
| inner空：0,31,31,31,0,7 | 否 | 463.6 | 490.8 | 487.3 | 492.1 |
| profile：0,1,2048,2,5,7 | 否 | 10.4 | 10.8 | 10.8 | 10.9 |

大stride接受输入的 median paired cost/source 为 interchange0.764、tile0.899，
即完整调用时间分别下降约23.6%和10.1%。Small 对应1.048／1.265；dense对应
0.990／1.060，后者没有置信区间支持一般或显著收益。完整调用包括实际 guard。
Identity 和回退版本也有更快／更慢的结果，code layout／backend 同时改变；
不能将 guarded-source 的差值当作纯 guard 成本。

## 检查、大小和编译成本

另对实际打印 Clight 的 prefix 诊断，停止在最终分派前。三个接受输入的30／
4,805／4,805个源点均执行39次条件判断，identity／interchange／tile逐项相同。
五个拒绝输入依次31／1／2／6／21次。Prefix 无 loop scan 和 input-array load；
逐项核对数组不变、pre107／post200。源在检查之前的 `pre += 7` 仍在 prefix内，
因此不把整个 prefix 称作无公开副作用的 expression。

诊断只计 Clight if-condition evaluations，包含常量／重复事实，不是生产汇编
操作数或 branch 数。没有从这一例推出任意 affine guard 的常数成本。

Single function bytes 为 source218、identity630、interchange629、tile878。
一次已构建 compiler 的 warm program compilation 分别约0.032／0.032／3.321／
8.080秒；link另记，不含 proof/extraction setup。没有用这些数据推断一般编译
复杂度或其他优化器的作者工作量。

## 复核与后继

Cost report `build/tensor-affine-region/cost/report.json` SHA256：
`b8cf24d69e7558c67040327eeeec1f0559b5c99b21bddaac6b9b86f09f88ad4d`。
Raw `samples.jsonl` SHA256：
`a662459c8ec2cbaf648421df679916049bf32f0213204f880272bcb7f8901e55`。
报告绑定 profile environment、原 proof、新 compiler stamp、新 native report、
source、toolchain lock、四组 artifacts、诊断和全部 helpers；生产脚本拒绝覆盖
既有 timing report。Validator 重新生成源／预期累积结果和 raw summaries 并核对
实际调用次数、覆盖和文件摘要。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_affine_region.mk cost
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_affine_region.mk validate
```

当前获得的是一个有实际整程序证明、有紧凑检查、在一个声明输入／profile上有
净收益的例子，同时保留两个源场景的负结果。更广泛功能、代表性收益、作者
工时和 source-only rebuild 均未由它完成。下一功能项是 literal-bound 的私有准备／
状态运输和 source-progress 接入，再实际组合 loaded bounds 与动态 tensor布局。
