# 紧凑出口：与相同 guard 的 shadow 版本配对计时

2026-10-07。[紧凑出口 compiler](nested-compact-exit.md)的完整调用，使用同一
literal-15 固定布局 C、候选 profile、guard、调用边界，与 source 和前一版
single-scan same-word shadow compiler 比较。前一版的入口为
`compile_ncs_stability_regions`，新入口为 `compile_ncs_compact_regions`。
这次的 shadow 对照也接受同值 header aliases；不同于上一份成本报告中
scans-only 对照的 alias 回退。两份正式报告分别保留，数据没有合并。

## 协议和结果

30 轮、8 个输入、5 个版本，共 1,200 个 fresh-process CPU batches。协议与
前阶段一致：seed=20261007，CPU 0，C `clock()` process CPU time，目标每批
200ms，全部至少 100ms；AMD Ryzen 7 7800X3D／WSL2 Linux 5.15。正式计时不与
proof/extraction/native/paper build 重叠，被计时的 CompCert 汇编没有插桩。

每次调用先重置 aliased headers，该工作计入时间，避免原来的拒绝输入随后
变成接受输入。每批前后按独立 source-word model 核对完整 A/B/C、headers、
公开 counters 和上下文 markers；初始化与核对在计时外。原始 batches、IQR、
每轮相对于 source 的比值及校准样本全部保留，未按快慢挑选正式样本。

下表为 median ns/call。旧 shadow 列使用**相同 guard 的 interchange**。

| 输入 | Source | 新 Identity | 新 Interchange | 新 Tile 2×3 | 旧 Shadow interchange |
| --- | ---: | ---: | ---: | ---: | ---: |
| 独立 headers，同值 15 | 911.1 | 804.3 | 1229.8 | 1358.2 | 1521.1 |
| shape=a，同值 15 | 910.1 | 802.5 | 1230.0 | 1352.1 | 1515.1 |
| shape=a+5，同值 15 | 912.0 | 803.9 | 1228.2 | 1346.3 | 1505.9 |
| 独立 headers，raw=5/7 | 158.4 | 361.9 | 907.2 | 1216.2 | 938.2 |
| shape=a，raw=12/13，域增长 | 913.8 | 803.4 | 839.8 | 806.1 | 875.2 |
| 非零 row=1 | 854.8 | 745.7 | 757.0 | 744.9 | 811.9 |
| 空 outer，单 cell header | 2.5 | 3.4 | 3.3 | 3.5 | 3.4 |
| 超 profile，root count=17 | 973.9 | 839.8 | 854.4 | 843.1 | 916.7 |

同值独立输入的新 interchange 比配对 shadow 对照便宜约 19%，但仍约为 source
的 1.35×；tile 为 1.49×。Identity 为 0.88× source，这是该输入上的完整
lowering/backend 结果，没有证明一般 identity rewrite 都会加速。非同值的
6×8×5 输入中，interchange 约 5.73× source，tile 约 7.65×。回退版本有时也比
disabled source 快：版本的代码布局和 backend 结果一并改变，不能把差值解释
为纯 guard 或纯 shadow 的 CPU 成本。这些负结果与例外没有删去。

这里没有代表性 benchmark 收益、CI、break-even、真实 workload 的接受频率
或混合路径收益结论。实验说明该候选实现改动降低了部分完整调用成本；它
没有为一般 interchange/tiling 建立净收益。

## 检查工作、代码和编译成本

另对打印 Clight 的实际 guard prefix 作 GCC diagnostics，停止在最终分派前，
核对没有改变输入内存。新 interchange 和 shadow interchange 的接受结果、
prefix 条件求值数与 header loads 在八个输入上逐项相同：

| 输入顺序 | 接受 | Prefix decisions | Header loads |
| --- | --- | ---: | ---: |
| 三个同值输入（各自） | 是 | 17 | 2 |
| 非同值独立输入 | 是 | 900 | 2 |
| header 改写、域增长 | 否 | 37 | 2 |
| 非零 row | 否 | 3 | 0 |
| 空 outer | 否 | 5 | 1 |
| 超 profile | 否 | 12 | 2 |

它们不是机器操作数，不包含最后一次分派。验收脚本显式检查新／旧两列相同。
Kernel bytes 为 source 161、新 identity 587、interchange 626、tile 719、shadow
interchange 644。单次 warm program compilation 约为 0.032/0.032/0.615/1.617/
0.667 秒，link 单列；不是包含 proof/extraction setup 的 clean-build 成本。

## 绑定与复核

- 完整报告：`build/nested-compact/cost/report.json`，
  `540f83698417f637a8b35ddf9198322f30becf04833a9e80b5010d21513f294a`。
- Raw batches：`build/nested-compact/cost/samples.jsonl`，
  `ef253bdad423803349f07f2502477d8047e5940286bf73bfcb7a0a8fad004fba`。
- 新 compiler：
  `7cd55f3379f40e3b6a324554077c44ff24abf535dcb3b18d6d044a61b6cb7529`。
- Shadow compiler：
  `cf565f8f8374af84631e08878cb8f67ee56b44cd16ba884a0b2eae329a0d8a59`。

报告绑定两版 proof/native 报告、源和 toolchain、五版 assembly/binary/dump/log、
diagnostic artifacts 与所有 helper sources。复核已经通过：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_nested_compact_cost.py --validate
```

生产脚本拒绝覆盖既有 timing report。下一项继续压缩非同值 stability／多数组
alias 的工作，分开研究候选代码成本、真正有收益的 kernel 和更广 source class。
