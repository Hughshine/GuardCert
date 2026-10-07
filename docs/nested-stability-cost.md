# 单份 stability guard 的完整成本

2026-10-07，生产入口仍为 `compile_ncs_stability_regions`。本轮未改变 runtime compiler。
由 [成本脚本](../scripts/native_nested_stability_cost.py)编译一个 literal-15、固定
`80*row+5*column+component` 地址的 kernel；检查窗口允许 root/child counts≤16。
这是机制实验，不能代表 OLO benchmark 收益、源覆盖或真实 workload 接受频率。

## 完整调用计时

所有版本使用相同 C 输入、后端、调用边界与 header 重置。每次调用先重置两个
可能被 BODY 改写的 headers；该工作计入时间，避免第一次回退后后续调用悄悄
变成同值接受。每批在一次 warm-up 后计时，初始化和核对完整 A/B/C 数组、
headers/public counters/markers 在计时外；每个原始 batch 前后都通过独立源模型。

30 轮、8 个输入、5 个版本，共 1,200 个 fresh-process batches。每批目标 CPU
时间 200ms，全部至少 100ms；C `clock()` 记录 process CPU time，seed=20261007
打乱每轮顺序，pin 到 CPU 0。WSL2 Linux 5.15，AMD Ryzen 7 7800X3D，GCC 11.4
仅负责链接；被计时 kernel 是未插桩的 CompCert 汇编。正式采样期间没有 proof、
extraction 或 paper build。一次与证明编译重叠的早期试跑已中断，其部分数据
另存，不进入最终 30 轮；没有按快慢挑选正式样本。

下表为 median ns/call；IQR 和每轮相对于 source 的比值及全部原始 batches 在报告中。
旧版是同候选的 scans-only compiler；它在两个同值 alias 输入上仍回退。

| 输入 | Source | Identity | Interchange | Tile 2×3 | 旧 interchange |
| --- | ---: | ---: | ---: | ---: | ---: |
| 独立 headers，同值 15 | 909.9 | 1397.5 | 1503.4 | 1622.7 | 2725.1 |
| shape=a，同值 15 | 910.5 | 1394.9 | 1506.4 | 1628.0 | 795.3 |
| shape=a+5，同值 15 | 914.4 | 1390.8 | 1511.6 | 1624.5 | 854.2 |
| 独立 headers，raw=5/7 | 158.3 | 441.5 | 936.1 | 1142.8 | 918.2 |
| shape=a，raw=12/13，域增长 | 911.4 | 796.6 | 875.3 | 798.2 | 796.9 |
| 非零 row=1 | 853.7 | 745.0 | 811.5 | 757.5 | 742.6 |
| 空 outer，单 cell header | 2.5 | 3.2 | 3.4 | 3.4 | 3.2 |
| 超 profile，root count=17 | 967.7 | 841.5 | 917.7 | 858.9 | 842.5 |

同值独立输入的新 interchange 比旧扫描版本快，但仍比 source 慢约 1.65×；
即使 identity 也约为 source 的 1.53×。非同值 6×8×5 输入的新 interchange 约为
source 的 5.91×，tile 约 7.21×。更大的接受域和更便宜的 guard 没有自动形成
净优化收益。某些回退版本比 disabled source 快，这也是保留的实测结果；
差值包含完整 lowering/布局/backend 效应，不能把它叫作负的 guard 成本。

没有 bootstrap CI、break-even 或真实混合 workload 的收益结论。该 literal-store
例重在观察检查机制和语义责任，后继还需实际 kernel 与更广条件算法。

## Guard-prefix 工作与成本归因

另将实际打印 Clight 的 guard prefix 截在最终 source/candidate 选择前，以 GCC
诊断版统计所有 prefix `if` 条件求值与两项 header loads，并核对没有改变输入内存。
计数不包含最后一次分派、不包含每个算术操作，也不是机器指令或已验证的新 pass。

| 输入 | 新 prefix decisions | 旧 prefix decisions | 新/旧 header loads |
| --- | ---: | ---: | ---: |
| 独立 headers，同值 15 | 17 | 4673 | 2/2 |
| shape=a，同值 15 | 17 | 36 | 2/2 |
| shape=a+5，同值 15 | 17 | 54 | 2/2 |
| 独立 headers，raw=5/7 | 900 | 899 | 2/2 |
| shape=a，raw=12/13，域增长 | 37 | 36 | 2/2 |
| 非零 row=1 | 3 | 3 | 0/0 |
| 空 outer，单 cell header | 5 | 5 | 1/1 |
| 超 profile，root count=17 | 12 | 12 | 2/2 |

Numeric 是 first-path probe 加参数 interval tree，成本随 depth/parameters 增长，
并非逐 point 扫描。单数组 same-word 接受时 stability scan 被跳过，alias-only
code 是 `skip`：完整 guard 工作已与域大小无关。非同值及多个数组的扫描仍须改进。
这一核对纠正上一阶段文档中错误的“逐点 numeric”成本归因。

## 下一项由这些结果驱动

生产候选的 `affine_multi_candidate_code` 在执行候选后运行 `affine_shadow_source`
恢复公开 counters。虽然其 BODY 是空的，它仍遍历迭代域。既有库另有紧凑
`affine_exit_statement`，但其执行域不自动适用于空 child 或一般依赖 bound。
下一项针对已接受的固定矩形 nested 源，实际生产所需 exit-domain 与 frame，
证明替代 shadow traversal，再通过同例计时检验。不能把成本相减当作已证明的归因。

与此同时，非同值 stability 和多数组 alias 的紧凑 footprint 条件、更广 affine
source/参数域变换、动态 layout/delinearization、完整 BT 与作者工作比较仍在目标内。

## 证据与重现

报告 `build/nested-stability-shared/cost/report.json`：
`8490f3a6a2a03fa197e7a9c782b91fa712cf0d243b70522bd653dc0f296d0542`。
它绑定 C、五个 dumps/assembly/binaries/logs、diagnostic artifacts、raw samples、
工具链与既有 proof/native 报告。Kernel bytes 为 source 161、identity 611、
interchange 644、tile 755、旧 interchange 613；不能将它们当作执行收益。
Program compilation 约 0.032/0.032/0.665/1.567/0.615 秒，link 单列；这是已构建
compiler 的单次 program build，未包含 proof/extraction setup，不是 clean-build 成本。

```sh
python3 scripts/native_nested_stability_cost.py --validate
```
新实验用脚本默认目录运行；已有报告存在时拒绝覆盖。上述复核已通过。
