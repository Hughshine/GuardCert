# 双 loaded store-list：完整调用成本

2026-10-08。继 [readonly probe 后继](word-nested-store-probe-memo.md)后，
本阶段比较同一 C 源码经 source、shared setup 和 probe memo compiler 生成
的完整调用。结果没有显示相对原程序的净收益：新 guard 的普通 2×3 接受
输入约为 source 的 11.45–11.61 倍，8×8 输入约为 186.58–226.66 倍。
Memo 相对旧 guard 在这些接受输入上较快，但仍须降低主要扫描成本。

本阶段没有新语义定理或 compiler；复用冻结的两套 compiler、source/model/
candidate、region guarantee 和 Csem→Asm 证明。完整 goal 保持 active。

## 输入、执行与验证

三种 profile 为固定 stride 行布局、固定 stride 列布局、参数 stride 行布局；
两者 bounds 均从内存读取，body 是两个有依赖的 Mint32 stores。实际两轴
Pluto、2×3 tiling 和 per-statement prepared codegen 从 marked C 自动运行。
各 guarded config 安装一个 region，disabled source 安装零个。不加虚拟轴，
用户不提供目标 AST 或语义 callback。

每个 profile 的九组输入：

| Case | 参数/含义 | 新旧 guard 的观察路径 |
| --- | --- | --- |
| small-accepted | start=0, n=2, m=3, alpha=1, ld=16；分离数组和 headers | candidate |
| cap-accepted | n=m=8，其余同上 | candidate |
| word-wrap | n=3, m=2, alpha=2147483647 | candidate；RHS 保持 modular32 |
| alias-refusal | 2×3，A=B | cached source |
| header-refusal | start=1，2×3 | original loaded source |
| header-alias-refusal | 2×2，K=B，alpha=-2；首次 store 改变 child bound | original loaded source |
| setup-refusal | n=9, m=1，超过 cap 8 | cached source |
| outer-empty | n=0, m=99；A/B/K=NULL | outer-empty；不读 child 或 arrays |
| child-empty | n=2, m=0；A/B=NULL | cached source；不执行 body |

初始化一个 1,024-word arena，A 位于 word 64，普通 B 位于 word 320，H/K
位于 words 0/1。每次调用前重置 headers，header-alias case 将 K 重置为 2；
数据数组不重置。计时在一个 warmup 后进行，包含每次 header reset，以及
完整 capture、header/numeric/alias checks、candidate/fallback、public exit。
初始化、printf 和输出检查在计时之外。

准备阶段有 243 次未插桩 assembly 完整输出检查（3 profiles × 3 modes ×
9 cases × 3 repetition counts），以及独立 81 次 printed-Clight/GCC 完整
调用诊断。Repetition counts 为 0/1/3，另有一次 warmup；不是 243 个单次
调用。原 C 的 GCC `-O0 -fwrapv` 输出也与独立源模型匹配。

源模型逐点实际重读 H/K，执行两个有依赖的 modular32 stores，并检查公共
迭代变量、调用前记录值及全部 1,024 words。稳定分支输入的重复执行使用
独立闭式结果；先对 1–4 次顺序执行交叉核对。Header-alias 输入在重置 K
后完整调用是幂等的，也核对了第二次执行。每个 calibration 和测量批次
保留 warmup 和 repeated-final 输出并再次核对，避免只测 checksum。

## 配对计时协议

AMD Ryzen 7 7800X3D、WSL2/Linux、CPU affinity=0。每个 batch 启动新进程，
使用 C `clock()` 测 process CPU time；全部 timed code 来自未插桩 CompCert
assembly，GCC 只 assemble/link。实际 assembly 中的 warmup 和循环内
`loaded_pair` calls 都检查存在，未让 GCC 重新优化 timed kernel。

每 profile/case/mode 独立校准 repetition count，目标至少 0.1 秒。三十轮
中每轮随机排列全部 81 个 batches，seed=20261008，共 2,430 个 observations。
最短实测 batch 为 0.095454 秒，协议下限为 0.05 秒；没有删除样本或 outliers。
下面 ratio 是逐轮配对 ratio 的 median，不是两个 ns medians 相除。
原始 samples、stdout、calibrations、IQRs 都绑定在报告中。

## 结果

行布局的完整 ns/call medians：

| Case | Source ns | Shared ns | Memo ns | Memo/source 配对 | Memo/shared 配对 |
| --- | ---: | ---: | ---: | ---: | ---: |
| small-accepted | 9.419 | 114.963 | 109.723 | 11.612 | 0.9534 |
| cap-accepted | 44.194 | 9663.742 | 9219.501 | 208.128 | 0.9550 |
| word-wrap | 9.694 | 127.074 | 119.069 | 12.301 | 0.9437 |
| alias-refusal | 9.416 | 104.207 | 97.885 | 10.448 | 0.9417 |
| header-refusal | 7.824 | 7.820 | 7.960 | 1.016 | 1.0124 |
| header-alias-refusal | 6.457 | 7.199 | 7.117 | 1.102 | 0.9893 |
| setup-refusal | 13.477 | 20.512 | 21.292 | 1.577 | 1.0400 |
| outer-empty | 2.538 | 3.377 | 3.320 | 1.319 | 0.9888 |
| child-empty | 3.628 | 5.522 | 5.416 | 1.499 | 0.9796 |

其他两种布局的完整配对 ratios（原始 ns medians 也在报告中）：

| Case | Column memo/source | Column memo/shared | Variable-row memo/source | Variable-row memo/shared |
| --- | ---: | ---: | ---: | ---: |
| small-accepted | 11.446 | 0.8401 | 11.589 | 0.9500 |
| cap-accepted | 186.577 | 0.7686 | 226.662 | 0.9517 |
| word-wrap | 12.068 | 0.8632 | 11.756 | 0.9365 |
| alias-refusal | 10.114 | 0.8289 | 11.026 | 0.9330 |
| header-refusal | 1.030 | 0.9969 | 1.294 | 0.9930 |
| header-alias-refusal | 1.112 | 0.9981 | 1.097 | 1.0033 |
| setup-refusal | 1.704 | 1.0040 | 2.278 | 1.0099 |
| outer-empty | 1.308 | 0.9770 | 1.312 | 1.0084 |
| child-empty | 1.645 | 1.0844 | 1.425 | 0.9789 |

[完整调用图](../paper/figures/word-nested-memo-cost.pdf)显示所有输入的 paired
cost/source median 和 IQR（descriptive dispersion，不是 confidence interval）。
没有一个新版本 case 的 median cost/source 小于 1。也保留了相对旧版本的
回退 regressions，例如 column child-empty +8.44%、row setup-refusal +4.00%。
当前数据不构成一般 workload profitability，也不能定量拆分 setup 或 alias
对 CPU 的独立影响。

独立 GCC/Clight 诊断计数包括整个 guard 的 `if` 求值，跳过 candidate/source
body，另计 numeric setup。普通 row 的 2×3 accepted 为 738/33→720/15
（total/setup）；8×8 为 71,252/33→71,234/15。Alias-refusal 仍为
738/33→720/15：flag 已拒绝后，既有 pair scan 继续遍历。各 case/profile
扣除 setup 后的新旧计数相同，完整输出及 paths 相同。这些是 Clight 测试
次数，不能解释为 assembly 指令或 cycles。

Linked `loaded_pair` bytes（source/shared/memo）为 row 113/1442/1344、
column 113/1426/1329、variable-row 122/1594/1471。静态缩小及 setup 次数
定理成立，完整成本验收仍失败。相比完整 OLO 需求，一般 affine domains、
三 loaded/literal axes 与 dynamic layout 的联合源族、其他 scalar/chunks、
真实大 benchmark 和作者负担仍是独立缺口；不能把其他实例的能力相加。

## 对计划与责任的影响

下一阶段优先紧凑 alias 条件。先针对 checked 相同 affine access maps 的
矩形域构造有限差值空间：每个 point pair 的坐标差有一个域内 canonical
pair。若 canonical pair 的真实指针 equality 可以证明覆盖所有 point pairs，
检查数可从 `(n*m)^2` 降为 `(2*n-1)*(2*m-1)`。这是待实现/证明的设计，
不是当前 compiler 的能力或复杂度定理；template 不匹配应复用原 scan。
首次 alias refusal 停止扫描也值得实现，但不能代替接受路径的降低。

| 提供方 | 下一阶段必须交付的证据 |
| --- | --- |
| Domain/优化库 | template eligibility、canonical coverage、实际地址对应、接受蕴含现有 restricted nonalias；不是仅证明整数式 |
| Clight 条件服务 | 原 source 对每个 canonical read/comparison 的许可；实际循环/算术不溢出、flag/fresh cursors 的 execution、actual-exit/public transport |
| Factory/实例接入者 | 新条件接原 candidate 和 region guarantee；自动资源与 scope，实际 C frontend/extraction/native/context |
| 语言 host | 复用现有 progress、boundary、placement、private declarations 和 backend；若新语法/出口越界才新增对应证明 |
| Kernel | 继续消费和组合局部证书；不加入 pointer/affine 语义 |
| 支持族源码用户 | 仍只给 marked C 和策略；不提供同 block 假设、语义 callback 或局部证明 |

Clight 的不同 allocation pointer ordering 可无定义。新的条件须使用有 source
许可的 equality 或显式语言 evidence；现有 common-base envelope 可复用，
不能把任意跨 block interval comparison 当作安全操作。完成 actual encoding
和 compiler 接入后再测接受/拒绝/full-call 成本；同时保留 general affine
source/scalar 和完整 OLO 功能，不以无限增加小 fixture 延后成本验收。

## 冻结报告与复核

| 报告 | SHA-256 |
| --- | --- |
| `build/multi-word-nested-memo/cost-prepared-v1/report.json` | `b75167b9271a55da3df0ff809ab38415cbb6a57cdace79c79518e529489f1533` |
| `build/multi-word-nested-memo/cost-v1/report.json` | `7d7067e047ad7af9b58451047ae5df6d275554ae5e2b44989c19752e68828124` |
| `build/multi-word-nested-memo/cost-plot-v1/report.json` | `2a57836ea2ead8e9b4fbb35fb99300486feab1b8f28864cc121c69032b262795` |

本 workspace 的只读复核命令（不重新计时或重编已有 compiler）：

```sh
python3 scripts/prepare_word_nested_store_memo_cost.py --validate
python3 scripts/measure_word_nested_store_memo_cost.py --validate
python3 scripts/plot_word_nested_store_memo_cost.py --validate
```

这三个新 helper 的成功 checkpoint 会验证完整 binding 链与输出；不覆盖
已有 proof、compiler、native、work 或 timing reports。全新环境需要先按照
前阶段文档构建其 dependency checkpoints，不将本机命令当独立完整 artifact。
本次不重跑旧 proof/native 审计。计时不包含 compiler/proof/extraction setup，
不测 compile time/作者时间，不隔离 core，不代表 benchmark 输入频率。

论文后继 checkpoint 为 `build/paper/word-nested-cost-v4/`，纳入图与上述负面
结果。`word-nested-cost-v1/` 的离线失败日志保留：缺 `graphicx.sty` 缓存；
`word-nested-cost-v2/` 的失败日志也保留：sandbox 禁止 bundle 的 DNS。
`word-nested-cost-v3/` 补齐资源，但新段落有 overfull box；日志和 PDF 保留。
后继修正该段并用完整缓存构建，不重跑任何研究实验。
