# 从 body guards 推导运行时上界，并接入完整 compiler

本记录面向增加 domain 服务的优化器作者。它接在
[source-aware 整段接入](double-tree-source.md)后，关闭 tricky3 的固定 cap 空转。
[证明摘要](double-tree-pruned.json)与[运行／成本摘要](double-tree-pruned-native.json)
分别绑定 Rocq 端点、实际 compiler、生成代码及运行证据。

## 服务提供什么

`PolCertGuardedBodyPruningFor` 在已有 Loop model 上实例化，提供：

```text
quiet_bounds body = Some [B1,...,Bn]
  -> all Bi(env) <= x
  -> executing body at x leaves its state unchanged

prune bounds statement
  -> under env_within bounds, preserves each finite source execution
```

Guard 的上界来自既有 `guard_upper`。一个 sequence 要求每个成员都能建立
quiet suffix，合并它们的义务；遇到不能处理的指令／结构保留原循环。
服务优先使用内层 guarded bodies 的证据，不让外层 enclosure cap 遮住更小的
child bounds。它去除相同表达式，再检查所有 proposed upper intervals 均低于
原上界的 lower interval。这个充分条件保守，主要适用于固定 enclosures；
它不提供一般相关变量的比较推导。

互补 LE／Not-LE guards 选择 bound list 的最大值。两个不同 bounds 的输出是：

```text
if B1 <= B2: loop [lower,B2) body
if !(B1 <= B2): loop [lower,B1) body
```

数学证明支持有限 bound lists；当前 AST 构造会复制分支，多个不同 bounds 时
可能指数增长。它不是紧凑 max lowering 或 OLO compact entry-condition 算法。
语义服务位于 domain 库，最小 kernel 没有增加具体 Loop 或 machine semantics。

## 验证链与责任

最终 polyhedral checker 继续验证 affine reference。新 candidate compiler 先
消费 `prune_execution`，再把实际 pruned Loop 交给已有 machine lowering。
`Not` 和动态 division bounds 不要求重新被 affine extractor 接受；从已检查
reference 到这个实际 target 的证明由新 postpass 提供，不能用旧最终 checker
的 theorem 直接替代。Native adapter 只计算同一 extracted pure postpass 的
诊断 receipt，并返回原 reference，没有 semantic extraction override。

Domain 负责 quiet-suffix 义务和 runtime bound selection；语言继续负责 safe
captures、machine expression／instruction execution、private/public frame 和
准确源出口。新 factory 与当前程序 host 消费这些证据，终点为
`DoubleTreePrunedCompiler.compile_selected_pruned_double_tree_program_correct`：
原当前 Csyntax 的 Csem→Asm backward simulation。Kernel／host laws 不变，
C 用户不补动态 model callbacks。Postpass 的有限 forward preservation 与原
独立 source progress 继续区分，不声称 standalone full equivalence。

五个新模块603行，查询12端点，1 closed、最多42 inherited globals；无新增
global assumptions。十个 module attempts 中五成功、五失败，全保留。审计绑定
10,547文件；实际 native compiler 为 `native-pruned-v1`。

## 实际代码与运行

原三个程序五配置15/15完整输出匹配。三个完整 marked regions 各安装一次；
unmarked／wrong-shift 均零安装。Runtime tricky3 adaptation 保留原计算区域，
同一 profile[0,32] binary 的21/21 inputs匹配。Reference有四个point positions，
实际pruned target有一个outer和两个互补inner loops、七个positions；仅一个inner
分支执行，三个源loops仍为fallback。没有general many-to-one piece checker。

十一条GDB路径在未改assembly／未插桩binary上通过。Empty outer跳过child
headers，refusal短路后续checks，四个scalar stores的完整次数／变化顺序保持。
实际 body-entry comparison 位点给出：

| 输入 (pointc,clusterc,dims) | 前序 cap32 body 次数 | 本版 body 次数 |
| --- | ---: | ---: |
| (1,0,0) | 32 | 0 |
| (1,0,7) | 32 | 7 |
| (2,3,5) | 64 | 10 |
| (3,5,2) | 96 | 15 |

两个动态 loop header 的观察还包括退出检查：选择 dims 时次数为
`pointc*(dims+1)`，另一个 header 为零；选择 clusterc 时相反。
这不同于仅由静态 Loop AST 推测工作，也不是 CPU guard 成本。

## 成本对照及当前缺口

同一 argv C 计算用 profile[0,4096] 编译为前序cap版、本版和同一后端的
unmarked source。Unmarked只删除selection markers。六输入／三版本／七个
随机顺序batches的126次完整outputs全匹配；完整调用没有截去guard、fallback
或public exits。计时是**完整子进程 user+system CPU**，还包括startup、argv、
initialization、四scalar完整digest和printing；不是kernel-only函数计时。
未做CPU pinning或frequency控制。先前仅cap／pruned的84次结果也保留，不能
将其替代original source基线。

| 输入 | Cap median ms | Pruned median ms | Source median ms | Pruned/source paired ratio median |
| --- | ---: | ---: | ---: | ---: |
| (4096,0,0) | 27.063 | 0.509 | 0.582 | 0.995 |
| (4096,3,5) | 26.998 | 0.676 | 0.531 | 1.157 |
| (4096,4096,4096) | 26.638 | 26.900 | 14.772 | 1.837 |

最后一列是七个配对ratios的median，不是前三列medians相除。小输入、empty和
fallback的sub-ms结果受startup与测量波动影响，不推出明确收益。Max pruning
消除了低child counts时的cap空转，但满domain仍约慢于source 1.84倍，未满足
有用sequential优化效果的验收。Emitted bodies仍有重复outer和child membership
checks；下一步需要在loop／branch事实下进行已证明的残余条件处理，验证actual
lowering的变化，再对照source成本，不能只比较一个较慢的前序guarded版本。

General codegen-piece forward/progress、ISS、真正tiling／其他域变换、OLO
entry-condition construction、共享checks memoization，以及完整62例与CGO17
原程序／更大tiers仍未完成。此checkpoint不重算aggregate source coverage，
不完成整体goal。

## 复核

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_double_tree_pruned.py --validate
```

`scripts/summarize_double_tree_pruned.py`绑定冻结proof、native、observer与cost
reports。`compare_double_tree_pruned_source.py`记录实际source基线和时间范围。
