# 单份扫描、较大域与尚未消除的检查成本

2026-10-07，接续 `64232ee` 的 [same-word compiler](nested-stability-compiler.md)。
当前 source/candidate 格式、kernel、候选证书和语言 host 不变；改变实际条件代码，
增加较大域输入及独立原生证据。旧目录保留其历史产物，当前默认工具使用
`build/nested-stability-shared/`，旧阶段摘要校验不能再被称作当前源码的证明验收。

## 条件生成及证明责任

前阶段在两个缓存比较的失败分支各放一份 scan。本阶段生成：

```text
if (root_cache == Int.add(w, root_delta))
   & (child_cache == Int.add(w, child_delta)):
    private_result := true
else:
    原 stability scan（仅一份）
```

这里的 `&` 是两项 0／1 Boolean word 的 eager conjunction。它不是通用
short-circuit lowering；进入本段前，已有 capture／positive／numeric gates 保证
两个缓存都已初始化。两项均只读 private caches，不读取 header 或比较指针。
不成立时没有先写 result=false，scan 入口完全不变。

语言服务 [ClightInitializedBooleanAnd.v](../prototype/interface/ClightInitializedBooleanAnd.v)
显式要求两项的 int32 类型、各自实际求值得到 Boolean word，再证明实际 `Oand`
求值。Domain 的 `ncs_word_pair_expression_test` 从两个 cache bindings 生产这份
输入，证明结果等于原 `ncs_same_word_flag`。`ncs_word_or_scan_execution` 的接口
保持，实际 receipt→multi adapter→guard certificate→原 candidate preservation
certificate→语言 host→Csem→Asm 链直接复用。

该 language lemma 不是最小 kernel 的定律；独立查询为四项既有 baseline assumptions。
完整 compiler 沿既有 42-global baseline，kernel 闭合，无新增 global axiom。
这也说明优化条件不能只在“所有表达式都定义”时证明 Boolean 等价：前述
initialized operands 是语言 lowering 的必要前提。后项读取仍需前项许可的 check
应继续短路，不能使用这个服务。

原根比较失败时，前阶段只执行一项 equality；本阶段已定义的两个比较都执行。
它交换了少量 eager work 与扫描代码共享，不宣称运行成本在所有输入上下降。

## 用户与较大实例

源实例仅把 actual C BODY 的 literal 从 1 改成 15，并提出 count≤16 的 profile；
源码描述、候选及 checker 不变，没有新增用户提供的语义证明回调。新的 Rocq
fixture 核对 actual indexed BODY 的 word proposal 及 static site；它是验证示例，
不是每个 C 使用者都需手写的证明。

双 raw headers 同为 15 时，原源有 16×16×5＝1,280 次 stores。测试保留两个
alias layouts：`shape=a` 和 `shape=a+5`；同值 stores 保持两项 header 观察。
不同 raw words 下不假设稳定：`12／13` 与 `15／14` 的 header/data overlap 会
把原实际域增长到 16×16，本例明确验证这些输入执行原源回退。

较大矩阵还包含独立 header 的 6×8 域、one-cell 域、超 profile 的合法 17×16
回退、nonzero／negative row、单元素 root allocation 下的 empty outer、null BODY
pointer 下的 empty child，以及 header offset 的 signed32 wrap。参考模型逐次
读取实际 header，不能用初始缓存 rectangle 替代变化中的原程序。

这是已有固定 layout frontend 的更大输入及 constant-word 参数实例；没有增加
动态 stride、一般 affine source class 或完整 BT 支持。

## 实证

独立 audit：23 endpoints、598 required dependencies、897 source digests；
当前 entry 已提取与构建。原矩阵在新 compiler 上重新执行 762 assembly calls、
381 Clight dispatch calls。接受结果保持，interchange 仍为 51 fast／75 refusal。
另有同输入旧 scan-only compiler 的 127 assembly／127 Clight calls 和四个
未修改汇编 alias probes，保留之前 acceptance／fallback 对照。

同 source、mode、profile 的 constant-one 函数大小：

| 配置 | 前阶段双 scan | 当前单 scan |
|---|---:|---:|
| Identity | 728 bytes | 611 bytes |
| Interchange | 762 bytes | 644 bytes |
| 2×3 tiling | 867 bytes | 755 bytes |

前阶段二进制及 report digests 与既有记录核对；表格是实际 linked function size。
原 scan-only interchange 为 613 bytes。单 scan 消除了大部分新增代码，但不是
整份优化的 timing／profitability 结论。

较大矩阵四配置给出 60 新 assembly calls，另有旧 scan-only compiler 的 15 calls；
三配置给出 45 Clight dispatch calls，各为 6 fast／9 refusal。完整 A／B／C、
headers、三个公开 counters 和前后 markers 对照一致。九个 GDB probes 覆盖
independent／两种 header alias，在未修改汇编中得到：

| 配置 | Watched indices 写序 | 公开 counters |
|---|---|---|
| Disabled | 15,80,160 | 16,16,5 |
| Interchange | 80,160,15 | 16,16,5 |
| 2×3 tiling | 80,15,160 | 16,16,5 |

较大域中 tiling 的真实写序也得到区分；不是借小域相同写序证明候选路径。

十四次独立 diagnostic Clight calls 对照稳定性阶段：16×16×5 independent 输入
的 header pointer comparisons 2,560→0，新 cache comparisons 为 2；6×8 的
不同 word 输入保留 480 次 pointer comparisons 并增加 2 次 equalities；两个
改变 header 的 alias 输入保留 10／20 次 scan comparisons 并回退；超 profile
输入不进入本段。计数插桩由 GCC 执行，不是 verified pass 或 assembly 指令计数。

## 下一项的实际困难

2026-10-07 成本核对更正：先前此处将 numeric 检查说成逐点工作，这是错误的。
`affine_package_guard_code` 只执行 first-path probe 与参数区间 tree；其成本随
nest depth／parameter 数量增长，不随 iteration-point 数量增长。逐点工作来自
header-stability scan 与多数组的 alias-pair scan。单数组 literal-word 快捷接受时，
前者被跳过，后者实际生成 `skip`，因此这条路径的完整 guard 工作已经不依赖域大小。
拒绝快捷条件后仍可能扫描，且多个数组的 alias 检查需要另行处理。

已知 cache facts 仍可用于 certified static range derivation，但它主要消去冗余的
固定成本检查，不能被说成消除了这里不存在的逐点 numeric 工作。改变实际 guard
仍须保留 dependent capture 的读许可、原源码 domain、helper frame 及模型入口。
地址含额外参数的 BODY 不能仅凭 store word 跳过其范围检查。

完整 guard／program timing、条件接受域对照、编译成本和作者工作比较继续推进。
更多 source classes、参数域变换、动态 layout／delinearization 及完整 BT 适配
仍是完整目标的一部分，本阶段不缩减该目标。

## 重现

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/nested_stability.mk native
python3 scripts/probe_nested_stability.py
python3 scripts/native_nested_stability_large.py
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/nested_stability.mk validate
```

GDB probes 需要 ptrace 权限。旧 binary 是已核对摘要的对照产物，脚本不重新提取它。
当前 reports 绑定新 source／proof／compiler／helpers 和产物；旧 source-only
`1d3acc0` 路径的 readonly validate 仍通过，其结果不自动证明当前新入口 empty-build。
