# 运行时参数下标：从原 Clight 到完整程序

原 `fusion5` 的第二段读 `B[i+2][N-j+2]`，写 `C[i+2][j+2]`。
此前 decoder 只把 iterators 放进 access rows，因而拒绝原 `Evar N`。
本后继保留该 global read 和原运算树，把实际运行时参数 `n` 与迭代坐标
同时放进 instruction arguments。它复用已有 double instruction、layout、
真实 `Mem` load/store、polyhedral checker、private capture 和 scoped host。
没有把 `N` 的 initializer 当作原读取的替代，也没有改写原 benchmark。

## 责任与实际消费的证明

| 责任方 | 新证据及其消费者 |
| --- | --- |
| Language | `long_header_affine_execution` 连接原 `Evar` load、I64 temporaries 和表达式执行；access receipts 消费它 |
| Domain/source instance | `checked_double_header_source_shared_execution_iff` 连接实际 assignment 与现有 double memory model；nest theorem 消费它 |
| Domain/condition derivation | `double_header_row_profile_sound` 与 endpoint checker 推导所有 reached accesses 的数学范围；entry/model factory 消费结果 |
| Language/source instance | 首次读取许可来自原 source execution；实际 global-store frame 建立后续读取稳定性；capture/model transport 消费这些事实 |
| Domain/candidate instance | 最终 checker 验证恢复了参数 argument 的实际 candidate；guarded-execution theorem 消费 accepted capture、checker 和 Clight lowering |
| Language host/site | 已有 scoped host 消费 region contract、resources、public exits 和独立 progress；新 compiler 在实际 intermediate program 上组合到 Csem→Asm |

这些是实例实现者的证明责任。C 使用者仍然提供标注、程序和策略选项，不提供
逐 site 语义 callbacks。Minimal kernel 和 host 定律保持原接口。原执行是证明
的起点，运行时不会预执行原循环来决定接受与否。

源模型的 instruction arguments 为 `n :: coordinates`；candidate environment
仍使用已有的 `[q,n]` private parameter layout。`q` 是已验证安全 capture 的
ceiling quotient，最终 candidate checker 消费 `0 <= d*q-n <= d-1`。这两种
布局不能混淆：instruction 的参数 argument 不是新的 iterator。

`double_header_nest_canonical_source_model` 在其明确的入口、freshness、resolved
points 和 stable header 前提下，证明实际 Clight 的有限执行与 source Loop
有限执行的 iff，并给出精确 public iterator exits。Factory discharge 这些
前提后，`checked_double_header_raw_pipeline_execution` 才提供实际 source/model
桥。它不是独立的无限行为等价；source progress、region installation 和
backend simulation 另有证明。

## Condition 的表达力与限制

新的 access family 接受一个 global signed I64 header，以及由该 header、
signed I64 iterators、常量、加减、常量乘法形成的仿射下标。Parser 临时把
header 编码为一个 temp 只是解析办法；依据原 AST 的完整重建检查决定接受。
不同 header `M` 和 nonlinear subtree 保守拒绝。即使 `(i*j)*0` 数学上为零，
当前 decoder 也不会略过不受支持的运算子树。

对 row `a*n + sum(c_k*x_k) + b`，保持同一 `n` 与 `0<=x_k<n` 的关联。
令 `lo=sum(min(c_k,0))`，`hi=sum(max(c_k,0))`，得到：

```
lower(n) = (a+lo)*n + b-lo
upper(n) = (a+hi)*n + b-hi
```

两者都是 `n` 的仿射函数。静态 endpoint checker 检查 `n=1` 与提议 cap，
并证明所有 `1<=n<=cap` 的 reached accesses 位于声明的数组维度内。
Cap producer 的除法只是充分条件提议，checker 才是正确性依据；没有最优
cap 或最弱条件保证。`n=0` 的 reached-point 义务为空，source proof 和 public
exit restoration 单独处理这个情况。

原 `N-j+2` 的范围为 `[3,n+2]`。`B` 的第二维为 101，结合其他访问产生
cap 98。Closed examples 检查 cap 98 接受而 99 拒绝；native 只运行源程序
定义良好的输入，不用越界的 `n=99` 作为回退正确性实验。运行时 entry check
测试捕获值是否位于 `[0,cap]`，通过后才计算并捕获 `q`。

这里的数学 bounds 不等于 `Mem` 权限。Layout、global bindings、物理 span、
实际 load/store 和权限继续由已有 double memory instance 的证据处理。
I64 表达式定理中 `Int64.repr` 描述 modular execution，不宣称任意中间值
都不会 overflow。支持的是这个具体源族与既有地址编码的证明链。

## 实际 candidate 的第一次失败与修正

`native-v1` 已提取新 compiler，但原第二段的 candidate 被最终 checker 拒绝。
旧 untrusted adapter 把全部 instruction arguments 当成 iterators；新的 leading
argument `n` 因此错误产生 `n<n`，并使 prefix arity 不匹配。原完整输出仍匹配
GCC，但只有第一段安装成功。这个结果保留为失败证据。

`GuardSelectedDoubleHeaderQuotientV2` 在 proposal 内临时投影掉这个 parameter
argument，运行已有 iterator proposal 算法，再在最终 candidate 的实际 depth
恢复原参数。它先检查 leading argument 确实表示 `[q,n]` 中的 `n`。
投影与恢复均不受信任，同一个最终 checker 验证完整 candidate；没有新增
raw-to-adapted equivalence 公理。

Header phase 分别保存：

- `header-actual-raw.loop`：实际 codegen 结果；
- `header-iterator-proposal-input.loop`：临时投影后的 proposal 输入；
- `header-actual-generated.loop`：恢复参数后、交给最终 checker 的实际 candidate；
- `header-coordinate-proposal.txt`：参数与 iterator 的区分记录。

该 phase 的旧 `raw-generated.loop` / `generated.loop` 是临时 iterator proposal
文件，不能当作实际 compiler raw/final candidate。其他阶段继续按已有含义
保存这些文件。

## 接入与当前验证边界

新的 complete entrypoint 是
`HeaderLiteralQuotientTiledCompiler.compile_selected_header_literal_quotient_tiled_stable_program`，
其 `_correct` theorem 连接原 Csem 与生成 Asm 的 backward simulation。
顺序为 selected literal normalization、新 header-access pass、接收实际当前
program 的既有 quotient pass、既有 fallback passes 和 CompCert backend。
已由旧 source checker 识别的源族委托给旧 compiler，避免重复安装。
任意 phase/resolver 提议仍由实际 checker 授权。

核心新增 14 模块、1,730 行，审计 52 端点：15 closed，最大继承原有 42 个
globals，没有新增全局假设。Audit 固定 527 个 reachable proof sources、
9,214 bindings 及失败 proof attempts。另一个 trace module 用 reflexivity
证明 native trace 与实际 factory 相同。`native-v2` 固定 9,339 bindings，
compiler SHA256 为 `6ac62054ed5bceef2f51723b0b759b893b66830653a8e0eceaeae5ba37d63cac`。

未改动的原 `fusion5` 两段都安装，Pluto 的两份日志均记录从 `(i,j)` 到
`(i/32,j/32,i,j)` 的真实 tiling。全部 30,201 个观察值的 digest 匹配 GCC。
31 项 context checks 覆盖参数重关联／消去、unit/mixed-unit tiles、接受、
静态拒绝、多 marked sites、marked/unmarked 和 public exits。
同 binary 的 20 项 initialized 回归通过。十次 unchanged-assembly debugger
检查观察第二段：`n=31/32/33` 时 `q=1/1/2`，零值捕获 `q=0`，负值走 source
fallback 且不捕获 quotient；public controls 和完整输出也在 debugger 下匹配。

同一新 binary 完整重放 62 原例＋两份已披露 adaptation：60 raw 和两 adapted
输出匹配 GCC，`corcol3/pca` 的既有 frontend 拒绝保持，零 timeout/mismatch。
15 个原例共 32 sites，其中 29 为 quotient versions、三处 initialized。
新增 header-access site 是 29 的子集，不能重复相加；原 fusion5 两段合计两处。
43 个 compiled originals 未进入 tiling phase，tricky2/tricky3 仍进入而未安装。

所有其他项目实验结束后，用不变的 optimized assembly 和同 compiler／flags
的 unmarked 原程序做一次 warmup、七组交替完整调用。所有输出匹配 GCC；
medians 为 optimized 0.004383682 秒、unmarked 0.004313963 秒，比值 1.016161。
计入启动、初始化、两个 regions 和 digest；未隔离 guard、未控制 affinity／
外部 host load。这个短调用结果没有建立 useful speedup。先前 literal／polynomial
成本保持其独立 binary 边界。

[固定汇总](double-header-access.json)绑定 11 份报告、18,287 files，区分 proof、
extraction、第一次 final-candidate refusal、两段安装、contexts、actual paths 和 cost。
可在本工作区核对：

```
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_double_header_access.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/summarize_double_header_native.py --validate
```

安装数不能代替原语料的所有 sequential configurations，也不能代替收益。
Independent bounds、nonzero/inclusive headers、statement sequences、untiled
rank-one/mixed phase results、其他 sequential phases、原 BT／LLVM／SPEC、
larger tiers 和 OLO condition handling／useful effects 仍属 active goal。
