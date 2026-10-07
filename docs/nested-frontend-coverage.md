# Nested frontend：多数组 BODY、依赖拒绝与程序上下文

2026-10-07，接续 `cc02ac7` 的 [actual C frontend／candidate execution](nested-frontend-native.md)。
沿同一实际提取入口 `compile_ncs_frontend_regions`，新增七类函数的完整 C 输入，
验证 read/write BODY 和 language host 上下文。没有修改 kernel、Rocq 源、candidate
producer、extracted driver 或 compiler binary；本阶段复用父阶段完整 Csem→Asm
定理和检查器，新增功能覆盖证据。先前报告保留原有 scope／bytes。

## 输入和运行

[native_nested_frontend_coverage.c](../examples/native_nested_frontend_coverage.c)有七个函数：

| 函数 | BODY／上下文 |
| --- | --- |
| `nested_accum` | 同一点的实际数组读取、计算和写回 |
| `nested_multi` | 读取 B、C，写 A；三个 pointer 可以同 block 或重叠 |
| `nested_chain` | 读取 `a[index+75]`、写 `a[index]`，存在真实 loop-carried dependence |
| `nested_write` | 写常数 1，可改写任一 loaded header，产生动态回退 |
| `nested_undefined` | 仅在 outer／child active 时定义 BODY scalar；空路径保持其未定义 |
| `nested_twice` | 同一函数两次原片段，第二次 reset row=0，再执行独立 guard |
| `nested_context` | 前后全局副作用、循环前 skip/return、循环后另一 return |

每个片段保留相同两次 `shape[0/1]+1` header 和 literal component 上界 5，
数据 index 为 `80*row+5*column+component`。119 个输入覆盖 row=0／1／-1／3，
singleton／one-column／空 outer／空 child，root/child offset expression wrap，BODY value wrap，
只有一个可读 header 且 BODY pointers 为空的 outer-empty 路径，全部 BODY pointers
为空的 child-empty 路径，以及数据 alias、control 和有效 root/child count=5 的
profile 边界拒绝 cases。区间 `[1,5)` 的上界为 exclusive。不是任意 fragment 类。

六配置 disabled、identity、interchange、2×3 tiling、wrong-reindex、invalid-domain，
共 **714 full assembly calls**。每调用核对 A 的 6,144 words、B／C 各 2,048 words、
两个 headers、三个 public counters 和两个 context markers。GCC `-fwrapv` reference
与独立动态 source-word model 先互相对照，再对照实际 CompCert assembly 输出。

所有函数的 original site descriptor 都通过 exact/checked 检查；原 source AST
保留在 fallback。Identity 安装七类函数；interchange／tiling 安装除 chain 外的
六类，twice 有两个实际 guarded sites。Disabled 和错误候选保留全部原 loops。

## 真依赖反例，不把任意拒绝称作发现 bug

Chain 的 `+75` 读偏移对应 source coordinates 的 `(row+1,column-1,component)`。
输入 `(start=0,u=2,v=3,alpha=1)` 下，强行交换前两层的 traversal 会改变 30 个
A words；强行 2×3 tiling 会改变 5 个。两个明确无 guard 的 C 变体经同一 compiler
的 disabled 模式编译，实际 **两次 assembly counterexample calls** 均与其重排
word model 一致，并与原源不一致。它们不是成功优化调用，另列于 native report。
模型和变体都恢复同样 public exits，差异发生在实际数组内容。

| 错误变换 | 不同 words | 第一处 A index：源值→错误值 |
| --- | --- | --- |
| interchange | 30 | `133: 625→852` |
| 2×3 tiling | 5 | `143: 653→878` |

Checked pipeline 在原 chain 输入上静态不安装这些候选，保留三个 source loops。
本报告观察的是整条 checked pipeline 的拒绝；未新增针对其内部某一分支的
diagnostic instrumentation，因此不把该观察细化成特定 validator subroutine 的
返回值。实际反例说明该候选确有语义问题；拒绝不是仅用坏 metadata 测出来的。

## 同一 chain 的更窄前提与实际 guarded rewrite

不受信任 profile proposer 还可以提出更强前提：把 child bound 范围从 `[1,5)`
缩到 `[1,2)`，root 的 `[1,5)` 范围保持。于是 child-count=1，`+75` reads 与
本 profile 下的全部 writes 分离，同一个 candidate checker 接受 chain 的
interchange／tiling。同一个 guard producer 编码该 profile：在 `(u=2,v=0)`
三行输入上走 fast，在前述 `(u=2,v=3)` 错误重排输入上回退原源。

这是 source/candidate 的可检查前提改变，不是改 kernel 或更换条件证明。新
data profile 仍沿有序 capture、numeric gates、header stability／alias checks
产生原 source 到模型的对应，使用相同 Csem→Asm compiler endpoint。前提由
实例 proposer 提出，充分性由 checker 证明，guard 安全／编码由已验证服务交付。
没有自动发现最弱前提，也没有宣称这个更窄条件最有用或成本最低。

单列的 one-column profile report 覆盖两个配置，各 119 full assembly calls，
共 **238 calls**，全部输出与原源一致。另 **238 instrumented Clight calls**
检查分支，每配置 16 fast、118 runtime refusals。所有七类函数安装候选，chain
不再是静态拒绝；受限前提外的输入运行原 AST。该报告没有额外 GDB path probe。

## 动态 condition 的覆盖与机器路径

三个候选配置的 instrumented Clight 各 119 calls，共 **357 calls**：

| 配置 | fast dispatches | runtime refusals |
| --- | --- | --- |
| identity | 53 | 81 |
| interchange | 47 | 71 |
| 2×3 tiling | 47 | 71 |

这些是最后 select 的执行次数，重复 sites 可在一个调用中执行两次；chain 静态
拒绝和 context skip 可完全没有 select。不能把 370 个 dispatches 当成 357 个
函数调用，也不能把 Clight 插桩称作实际 assembly 路径。

BODY 的 `alpha` 只影响存储值。取 INT_MAX／INT_MIN 的 active 输入仍走 fast，
与 source signed32 modular 操作结果一致。它的定义性在 active source leaf 中
生产，不要求 BODY value 算术无 wrap。控制／地址的整数模型和范围条件另由
原 numeric/model services 校验；root/child loaded-plus-offset wrap 导致空源和
回退时，不提前读取无许可的 child header／BODY parameters。这区分了前提的
语义用途，不能笼统声称“所有算术必须不溢出”。

十次 GDB probes 观察未插桩 assembly 在 `a[15]`、`a[80]`、`a[160]` 上的写入，
不是全部 stores 的日志，且不计入 714 原 matrix calls：

- independent arrays 和同 allocation 的分离 slices：interchange 顺序
  `[80,160,15]`，tiling `[80,15,160]`；说明 same block 不等于有依赖。
- 完全相同 pointers 和 shifted alias：源顺序 `[15,80,160]`。
- twice：上述候选顺序按相同次序执行两次，第二次值也匹配模型，出口 `[3,4,5]`。
- context skip：零被观测写入，出口 `[-7,-8,-9]`，markers `[107,200]`。
- context 的 post-loop return：tiling 顺序，出口 `[3,4,5]`，markers `[107,219]`。

## 复核和下一步

当前已安装父阶段 compiler／proof closure；运行命令如下，machine probes 需要
允许本地 GDB child-process ptrace 的环境。`--validate` 只读已有 artifacts：

```sh
make nested-frontend-coverage
make nested-frontend-coverage-clight
make nested-frontend-coverage-machine
make nested-frontend-profile
make nested-frontend-coverage-validate
```

Source generator、cases、word model、compiler/proof/driver/native source stamp、
全部 assembly／binaries／outputs 和 GDB scripts/logs 都绑定摘要。原 compiler SHA
仍为 `04d799e2617550ec5895fdb2b27cf8319c1796e6ee41e831baae30173329e478`。

| 报告 | SHA-256 |
| --- | --- |
| `build/nested-frontend/coverage/report.json` | `9330c60bb3a1b51bfc785d80248747203fcd2f81ecc6f5dab562e2762705d6e2` |
| `build/nested-frontend/coverage/clight-report.json` | `2b7e2429203f0a4fe1bf8413b6b702371878c32a48fac7ba9d992d6fb1e42d02` |
| `build/nested-frontend/coverage/path-report.json` | `6d61ac9ab746ace0a4a76e5e9c329dd676b35ae7de5f259b28785a299b85eb5b` |
| `build/nested-frontend/coverage/one-column-profile/report.json` | `63f30c900e6b0f8199cc5bec427ac219a2b41f87d507c0503ec4816ee5147ec2` |

本阶段没有新增 generic semantics／condition inference，也没有运行时间、guard
work 或作者 effort 测量。接下来建立 fresh-checkout empty-build 路径，再在同例上
证明和比较 compact sufficient condition 的安全、接受域、成本与作者 obligations。
当前 source profile 仍是有限 loaded-header shape；更广 affine/polyhedral source、
完整原 BT 的动态布局／delinearization 和 OLO usability 仍需按主计划完成。
