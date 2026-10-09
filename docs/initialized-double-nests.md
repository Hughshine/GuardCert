# 完整初始化循环：实际 source、模型和公开出口

2026-10-09。本阶段把[初始化＋inner reduction](initialized-double-reductions.md)
扩到完整 marked region，关闭原 `mxv`、`matmul-init` 的 outer-loop 与 literal
frontend 结构缺口。真实 source 与现有 PolCert `Loop` 的有限正常执行双向对应、
所有 source iterator 的精确出口，以及独立 small-step source protocol 均已编译。
安全入口条件、candidate/factory 和整程序安装仍未为这两个案例交付；原 corpus
的 nonidentity optimized coverage 仍为1/62。

## 实例作者使用的接口

[GuardMemoryDoubleInitializedNestData.v](../adapters/compcert-memory/GuardMemoryDoubleInitializedNestData.v)
从 actual canonical AST 产生普通数据：

```text
checked_double_initialized_nest p prefix_controls source
  : option (list ident * double_initialized_reduction)

checked_double_initialized_raw_nest p prefix_controls literal_source
  : option (list ident * double_initialized_reduction)
```

第二个接口位于
[GuardMemoryDoubleInitializedRawNest.v](../adapters/compcert-memory/GuardMemoryDoubleInitializedRawNest.v)。
支持族是任意深度的 initialized outer loops，同一实际 global signed-I64 header，
以及 leaf 上的 double initializer＋initialized reduction loop。Descriptors
包含实际 iterators、header、statements、checked instructions 和共同 layouts；
没有额外执行 IR，也没有让调用方填写 source/model 语义函数。

每层 producer 检查 iterator freshness，并重建完整 reset/test/body/increment
进行 statement equality。Leaf 沿用 actual declarations、access/layout 和 typed
instruction checks。Raw producer 先获得 elided AST 的描述，再重建并精确检查
literal frontend 形状。不匹配的结构返回 `None`。这个族仍不覆盖不同 headers、
任意相继 nests、任意 statement body 或任意 control exits。

Domain 实例消费返回的数据，构造已有 typed PolCert AST：

```text
outer Loop 0 captured_N
  ...
  Seq (Instr initializer) (Loop 0 captured_N (Instr reduction))
```

Model 的 parameter/coordinate 环境从 prefix 和 outer depth 构造。Sequence
保留真实 intermediate memory；模型 stores 保持相同 location registry。
Checked writes 不使用 header global，language 定律由实际 symbols/blocks 分离
得到 Mint64 header observation 的保持。

## 证明给出的边界

[GuardMemoryDoubleInitializedNestSource.v](../adapters/compcert-memory/GuardMemoryDoubleInitializedNestSource.v)
的 `checked_double_initialized_nest_source_model` 给出：

```text
actual source, finite E0 / Out_normal execution
  <-> real typed nested Loop execution with identical final memory
      and exact source-temp exit
```

Generic theorem 消费 checked AST、实际 program/site scope、入口 header load、
signed range，以及到达点的 address-resolution 前提。它在内部组合逐层 source
对应、frames、header stability、控制 invariant 和 exits；这些不由 C 用户提供。
当前 actual-source wrappers 从 `0 <= captured_N <= 98` 和两例的真实100 extent、
padding2 geometry 推出全部到达点的 resolution。这个条件目前是逻辑前提，尚未
由新的 emitted guard 交付。地址 resolution 不证明 allocation、load 或 store 权限。

公开出口区分未到达的 controls：

| 实际 region | `N=0` | `N>0` |
| --- | --- | --- |
| `mxv`：outer i，inner j | i=0，j 保持入口值 | i=N，j=N |
| `matmul-init`：outer i/j，inner k | i=0，j/k 保持入口值 | i=N，j=N，k=N |

其他 temporaries 保持。Leaf count0 仍执行 initializer 和 inner reset，整个
outer region count0 则不执行 leaf；这两个情况有不同的 exit。
[GuardMemoryDoubleInitializedNestExit.v](../adapters/compcert-memory/GuardMemoryDoubleInitializedNestExit.v)
表达这一差异，并证明 frame、idempotence 与 fresh-prefix override 的组合规律。

Literal-source finite transport 保持所有有限 traces、memory、temporaries 和
outcomes。它不提供 divergence/progress 结论。Canonical 与 raw 的独立
[source protocols](../adapters/compcert-memory/GuardMemoryDoubleInitializedRawNestProgress.v)
通过实际 checked assignments、fresh controls、sequence protocol 和 loaded-bound
loop protocol 组合。它们不要求接受时的 count/range 或 header stability，也
不把未定义的 memory accesses变成安全操作；这使 fallback 的 source protocol
可以独立于优化接受条件生产。Region protocol 仍须由 factory 接到实际 host。

## Narrative 对照与剩余责任

重新 fetch 后，`topdown/research-positioning@8ce9c8b` 仍是最新可见版本，
两份 topdown 正文与 main 一致。这里落实其 source/model 方向、前提来源和
三方责任澄清：

| 义务 | 当前证据来源 | 接入时还须交付 |
| --- | --- | --- |
| Actual syntax/types/accesses/layouts/fresh iterators | Domain AST producer＋language checker correctness | Actual site 上运输 checks，分配 private controls。 |
| Source/model 对应与完整公开 exit | Domain nest induction，复用 language execution/frame/control 定律 | 将入口 capture 后状态接入该 theorem。 |
| Header stability | Static distinct global IDs＋实际 language block/store frame | Actual program/no-shadow/site receipts。 |
| Reached-point bounds/resolution | Captured range＋actual geometry；当前 wrappers 内部 discharge | Emitted machine condition 安全且接受推出该 range。 |
| 安全 header capture 和 refusal | 尚无本族 runtime producer | 原 outer test 许可读取，private cache/flag、短路和拒绝入口运输。 |
| Candidate 正确性、lowering、progress | 既有 typed pipeline 服务可复用，尚未连接本族 | 实际 generated candidate 的检查、private pool、出口恢复。 |
| 整程序正确性 | 既有 scoped Clight host／CompCert backend | 本族的实际 region guarantee、placement/resources 和 Csem→Asm endpoint。 |

Kernel 未改变。这里补的是 `C_opt` 内部的 source/model 桥和 language source
protocol，不是整个 conditional optimizer。`C_derive`、`C_guard` 和 installation
仍须由 actual factory 闭合；终止执行 iff 不代替 source protocol，source protocol
也不代替 candidate/guard/install 证明。

下一项直接接原 `mxv` 的入口 capture/range、真实 PolCert/Pluto candidate、
lowering/public restore 和 scoped compiler，随后将同一数据路径应用于
`matmul-init`。首先拿到完整程序结果，再扩相继 nests；不继续把未安装的 proof
数当作功能覆盖。不同 sequential phases、原 BT、其他原案例和完整成本仍在 goal 内。

## 验证与复现

八库与两份 actual-source wrappers 共1,191行，50个 audited endpoints，14 closed，
最多6 inherited globals；261个 reachable sources，8,278个绑定文件，无新增公理。
27次库编译保留8次成功与19次拒绝；canonical wrapper 第3次成功，raw wrapper
第5次成功。两个 literal AST exports 单独编译，未改变 original C input。
首次 raw export 缺少原先所用 `-fall` frontend option 而拒绝，日志／script snapshot
保留；后继使用同一输入及该 option 成功。Export 本身不证明执行对应。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_initialized_double_nests.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/summarize_initialized_double_nests.py --validate
```

[机器摘要](initialized-double-nests.json)绑定 frozen source/object、尝试日志和
report hashes。Proof report SHA256 为
`ec74bcd8df51e709d18f0b7a68b79d2c4647fd826f624fd0af6ecf916e8e6ff5`。
本阶段只新增 source 证明和 read-only syntax export；没有新 installed optimizer、
native correctness/performance run 或 guard-cost measurement。整个 goal 保持 active。
