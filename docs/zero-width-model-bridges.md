# Zero-width children：源、模型与候选的责任连接

2026-10-08。再次 fetch `topdown/research-positioning@c4b1395`，main 的
[narrative](topdown/paper-narrative.md) 与该版本一致。本阶段按其
source/model 方向和 premise provenance 澄清，连接上一阶段的
[later-body 许可](leading-empty-body-licensing.md)与允许空 child 的模型域。

## 交付范围

五个新 Rocq 模块共 548 行，已编译并审计 17 个端点，7 个 closed，单端点
至多使用既有的 12 项 globals；它们均在父报告的 42 项允许集合内，无新增
公理。新增的是零宽度假设下的 candidate checker soundness、concrete
source decode、candidate lowering/public restore，以及 actual guard
接受后完整参数视图的 producer。没有新 factory、提取 compiler 或 native
接受结果。安装态的 first-empty-child 路径仍保守回退。

Kernel、language host 和底层 mapped-domain/tiling validators 保持。
新包装明确把更宽的假设交给原 validators；不扩大旧 certificate 的适用域。
本阶段的 checker 定理以实际 checker 返回 true 为前提，没有另行运行一个
具体调度/分块候选来证明它在更宽域上被接受。

## 同一个条件原来承担了两项责任

旧模型和源参数许可共同使用 `1 <= U(0)`，其中 `U(i)` 是数学 affine child
width。旧首个 body 证明据此恢复第零行 leaf execution，从中得到 body-only
address/scalar 参数的 typing；旧 `memory_parametric_assumed_loop` 则把同一
限制交给 polyhedral validator。

上一阶段从原有限执行恢复 empty prefix 后的实际 leaf，并证明此前 memory
保持。其常数个 affine endpoint 条件许可后来 body 的参数。本阶段把模型
限制单独改为

```text
0 <= U(0) <= cap
0 <= U(N-1) <= cap
```

在 `N > 0` 下，`memory_source_zero_endpoints_exact` 证明它与所有
`0 <= i < N` 上的 `0 <= U(i) <= cap` 等价。机器 guard 的安全求值仍由
原 checked arithmetic lowering 负责；数学 endpoint 定理自身不许可任何
memory read，也不自动取得 body typing。

对 `N=3, U(i)=i+M, M=0`，新模型 test 返回 true，旧 test 返回 false。
负的首个 width 和超 cap endpoint 被新模型拒绝。`U(N-1)=0` 允许。
模型也能表示所有 widths 为零，但 first-reached guard 会拒绝：没有实际
leaf，就不能靠该服务取得 body-only 参数。这里没有扩大 speculative read
的权限，也未提供一个新的 all-empty 安装分支。

## 三方责任与前提来源

| 连接 | 新证明及实际方向 | 前提来源与尚待连接的责任 |
| --- | --- | --- |
| Actual guard → full input view | `snapshot_zero_width_condition_view`：原 loaded source 许可及实际 check 接受推出完整 typed view | 静态 source package、header endpoint 编码；原 capture/header domain 和范围；复用上一阶段 later-leaf receipt。Body-only typing 是结论。Factory 仍须生产实际调用域。 |
| Actual guard → zero-width assumption | `snapshot_zero_width_condition_property`、`snapshot_zero_width_condition_model` | 数学 range 来自实际 guard 接受；full-context endpoint syntax equation 是静态 factory 义务。二者均不生产未来 header stability。 |
| Cached Clight source → source Loop | `memory_zero_width_pointer_region_source_under_ranges`：给定实际完成执行，恢复 Loop execution、相同 final memory 和公开 iterator exit | 静态 checked shape/body/encoding，动态 header/range/完整 typed view，原 source execution 是语义证明前提。没有 nonalias 前提；不是 parser 或独立双向 equivalence。 |
| Source Loop → candidate Loop | `checked_zero_width_model_candidate_correct`、`checked_zero_width_model_tiling_correct` 给出新的 `memory_zero_width_candidate_certificate` | 原 validators 检查实际 assumed source/candidate；候选作者提供实际 AST 与 mapping/tiling witnesses。证书应用时需要参数 bounds、zero-width model、footprint-restricted nonalias 和 source model execution。 |
| Candidate Loop → lowered Clight | `memory_zero_width_compiled_pointer_candidate`：恢复 actual compiled candidate execution，保留 final memory 和 context/pointers/live temps | 静态 backend compile equation，动态 typed view/encoder bounds、source footprint separation；消费新候选证书。沿用 footprint restriction 和 pointer backend。 |
| Lowered Clight → public exits | `memory_zero_width_pointer_candidate_restore`：实际 restore 后与原 source exit 的 live temps 一致 | Source decoder 提供 exit equation；静态 control distinction/context membership；实际参数 words 和最后 child expression。 |
| Original loaded source → stable cached source | 本阶段未放宽此桥 | 后继须把 zero-width facts 接到 actual point permissions、N/M stability scan 和 cached completion producer。不能直接使用旧 first-positive ready record。 |
| Local replacement → whole program/Asm | 本阶段未新增安装定理 | Factory 交付实际 region guarantee；site/selected language host 生产 placement、private resources、progress 和 continuation 证据，复用既有 CompCert backend。 |

原 source execution 从来不是 emitted guard 先运行原循环一次的步骤。
它是 conditional correctness 的语义起点。Factory 必须组合静态生产者、
运行时检查和入口/出口运输来 discharge 适用前提；源码用户仍只给支持族的
标注 C 和策略，不补 semantic callbacks。

Theorem 消费完整 typed view，与 actual guard 接受自动生产该 view，是两个
不同的交付。前者已经允许 zero children；后者已经复用原源许可证明。
Loaded source/cache 的 whole-loop transport 尚有更强的旧 ready 前提，因此
这两项完成不等于当前 compiler 已安装更宽域。

## 公开出口为什么暂时限制 nonnegative widths

旧 `memory_parametric_settle` 将最后的 `j` 恢复为 `U(N-1)`。对于零宽度
child，原程序 reset 后保持 `j=0`，该公式仍成立。新的 source decoder
显式消费所有 widths nonnegative，并沿用原底层 decoder 和 exit 服务。

对于负宽度 child，原程序的 `j` 仍为零，而旧公式给负值。上一阶段能够
取得 negative/zero prefix 后的 leaf receipt，但这不能代替新的 exit
证明。本阶段不支持负 child width 的 source/model/public-exit 连接。
首个为空、后继非空的 zero-width 路径是当前优先接入的接受域扩展；完整
目标中的其他 affine、alias、recursive loaded、scalar/chunk 与 OLO 范围保持。

## 审计与复现

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/compile_zero_width_model.py --attempt initial
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_zero_width_model.py --validate
```

编译 helper 对已有成功对象只核对并保留；每次尚未成功的 source attempt
先保存源码和 log。当前报告绑定 1,400 项 reachable source/object/helper/
attempt 证据，保留 5 次成功和 4 次被 Rocq 拒绝的 proof-source attempts。
成功源码、对象、helpers 与报告冻结，扩展使用后继模块。

```text
report: build/zero-width-model/proof-v1/report.json
sha256: a0720b58f71aa005ebf4a61672d1a2d9b75509f46cfbf484571deec06674413d
parent: build/leading-empty-rows/proof-v1/report.json
sha256: a0d2f284662d043e1830c9dcc29025fa42e448a13e0ccb20dcb8e1d605147867
```

工具链沿用 CompCert 3.18、Rocq/Stdlib 9.2、OCaml 4.14.1。旧 snapshot
native 报告的 2,500 项 bindings 在同一 opam 环境重新核对；没有重新运行
native matrix，没有新的运行成本或 profitability 测量。

下一任务以 zero-width ready facts 连接 source row decoder、实际 reached
write permissions 与 N/M stability，再生产 cached completion。随后 checked
factory 必须调用新的 candidate checker，把该域和 actual candidate/code
绑定，接 compact plan、selected compiler 和实际 annotated C/Pluto/native
验收。检查后继候选的接受域，不能仅放宽 runtime Boolean。
