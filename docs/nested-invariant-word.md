# 入口参数计算的同值条件：真实 guard 与完整 compiler

2026-10-07。新的 producer 将此前的 literal-word stability shortcut 扩展到
loop-invariant affine int32 表达式。它已连接实际 Clight guard、candidate 证书、
语言 host 和 Csem→Asm compiler，并完成提取及新的实际 C 矩阵。
源类仍是当前三层、固定布局、uniform child bound 的 nested source。

## 用一个实际例子看条件从何而来

新的 C 输入保留两个反复读取的 header，以及可能与它们 alias 的 output：

```c
for (; row < shape[0] + 1; row++)
  for (column = 0; column < shape[1] + 1; column++)
    for (component = 0; component < 5; component++)
      a[80*row + 5*column + component] = (alpha + beta) + 1;
```

令 `w` 是 `(alpha+beta)+1` 的 **CompCert int32 word** 结果。若两个 raw header
都等于 `w`，BODY 即使写到 header 所在 cell，也保持它们的值。因此 source 的
反复读取与缓存域相符，可以再使用既有 dependence validator 和候选 lowering。
这是一种观察值保持条件，允许部分本来会被地址分离条件拒绝的 alias 输入。
它不是对任意 alias 的许可。

原来的 capture、row gate、正 count gate、numeric/profile 检查与两个 helper
初始化仍先执行。只有它们接受后，新比较才读取入口参数和已初始化的 caches：

```text
root_cache  == int32(w + root_delta)
child_cache == int32(w + child_delta)
```

两项比较由已认证的 initialized-Boolean `Oand` 合并，不新增 header load 或 pointer
comparison。Runtime AST 在两处计算值表达式，没有声称进行 common-subexpression
elimination。Cache 等式经 modular addition cancellation 推出两个 raw headers 为
同一个 `w`。比较不成立时执行单份原 stability scan；语法不支持时保留旧 guard。
既有 literal BODY 优先保留原 lowering。Stability 接受后，原 multi-array alias
检查、candidate、五次赋值恢复公开出口、原 AST fallback 都继续使用。

值计算允许 wrap。例如 `alpha=beta=INT_MIN` 时，结果 word 为 `1`；raw headers
均为 `1` 时得到两个正 count `2`，实际原源与候选仍一致。这里没有新增“全部算术
都不溢出”的条件。Control/address 的范围和定义性仍由各自的既有模型条件判断。

## 表达能力与静态验证

[CompCertInvariantWordObservation.v](../prototype/interface/CompCertInvariantWordObservation.v)
的 actual execution checker 要求所有 memory stores 为 typed full int32 dereferences，
RHS 精确编码同一个 memory-free affine 表达式。表达式支持 temp、整数常量、加减、
乘常数，按 modular int32 求值。Sequence、conditionals 和 loop control 可组合；
所有 temp assignments 必须保护表达式读取的 temps。其执行定理交付 constant-word
memory effect 和 temp frame，再使用既有 cell geometry 保持同值 observation。
这是对实际完成执行的 effect 定理，不能替代 source progress、pointer frame 或读许可。

[ClightNestedInvariantWordCheck.v](../prototype/interface/ClightNestedInvariantWordCheck.v)
从第一个 store 提出表达式，使用既有 reifier 后检查整个 literal component subloop，
并检查全部 value reads 属于源 package 的 parameters。这个子集只支持 loop-invariant
值；坐标相关值、混合 store 值、partial stores、保护值参数的更新和不支持的 RHS
均不能使用新 shortcut。Checker 拒绝 shortcut 不等于拒绝整个 rewrite。

定义性不是新使用者假设。`ncs_prepared_invariant_value` 消费已有 prepared receipt
的 parameter domains，这些 domains 最终由已到达的真实原源 BODY 生产。空 outer／
child 或其他 gate 拒绝时不执行新的值比较，不要求原 source 未到达 BODY 的参数
已定义。新代码的 pure evaluation、比较 Boolean 和 eager conjunction 都有实际
Clight 证明。

[ClightNestedInvariantWordModel.v](../prototype/interface/ClightNestedInvariantWordModel.v)
连接每个 component subloop 的 observation 保持、原源→缓存源运输和 canonical
模型执行，交付相同 final memory／公开出口。它使用完整 source-derived capture／
numeric／preparation 证据，不假定将要证明的 header stability。

## 三方所有者与四条逻辑链

| 所有者 | 本阶段实际交付 |
| --- | --- |
| 最小 framework/kernel | 既有 guard/preservation certificate 及 `guardify_preservation`；代码和语义边界保持 |
| Clight 语言服务 | Affine int32 求值/frame、typed actual-store effect、同值 memory observation、defined Boolean 组合；复用 private-state、dispatch、installation、progress/backend 定理 |
| Domain／优化实现 | Static BODY/read-set checker、实际入口定义性、header 同值充分条件、原源到 canonical 模型及 guard-exit ports transport；复用 dependence/candidate/exit 证书 |
| 具体 site 作者 | 既有 source descriptor、parameters/live/private names、candidate schedule/domain evidence；没有新增 value、definedness、effect 或执行语义 callback |

这张表描述证明归属，不要求用户手填四份 record。逻辑上，新的 observation 保持与
source→model producer 交付 `C_derive`；实际值比较执行与其接受事实交付 `C_guard`。
既有 `C_opt`（conditional candidate correctness）和 `C_host` 复用。实际
whole-program installation 仍由 Clight language host 与 checked region/site
证据共同完成，不能由 local guard theorem 单独推出。

最难的位置是：新值表达式的真实入口定义性、整个 BODY 的保护读集合、可能 alias
的 header observation 在每次 source test 前保持，以及 prepared/model 入口到
actual guard exit 的运输。两个 Bool 等式本身不能代替这些证明。核心没有增加任意
assumption extractor、WP、最弱条件或最优 guard synthesis。

## 完整路径与本阶段验收

实际 producer 位于 `ClightNestedInvariantStability.v`。后继 multi adapter、guard
certificate、preservation、data-only factory 交付原 host 所需的 projected region
contract。`ClightGuardedNestedInvariantCompiler.compile_ncs_invariant_regions_correct`
证明 successful compilation 的 Csem→Asm backward simulation。Source/candidate
proposal types 与前一 compact compiler 一致，优化搜索仍不受信任。

独立 `build/nested-invariant` 绑定本阶段产物：

- Proof：35 endpoints／591 required dependencies／890 source digests；kernel
  闭合，compiler 保持既有 42-global baseline，零新增 global axiom。12 个查询端点
  闭合；其余使用各自已有基线，不把 baseline-free checker 等同于全部语言定理。
- Compiler：实际入口已提取；使用同一 pinned CompCert 3.18／Rocq+Stdlib 9.2
  工具链和原 C descriptor／candidate proposer。
- Native：两类 C BODY／20 inputs／六种 proposal modes，共 120 full assembly
  calls；全部 2,048 output words、headers、三个公开 counters 和前后 effects 核对。
- Clight dispatch：identity/interchange/tiling 共 60 instrumented calls，每种 mode
  10 次接受、10 次回退。包括普通和 wrap 参数的两个 header-alias 接受路径、header
  不同后的源域变化回退、coordinate BODY 拒绝 shortcut、非零 row、空路径及错误候选。
  这些是修改 Clight printer 输出后的 GCC probes，不是未修改 assembly dispatch 证据。

新的实例没有新 GDB machine probes、timing／profitability 或 fresh-checkout rebuild。
Uniform 参数例的 source／identity／interchange／tiling machine bytes 为
203／662／708／807；另一个 coordinate BODY 为 205／616／658／763。两类函数的
计数包含 context effects，不能与前一 literal kernel 的大小或计时直接对比。
既有 source-only reproduction 仍只绑定其当时 compiler，不能自动升级为本入口的复现。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/nested_invariant.mk native
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/nested_invariant.mk validate
```

Proof report SHA-256：
`d884ae94133cec8ac23648a36e892cc3fd3614a16411aea1268654b12dac2866`。
Compiler SHA-256：
`c0e5ce1c4510abc0dc55e3f4a0bdd42785397fd8bbbcc708b63ee6a425e97916`。
Native report SHA-256：
`198f06bcbc9a4864c7ac174ecc371ddceaa957bfea2924df34504c23596a832b`。
