# 未分块 phase：真实调度、条件与完整程序

本阶段修复的是 producer 把所有 phase 都要求成「至少新增一个 tile 维度」的
限制。新的 policy 可以提议零 link witness，表示 source point 不增加 tile
坐标；schedule 仍可改变。实际 source/model、phase validators、最终 candidate
checker、machine lowering、公开出口和 Csem→Asm 使用既有证明链。
没有新增 Rocq theorem、kernel law、host law 或全局假设。

## 使用与责任

常规编译继续使用自动 Pluto scheduling／tiling／intratile optimization。
`GUARDCERT_PHASE_KIND=untiled` 让同一 producer 调用 Pluto 时显式传入 `--notile`。
`GUARDCERT_PHASE_ORDER=1,0` 则提供一个手工 affine schedule 提议，交换两个
source iterator 的执行次序。它不改 domain、access 或原指令；现有 import／
dependence validator 决定该 schedule 是否可用，后续 checker 验证实际生成的
candidate。手工策略是数据输入，不是用户提供的语义证明。

例如原 intratileopt1 的片段具有以下结构，真实测试保留其数组、类型和 IEEE
运算树：

```c
#pragma scop
for (long long i = 0; i < N; ++i)
  for (long long j = 0; j < M; ++j)
    a[j+2][i+2] = (b[i+2][j+2] + c[j+2]) + 1;
#pragma endscop
```

order `1,0` 提议先遍历 `j` 再遍历 `i`，保留 instruction 的 source `(i,j)`
坐标。静态 decoder 与 footprint checker 给出逐轴充分 cap `98,98`；language
capture 从实际 `N/M` load 产生安全检查、范围和精确 private I32 表示。接受时
candidate 使用实际 captured `M/N` 上界；拒绝时执行该阶段原 source。两条路径
恢复公开 I64 iterators。`N=23,M=31` 的完整程序输出和公开出口与 GCC 一致；
未修改汇编的 debugger 观察同时确认 captured `[23,31]` 与接受路径。

| 责任方 | 本阶段实际消费的服务 |
| --- | --- |
| Kernel | 局部 guarded correctness 边界不变；本阶段没有把 native policy 放进 kernel |
| Language/domain 实例 | 既有 source/model、safe captures、typed bounds、实际 lowering、private frame 和 public exits |
| Host/site | 既有独立 progress、scope、fresh resources、当前 intermediate program 安装和后续 passes |
| 优化 policy | 提议零/非零 link witnesses、实际 schedules 和实际 Loop；所有提议仍由 checker 授权 |
| C 源码使用者 | 提供标注与策略选项，不补 semantic callbacks |

完整编译器仍调用
`RectangularHeaderLiteralQuotientPaddedCompiler.compile_selected_rectangular_header_literal_quotient_tiled_stable_program`。
其既有 theorem 量化 arbitrary phases、adapters 和当前程序 resolver，因此可以
直接容纳新的 native policy。不是凭借新 OCaml 函数的自述假定调度正确。

## 原样结果与非法结果

原 seq 是按 `(i,j)` 顺序对同一个 double `s` 累加。原 Pluto 返回未分块的
原样顺序；手工交换 `j/i` 不能利用实数加法结合律来证明 IEEE 程序。测试中
该错误提议在 affine dependence validation 后拒绝，没有进入 tile import
或 candidate codegen；完整 source fallback 输出匹配。

原 tricky2 两个一维更新同样收到未分块原样调度。后继 policy 对这些原样结果
直接保留 source，不注入 identity guard，不将它们算成新增优化覆盖。原 blocker
现在有具体分类：不是零 links 本身不可验证，而是这些实际提议没有变换效果。
进一步优化需要真实的其他变换或额外有证据的条件。

第一次 native build 只比较 scattering AST。Pluto 去掉 source tree 的零 schedule
分量，造成原 seq 被误判为「有变化」并安装无收益 guard。五项诊断保留了这个
counterexample；其 build 中的 policy metadata 不作为已通过的 native 事实。
V2 对可重建的单位 output equations 移除零分量后比较，使原样结果拒绝。
这只是保守的 untrusted policy，不是任意 schedule 等价判定或最优算法。
即使 policy 误判，实际候选仍需通过既有 correctness checkers。


摘要在交叉检查V3的automatic phase shape时拒绝了该项：仅省去`--tile`没有
关闭本地Pluto的默认tiling。该失败snapshot与`added-dimensions=2`证据保留；
V4显式`--notile`后，automatic实际输出`added=0 unchanged=false`，使用实际
参数bound并安装。这次修复不改手工路径或默认tiled路径，旧成本仍属于旧build。

## 原始参数 bound 与后继记录

V2 的未分块候选仍使用常数 cap 枚举与 membership predicates。V3 在所有
witnesses 都没有 tile links 时保留实际 affine parameter bounds；singleton
与 point-coordinate normalization 仍作为提议。最终 candidate checker 重新
验证实际 Loop，machine lowering 检查捕获参数及循环算术的范围。因而没有
将 native interval computation 冒称为证明，也没有绕过 guard/capture。
有 links 的路线继续使用既有 adapter。

成功源、helper、二进制和 reports 保持冻结，各后继分别固定：

- `native-v1`：结构相等判断不充分，五项诊断中的 seq-auto policy 失败。
- `native-v2`：零分量 signature 后继，28 contexts 通过，仍使用 cap 包络。
- `native-v3`：保留手工未分块实际参数 bound，33 contexts 通过；自动选项仍
  因Pluto默认tile=1而返回两个tile维度，不是自动未分块证据。
- `native-v4`：显式`--notile`，33 contexts通过，自动路径确实返回零links并安装。
- `paths-v1`／`paths-v2`：分别对V3／V4的六次 unchanged-assembly observations 全部通过，包括接受、
  空/负轴和两轴 cap refusal；没有修改目标代码或测量 guard cost。

33 contexts 包括自动/手工未分块 interchange、真实不等参数、公开出口、空域、
范围回退、错误 coordinate/bound/witness、畸形 phase、重复标记和标记旁的原程序。
原 matmul 的手工 `i/k/j` 未分块候选也实际安装并保持完整输出。

完整语料与较长调用成本的固定结果见 [机器可验收摘要](mixed-double-phases.json)。
成本输入在原 matmul 外层重复相同 region，不改变数组、类型或 IEEE 运算树；
属于披露的 context variant，不是原 corpus 覆盖。比较 unmarked／tiled／untiled
三种实际编译结果，固定一个允许 CPU，保持同 compiler 与 flags。仍未隔离
单独 guard 成本或控制外部 host load，不能推广为 benchmark-wide profitability。


V3的默认完整62＋两adaptations重放仍为60raw＋2adapted匹配、两既有frontend
拒绝、零timeout/mismatch；22原例39sites，没有新增source-family覆盖。
较长repeat context固定CPU、两次warmups及每variant七次轮换测量。Wall medians
为unmarked `0.479240290`、tiled `0.235665644`、untiled `0.214340328`秒；后两者
相对unmarked为`0.491748`和`0.447250`，本上下文约`2.03×`和`2.24×`。
Child CPU ratios为`0.489989`和`0.445493`。所有输出与重复GCC reference匹配。
这次证据包含startup、一次初始化、200次原region和digest；不重标原单次成本。

V4另行完成完整重放，仍为60raw＋2adapted匹配、两frontend拒绝、零timeout/mismatch，
22原例39sites。其独立成本后继也固定CPU、200次原region、七次轮换测量；wall
medians为unmarked `0.479495436`、tiled `0.239061819`、untiled
`0.210628710`秒；ratios为`0.498570`／
`0.439272`，本上下文约`2.01×`和
`2.28×`。Child CPU ratios为
`0.497037`／`0.437298`。
输出全部匹配相同repeat-context GCC；这些数字属于V4，V3成本原报告不改。

## 仍需完成

本阶段没有新增原 source 族覆盖，也未展示一个已安装 region 内同时含 tiled
和 untiled statements。零/非零 links 在 phase 数据接口可混合，不等于实际
多 statement source、异深度 codegen 和全程序安装已经交付。下一个功能验收
仍需处理该 source/phase 契约，以及独立参数路线的动态 tile bounds、非零与
inclusive headers、statement sequences、其余 PolCert/OLO 顺序变换和更广成本。
