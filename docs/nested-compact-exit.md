# 已接受的三层模型：五次赋值恢复公开出口

2026-10-07。前阶段完整计时发现，同值 guard 已不遍历循环域，但候选仍执行
`affine_shadow_source`：去掉 memory BODY 后重放三层控制循环，恢复 source 的
公开 counter 和 helper 出口。本阶段实现自己的紧凑出口 producer，并沿现有
guarded rewrite 接到新的完整 Csem→Asm compiler；guard、validator 和语言 host
保持。这个改动属于候选执行对应，而不是前提或检查条件的简化。

## 源类和为什么可以简化

当前 checked nested site 的模型为：root 读取稳定 temp cache，child 每行从
另一个稳定 cache 取相同 upper，第三层取 literal upper。三层 BODY 的 checked
leaf 只写 memory，不写 temps。模型接受事实和实际 source execution 一起证明：

- root counter/cache 和 child cache 是实际 int32 words；
- root 入口 counter 小于 root cache，child count 为正；
- literal component count 为正，这是既有 static site 检查的事实；
- names 唯一，cache 与被设置的 counter/helper 不同；candidate 保持 cache。

因此每层实际进入过，且 control increment 从 signed 范围内的起点精确走到
upper。最后的公开出口是 `row=root_cache`、`column=child_cache`、
`component=literal_upper`；两个 private helpers 分别为 child cache 和 literal。
执行的 patch 按顺序设置 child helper、component helper、component、column、row。
五个赋值只访问 temps，不读写源内存。

这个结论不适用于任意循环。空 child 原本应保留旧 component，空 root 原本应
保留旧 column/component；这里没有把它们一律设为 upper。生产 guard 拒绝这些
入口并保留原 AST fallback。局部证明不额外假定 `row=0`：它消费 root 实际活跃
和 child 为正，能覆盖现有 abstract model anchor 的接受入口。运行时支持的
原源 profile 仍由既有 row gate 决定。

## 可复用定律和连接顺序

[ClightIdempotentControlLoop.v](../prototype/interface/ClightIdempotentControlLoop.v)
给出语言级定律：silent、无 memory effect 的 control BODY 每轮执行同一个
settlement；settlement 幂等、保持该层 iterator/bound，并与 iterator 更新交换；
一个声明的 invariant 由 settlement 和 increment 保持。定律构造实际 Clight
执行及最终状态，包含零次情形。它并不允许省略普通 memory BODY。

[ClightFixedTempPatch.v](../prototype/interface/ClightFixedTempPatch.v)
生产固定赋值列表的 lookup、幂等、fresh-key 交换和 protected frame 定律。
这些代数定理的 assumption 集合为空；control execution theorem 使用既有
Clight/CompCert 基线。

[ClightNestedCompactExit.v](../prototype/interface/ClightNestedCompactExit.v)
实例化三层定律，构造原 shadow 的精确退出 temps；从既有 source→shadow
执行对应和 quiet determinacy，证明 patch 的结果等于实际模型 source 的
完整 temps 出口。`ncs_compact_accepted_inputs` 从 guard 接受和真实模型执行
取得活跃及 word 事实。它们由 checked site 数据和语言/domain 库生产，factory
没有增加语义 callback。

[AffineNestMultiCandidatePrefix.v](../prototype/affine-nest/AffineNestMultiCandidatePrefix.v)
复用既有 source decode、footprint restriction、非 alias、candidate validator
和真实 Clight lowering 定律，单独交付候选 BODY 的执行、精确最终 memory 及
入口 protected ports frame。旧 shadow compiler 的源与报告保持固定。

[ClightNestedCompactCandidate.v](../prototype/interface/ClightNestedCompactCandidate.v)
消费这个 prefix，从真正检查后的入口运行 candidate，再运行五个赋值。
cache frame 运输 patch 值，恢复 source 的全部公开 ports；candidate 和 source
得到同一个 memory。后继 local preservation certificate、guarded preservation、
projected region contract 和 data-only factory 连接原始 loaded source 与 fallback。
最后
[ClightGuardedNestedCompactCompiler.v](../prototype/interface/ClightGuardedNestedCompactCompiler.v)
的 `compile_ncs_compact_regions_correct` 给出实际 Csem→Asm backward simulation。
重复 sites 继续使用现有 checked table 与 host 安装定理。

## 责任和使用者输入

| 所有者 | 本阶段新增或复用的证据 |
| --- | --- |
| Framework/kernel | `guardify_preservation` 不变，消费新的 local candidate 证书及原 guard 证书 |
| Clight 语言库 | 幂等 control-loop 执行、固定 temp patch、quiet determinacy；复用 frame、安装、progress 和 CompCert backend |
| Domain/优化实现 | 从实际接受模型推出 positive/word 条件，实例化三层 patch，连接 memory candidate prefix 和 source 的公开出口 |
| 具体使用者/site | 原 AST、parameters/live、names、checked leaf、候选 schedule/domain evidence 等既有数据；没有新增 exit-domain/frame callback |

这里没有增加任意 exit synthesizer 或 universal WP。五次赋值只为当前 uniform
nested 模型生产；一般 affine child 的最后 upper 可能依赖 parent 或为空，需要
另外的 active/last-path 事实。

## 验收与命令

独立目录为 `build/nested-compact`。42 端点、606 依赖、905 source digests 审计
通过；kernel 闭合，完整 compiler 的 42-global 基线保持，零新增 global axiom。
提取成功。原七类函数／127 输入的 762 assembly calls 和 381 Clight dispatch
calls 通过；更大 literal-15 profile 的 60 新 assembly calls、45 Clight calls、
九个未修改汇编 probes 通过。完整 arrays、headers、公开 counters 和上下文
markers 按独立 source-word model 核对，接受及拒绝结果保持。

较大输入的三个 watched output indices `(15,80,160)` 仍分别给出 source、
interchange `(80,160,15)`、tiling `(80,15,160)` 写序，公开出口 `(16,16,5)`。
Identity/interchange/tiling bytes 从 `(611,644,755)` 降至 `(587,626,719)`；
source 为 161 bytes。代码大小不替代完整运行时间。[完整配对成本](nested-compact-cost.md)
另完成 30 轮／1,200 batches，同值 interchange 比相同 guard 的 shadow 版
便宜约 19%，但仍约为 source 的 1.35×；非同值输入仍显著更慢。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/nested_compact.mk native
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/nested_compact.mk large
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/nested_compact.mk cost
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/nested_compact.mk validate
```

Assembly probes 需要允许 GDB 启动待测进程。新的 proof/extraction 不读取历史
proof reports；本阶段仍使用当前树中 digest-bound 的 CompCert proof objects。
先前 source-only empty-tree 验收属于旧 compiler stage，不称为新入口的 fresh
rebuild。完整计时另与相同 guard 的 shadow compiler 配对比较；不通过不同
阶段成本相减归因。更一般 affine source、非同值及多数组 footprint 条件、
完整 BT 动态布局和作者负担比较仍待继续。
