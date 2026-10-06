# 整段循环的逐步宿主：有限检查前缀与可能无限的回退

2026-10-05。本页原先记录尚未实现的条件性进展设计。现在已有 Rocq 接口、真实 Clight 局部协议和完整 Csem→Asm 端点；原生验证见 [unsigned 内存上界案例](clight-guarded-circular-case.md)。[宿主分类](host-capabilities.md) 区分这个接口与已有的完成执行宏宿主、有限表达式宿主。

## 补上的能力

旧宏宿主先用独立 source progress 将源小步收集为正常完成执行，再调用局部规则。整个 source 需要独立进展。因此，只有 guard 接受后才有限、拒绝分支可能无限的循环，不能直接交给该宿主。

新 `open_region_protocol` 消费局部小步模拟。每个实际源步由目标正步数匹配，或者由目标零／多步匹配并严格减少自然数索引；后继回到局部关系，或到达保护全部原 temps 和 memory 的公开正常出口。不要求所有源步都减少索引，也不要求先完成整个 source。

```text
用户提交的 actual source / actual replacement
  ↓ 任意 enclosing continuation 上的局部小步协议
OpenRegion 的结构上下文、scope、freshness、memory 运输
  ↓ Clight.semantics2 forward_simulation
先行 pass 组合 + CompCert frontend / backend
  ↓ Csem → Asm backward_simulation
```

接口见 [ClightOpenRegionContract.v](../theories/ClightOpenRegionContract.v)。全局宿主见 [ClightOpenRegionProof.v](../theories/ClightOpenRegionProof.v)，使用者接入见 [ClightOpenRegionCompiler.v](../prototype/interface/ClightOpenRegionCompiler.v)。新宿主并不理解 alias、unsigned 模距离或条件合成；这些性质在规则实例中解释和证明。

## 首个实际完整循环

```c
unsigned i = start;
for (; i != *bound; ++i)
  *out = i + 2U;
```

候选缓存 bound 一次，保持单位递增和 store。guard 先读取实际头部；活动时再比较 out 与 bound。空循环不触碰 out；活动且非 alias 才接受。只读条件由现有 loaded-tree 生成器从已注册的正前提原子产生，并有实际树相等定理。

| 阶段 | 实例提供的证明 |
| --- | --- |
| 源头部到首次 store | 有限真实小步前缀；源暂时前进，目标暂留 guard 入口，固定前缀索引严格减少 |
| 检查定义性 | 头部实际读取提供 bound 的可读性；首次实际 store 提供 out 的写权限／有效地址，足以安全比较 |
| 检查接受 | non-alias ⇒ 每次实际 store 保持 bound load；私有 cache 保存其值；源与候选逐步匹配 |
| 检查拒绝 | 目标实际原循环追上对应前缀，再逐步保持相同控制、memory 和公开 temps；不要求整个回退有限 |
| 正常出口 | 所有原 temps 相同，完整 memory 相同；cache 是新鲜私有名字 |
| 候选进展 | 固定 unsigned bound 的模距离证明有限性；这是候选的独立定理，不是宿主的源进展假设 |

前缀是证明见证。运行时直接执行 guard 和所选片段，没有先执行 source 来查询域，也没有 runtime ghost 权限查询。前缀中的首次源 store 在证明关系中对应到目标所选分支的首次真实 store，并未增加程序中的 store。

当 `out==bound` 且 `*bound!=start`，源在每轮将 bound 写为当前 `i+2U`，随后递增的 i 与新 bound 相差 1，即使 unsigned wrap 也如此。`circular_alias_source_diverges` 和 `circular_alias_guarded_diverges` 分别构造实际 Clight 的 `forever_silent` 执行。这不是只证明两个整数恒等式，也不是在无限外围中替换一个有限头部。

## 用户需要交付什么

语言无关层仍由用户提供 source、candidate、condition、D／P 与条件证书；用户选择位置和遍历。对这个 Clight 宿主，还要提交：

1. `open_region_contract live source replacement`：两段 label-free，并在任意保持 globals 的环境、函数和 enclosing continuation 上提供协议。
2. 协议的初始关系、每步匹配和公开正常出口；零步匹配必须有下降索引。局部规则可以使用自己的 source-prefix、frame、alias、counter 或模型设施。
3. `select live pool source = Some replacement` 蕴含该契约。fresh pool、整程序 scope 和结构上下文运输由通用编译适配器提供。
4. 若要叠加先行 pass，提供其 Clight forward simulation；`compile_open_regions_after_correct` 组合后得到 Csem→Asm backward simulation。

这个低层协议比“正常完成时等价”更强。有限 big-step 条件等价仍可被其他宿主消费；它本身不能证明可能无限的整段 rewrite。

## 已实现范围和剩余限制

当前接口支持任意长度的局部小步对应，但限定源处于同一函数／locals 的 `State`，并在正常 `Sskip` 出口交还上下文；不是任意内部调用、return、跨片段 goto 或异常出口的开放协议。初始实例选择普通 Mint32 读取／写入的 quiet 循环，外围调用、跳转和其他控制由全局结构证明运输。只有实例已证明的行为可以进入全程序主张。

当前实际树每处有一份缓存候选、两份原循环回退；没有在新宿主中复用共享 Boolean lowering。不是性能结论。signed overflow、任意 body／步长、多个依赖 preload、廉价一般足迹以及旧 affine／tiling 到主只读接口的迁移仍需独立推进。

这个实现补上 [OLO 验收](optimistic-loop-acceptance.md) 的“整段回退可以无限”能力；它没有使完整多面体主线自动验收。
