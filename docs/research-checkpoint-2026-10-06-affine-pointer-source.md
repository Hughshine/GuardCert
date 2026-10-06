# 2026-10-06：非矩形 pointer 源 package 与分阶段参数条件

本阶段把真实源 package、参数读取证据、算术 guard 和源 Loop／公开出口连在同一个入口。尚未把 alias 条件、独立 candidate 与 host 组成完整非矩形 pointer compiler；没有该新 pass 的 C frontend、提取或原生执行证据。完整 goal 保持 active。

## 使用接口与证明责任

| 提供者 | 本阶段的实际接口／工作 | 不由这项工作自动获得 |
| --- | --- | --- |
| framework | 复用 `sequence_readonly_conditions`，组合前一条件建立后项安全域的 readonly 证书；核心未改 | 不解释 C／pointer／循环域，不发现优化或推导任意假设 |
| 语言实例 | [readonly_completed_tree_condition](../prototype/interface/ClightReadonlyCompletedCondition.v)：消费真实 Clight tree 完成与接受 sound，利用表达式确定性得到所有可达 test 的安全、完成及入口不变 | 使用者仍须证明每个实际入口上检查能完成和接受的含义；正常有限路径不等于无限行为契约 |
| optimizer/domain | [AffineInnerPointerSyntax](../adapters/compcert-memory/GuardMemoryAffineInnerPointerSyntax.v) 的源描述、元数据 checker；[SourceDomain](../adapters/compcert-memory/GuardMemoryAffineInnerPointerSourceDomain.v) 的活动路径参数证据；[Guard](../prototype/interface/ClightAffinePointerGuard.v) 的范围／宽度阶段；[RegionSource](../adapters/compcert-memory/GuardMemoryAffineInnerPointerRegionSource.v) 和 [SourcePreparation](../prototype/interface/ClightAffinePointerSourcePreparation.v) 的真实源对应与公开出口 | alias 的该实例推导、pointer receipt 接入、独立 candidate 及两套表示范围、local rule／C_host |

`describe_memory_affine_inner_pointer source row_limit column_limit header_limits body_parameters body_limits pointers extent` 返回 `option (memory_affine_inner_pointer_package source)`。caller 可提出范围、body-only 几何列表、pointer 集合和 extent；checker 才生产证书。它自动识别源控制／仿射 header 和 body 操作，识别 RHS 标量，并核对完整 source／outer／body AST、六组控制 freshness、稳定参数隔离、列表唯一性、实际用途、pointer 覆盖、地址范围及两种 context 下同一 header encoding。

这个 description 是实际 affine-inner source，不借用矩形 nest 的源 AST。新 `AffineInner` 模块与旧一维 affine-access 模块区分；原 tracked Rocq 文件和 API 保留。

静态几何箱中的 N 有上界 `row_limit+1`，因为 guard 允许 `N<=row_limit`，而几何 range 使用 `<cap`。checker 还核对这个增加后的 cap 的 signed range。此 cap 是元数据，不是新增运行时 count 或 temp。域仍只枚举 `0<=i<N && 0<=j<U(i,context)`。

## 从源到条件到模型的 walkthrough

源例子是：

```c
for (; i<n; ++i) {
    k=i+1;
    for (j=0; j<k; ++j)
        p[32+64*i+j] = q[4096+64*i+j] + a;
}
```

1. checker 绑定这段 normalized Clight 源及操作。完整数学 context 包含 n、实际 header 参数、body-only 几何和 RHS 标量；body 指令参数仍是 `[i;j]++entry_context`。
2. `memory_affine_inner_pointer_completed` 的 D 是存在真实有限正常源执行。由源执行取得 row／N 的 word 类型。D 没有 non-alias，也没有无条件假设全部入口 temps 都是整数。
3. preparation tree 先检查 `i==0 && 0<n<=row_limit`。成功后，源确实执行过 outer header；包括零系数读取在内的 header 参数获得 word 类型。随后执行 header range 检查，再运行已编译的 width condition。
4. width 接受证明第一轮 `U(0)>0`，并覆盖所有源行的 `0<=U(i)<=column_limit`。利用实际第一轮 body 的地址／RHS 求值取得 body-only 几何和标量类型；然后才检查 body-only 几何范围。标量 a 的类型来自真实 body，不被强制非负。
5. `affine_inner_pointer_preparation_condition` 是 framework 的主 `readonly_condition`。它保证上述次序下检查安全、可完成、保持入口，且接受取得 header、width、几何 range 和完整 typed view。拒绝没有证明优化前提的否定。
6. `affine_inner_pointer_preparation_source_execution` 消费同一个 package、同一个入口的实际 preparation 接受和实际源执行，推出真实 pointer Loop 执行，并给出完整源内存与精确公开 i／j／k 的出口关系。源解码不要求 non-alias。

这已经连接了 C_guard 的算术部分与 C_opt 的源对应部分。尚需在此之后连接允许的 pointer 观察、物理 non-alias、独立 candidate checker 和真实候选代码，才能得到 guarded local rewrite。

## 验证和证据边界

`make affine-pointer-source-proof` 编译受影响依赖 closure，核对 60 个端点，其中语言端点 6 个；522 项实际依赖、867 份源摘要和当前 `.vo` 摘要。CompCert 基线 35 项，继承 domain 的 7 项，新增全局公理为空。旧 `compile_realized_observed_pointer_correct` 也在当前 closure 中审计；这只是旧编译入口的证明回归。

本次未 clean rebuild 整个 CompCert 工具链。报告为 `build/affine-pointer-source/proof/report.json`，SHA256：

```text
c072c58f92e655f5fd347a4a2c0f71eb9ec79aae6ed2c1736d0059cc8dcf8cc3
```

[Examples](../prototype/interface/ClightAffinePointerGuardExamples.v) 用一个显式 normalized Clight fixture 验证：源 checker 接受实际非矩形形状；窗口不足、缺失 pointer、未使用几何参数和被修改的源增量拒绝；宽度条件能编译。另有实际 `decision_run` 证明 n=0 时拒绝，不读取故意未定义的 body 参数及公开 j／k。它们不是从成功证书再生成的源，不宣称已经绑定 C frontend 输出或执行机器代码。

本轮没有 native 运行、提取或路径探针。此前 [bf3e39d 阶段](research-checkpoint-2026-10-06-affine-pointer-support.md) 的报告／编译器／native 产物未覆盖。本轮重编译改变其 closure 中 27 个 `.vo` 摘要，旧对象绑定验证在 `GuardMemoryAffinePointerSyntax.vo` 处拒绝；旧 source 字节保持，旧 whole-program theorem 经本轮新 closure 审计通过。旧 `.vo` 摘要与旧 752 次原生调用保留为历史证据，不将它们重用为本轮新证明／新非矩形执行的绑定。当前新报告的全部源和对象摘要已独立复核。

## 持续计划和难点

三张未完成的连接分别是：prefix 提供真实 raw-pointer comparison receipt；实际 ragged footprint 的充分 non-alias 条件与 candidate 的 validator／encoder 范围；新源形状的 local-rule／sequence progress 与全程序 host。随后才提取和运行真实非矩形 C，核对非空接受、n=3 alias 回退、空／机器边界、破坏 receipt、非法域／schedule、完整 buffer、公开游标及外围 effect。

目前 D 使用完整有限正常源执行，不能据此声称从有限前缀处理无限源，也不能提前读取 loaded／依赖 bound。bounding box 继续只推导充分条件，不能授权扫描源未访问的点。这些难点、loaded 参数的安全次序／稳定性、性能与同例 proof-burden 比较均保留在 [计划](current-work-plan.md)，不缩小原 goal。

再次 fetch 后，`origin/topdown/research-positioning` 仍为 `f7936299fa6272fbf50db6b94a1bd0333808ea09`，另外两个评审分支仍为 `9673381676e18ed0afbc6114e0a62bea9c48002c` 和 `3e9f0080def8c029cceedbd35184b4de7b8b96bc`。本阶段继续按 narrative 分开三方责任与四张证书；没有增加新颖性、性能或作者负担减少的主张。
