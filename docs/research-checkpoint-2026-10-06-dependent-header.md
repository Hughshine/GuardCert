# 依赖 header：双读取、字节分离与源前缀证明

本阶段基于 `c51f526`，推进[private snapshot 后继验收](research-checkpoint-2026-10-06-affine-private-loaded.md)中的依赖读取。新增语言／domain 服务针对 `i<**pp`：从真正首次 header 取得两个 typed read，安全插入 private pointer 和 bound captures，检查实际 affine writes 与两项观察的字节分离，只有全部观察保持后才推进源前缀，接受后运输实际复合 header 源到缓存源。最小 kernel 未修改。

当前还没有把一个 checked source package 填入完整 joint scan，也没有新 candidate factory／Csem→Asm 入口、提取或原生执行。这是完成这些连接所需的证明阶段，不能算依赖读取优化器已验收。上一 private-loaded 编译器与原生结果保持独立。

再次 fetch，三个评审分支仍是 `7d94d810685a691efbf07df734f5fad8abfb4724`、`9673381676e18ed0afbc6114e0a62bea9c48002c` 和 `3e9f0080def8c029cceedbd35184b4de7b8b96bc`。继续按 narrative 区分 kernel、上层库、语言 host、domain 与优化证书；没有以接口参数冒充实例证明。

## 实际读取与 private preparation

```c
for (; i<**pp; ++i) {
  k=2*i+1;
  for (j=0; j<k; ++j)
    p[32+64*i+j]=q[4096+64*i+j]+a;
}
```

实际 header 先读取 pointer cell，再读取它指向的 signed bound。[ClightDependentBoundSyntax](../prototype/interface/ClightDependentBoundSyntax.v) 的反演提供：

```text
temps[pp] = pointer_cell
load Mptr(pointer_cell) = bound_pointer
load Mint32(bound_pointer) = signed_bound
```

`Mptr` 在当前 x86-64 配置为 `Mint64`；第二处仍是 `Mint32`。这两个许可都来自真正到达的原 header，零次 body 也有第一次 header。strict source progress 的活动条件只用 signed comparison 与机器最大值，不要求这两处未来稳定。

[ClightSignedExpressionProgress](../prototype/interface/ClightSignedExpressionProgress.v) 已证明并反射检查实际 normalized strict signed loop：成功的 `i<bound_expression` 足以取得 counter 与机器最大值之间的距离，body 每步保护 iterator。表达式可以包含依赖读取；frame／sequence／nested-loop 组合仍沿语言协议。它不证明表达式总有定义，也不推导 load 稳定性；新 host 尚未消费该 selector。region 入口使用已证明的 sequence／strict-loop 构造，不能把任意 framed-progress 对象直接当作初始 cursor 已关闭的 region。

[ClightDependentSnapshotInsertion](../prototype/interface/ClightDependentSnapshotInsertion.v) 在实际 prefix 后插入：

```text
private_pointer = *pp;
private_bound = *private_pointer;
原来的 **pp loop；suffix
```

公开 scope／memory、E0 与正常出口保持，两个 private 初值无需定义或一致。该语言 preparation 桥允许 prefix 本身改变 memory：许可取自在它之后实际到达的 header；不是把读取无条件前移到 prefix 之前。原复合 header 保留，没有用 private pointer 偷换拒绝分支的读取语义。不同的 fresh temps 还由 `dependent_header_safe_capture` 得到同时保留的两个 cache 值，后续真实 factory 必须静态落实其 distinctness／类型与 placement。

[ClightDependentHeaderObservations](../prototype/interface/ClightDependentHeaderObservations.v) 将 capture 的两个实际值绑定到一组带 chunk、block、offset、value 的观察。`dependent_header_from_observations` 填完具体 `**pp` 的 HEADER 语义义务：当前实际 source 只需 root temp 与原入口一致；pointer／bound caches 固定在 guard entry，两个实际内存观察保持时，header 的 Boolean 等于缓存 count 的活动性。

## 可执行的不同大小单元分离

不能把旧的 word 地址不等检查直接推广到 pointer cell。两个四字节 word 的起点不同，配合对齐足以分离；八字节观察还需要排除后半部分。

[ClightWordChunkSeparation](../prototype/interface/ClightWordChunkSeparation.v) 生成真实 Clight 检查：

```text
if write_address == observation_start: refuse
if observation is wide:
  if write_address == (int *)observation_start + 1: refuse
accept
```

它支持对齐的 `Mint32` write 与 `Mint32`／`Mint64` 观察，接受蕴含完整 byte separation。第二个比较地址的合法性和无 wrap 来自实际八字节 load 的权限与范围，不增加“guard 可以任意观察后四字节地址”的假设。比较用 equality，包含不同 memory blocks，不使用跨对象排序。第一次命中就不执行第二次比较；后续 probe 的执行也按条件短路。

[GuardMemoryAffineChunkWriteSeparation](../adapters/compcert-memory/GuardMemoryAffineChunkWriteSeparation.v) 消费已有 actual affine address 编码、range 与 reached-write receipt，形成每个实际 point 的双观察检查。其接受结果通过原 physical write-sequence theorem 保持两项 `location_load`，覆盖当前 `memory_nary_compute` 的真正读写序列，没有重定义一套纯数学写入语义。body operations 当前仍是 `Mint32` writes；这不等于已经支持一般 pointer stores 或异构 body。

## 局部到后续 header 的责任

[ClightObservedHeaderPrefix](../prototype/interface/ClightObservedHeaderPrefix.v) 将单观察 prefix 推广到一组观察。ghost invariant 保存原入口 reads、当前 reads、公开 temp frame、权限运输与剩余的真正 source execution。到达的活动 header 提供一整行实际执行；domain 解码它得到 point receipts。扫描只在本行全部观察保持后才产生下一行 invariant。guard 不执行 source stores，也不假设失败后的下一行可达。

| 证明义务 | 当前落实位置／剩余工作 |
| --- | --- |
| 源的合法首次读取、顺序 capture、公开运输 | language syntax／capture／preparation theorem 已落实 |
| 两个观察如何解释真正 `**pp` header | concrete `dependent_header_from_observations` 已落实 |
| 检查表达式自身安全、接受后 byte separation | language chunk condition 已落实；word slots、合法第二地址与机器指针语义都有证明 |
| 一个 actual affine point 对两个观察的保持 | domain 双观察 condition 和 physical write-sequence preservation 已落实 |
| actual body／row decode、所有坐标的算术和 receipt 来源 | 使用者实例义务；现有 checked affine package 的真实对应必须逐项填入 joint scan，尚未连接 |
| 足够 scan fuel 覆盖全部源 writes | 使用者／domain 的 cap／range 证书义务；generic scan exhaustion 本身不蕴含全局稳定性 |
| 接受后 source→cached 对应 | [ClightObservedHeaderCache](../prototype/interface/ClightObservedHeaderCache.v) 的 actual-execution bridge 已证明；domain 仍须提供 header、body decode 和每点全部观察保持的实例证据 |
| source progress | compound signed-expression selector 与反射 sound 已证明；不假设 bound 或 pointer cell 稳定；actual host 尚未连接 |
| source key、private pool 类型、whole-program 安装 | host／site 的后继接入义务；pointer cache 必须有 pointer 类型，不能直接复用全 numeric pool；尚无新 compiler 端点 |

缓存运输的正常 body、quietness、frame、point 和 header 参数都是有类型的使用者证明义务。它复用原 `strict_active_loop_transport`，不改变 source/candidate 执行的最终 memory、公开 temps 或 trace。它不会自行取得域覆盖、猜测观察、证明候选或提供 contextual closure。准备桥、前缀安全与缓存运输分别承担不同环节，完整 compiler 必须消费整条链。

## CompCert memory 反例与验证边界

[ClightDependentHeaderExamples](../prototype/interface/ClightDependentHeaderExamples.v) 实际分配 32 字节的 CompCert memory，在 offset 0 存 pointer，指向 offset 16 的 bound=3。原 header 的真实 expression evaluation 与安全双 capture 均有证明；private cache 初始不在 temp map 中。

offset 4 的合法 `Mint32` store 与 pointer 起点不同，但它与 `[0,8)` 重叠。实际第一次 equality 的 Boolean 是 false；第二次 equality 是 true，wide guard 拒绝，任意后续 probe 不执行。额外实际 store theorem证明写后不能再读出原 pointer。offset 8 的 word 则与 pointer cell 分离。不是仅统计 guard AST 或计算一个数学地址布尔值。

这些例子证明读取、条件运行与 byte footprint 义务，不证明一个完整、defined 的 C loop 在覆盖 pointer cell 后仍完成。当前 bare `**pp` header 的后续 pointer 若被破坏，源本身可能未定义；不能把这个 memory 反例说成已有完整 C 优化误编译，也不能拿它当新原生矩阵。真正 source package 的定义域和拒绝分支仍需接到宿主。

另有三项 progress fixtures：原 compound-header loop 通过 selector；写 pointer cell 的 body 仍通过 source-progress 检查；重设 iterator 的 body 被拒绝。第二项只区分 source progress 与 load 稳定性，不代表当前 affine optimizer 已支持 pointer stores。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make affine-dependent-loaded-proof
```

审计采用当前 private-loaded proof report 的 source／object 基线，并另核对原 compiler theorem；没有用早期 frozen compiler stamp 代替当前 development 状态。所有新增端点必须位于原 CompCert 假设基线内，domain 服务也不允许新增 VPL 公理。selected closure 为增量核对，完整闭包的 clean rebuild 未在本阶段执行。proof report 的新 frontend／extraction／native 字段明确为 false。

九个新增模块均实际编译通过；最终审计为 **51 个新增端点，其中 47 个语言端点，514 项 selected dependencies，945 份 source 摘要**。新增端点最多使用六项原 CompCert 假设；旧 private-loaded 完整 compiler 回归保持其 42 项基线，prefix 上层库端点无公理。最终 report SHA-256 为 `772724ae3d42eef83edf284b83cd5a0e133b65a2a23e85e4c9f6baefa817ccb9`，所继承 private-loaded report 为 `3fe08e4c4c8e233ad97f32b6ef2c90c31515d67a016a939c298790ff336464b6`。未重跑旧原生矩阵；旧入口产物绑定由其 validator 单独复核，不计作新依赖读取执行。

## 下一验收

优先用实际 checked affine package 填满 joint row/outer scan：复用其访问编码、width/count／word ranges 与 actual body decode，证明每次到达行的全部 write receipts，并把双观察 point condition 的接受保持填入 generic prefix。此后接 conditional candidate、原复合 header fallback、typed private pool 与 actual original source key，再提取新 compiler 并运行完整 C 接受／回退／上下文。按 cap 展开的 guard 大小、一般深层源、不同 body base 的 alias 接受和 P4／同例证明负担比较继续保留。
