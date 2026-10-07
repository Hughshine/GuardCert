# Deep affine＋loaded bound：候选与完整编译证明接入

2026-10-06。接续 [完整稳定性检查](research-checkpoint-2026-10-06-loaded-affine-scan.md)。
本阶段连接同一实际 bound capture／numeric／stability 检查、旧多数组 alias guard、
旧候选 validator／backend 和 Clight whole-program host，得到新的 Csem→Asm 定理。
本轮 fetch 的 narrative 是 `226ba94`；已同步新增的功能／可用性实施顺序。
最小 kernel 不变，完整实现目标仍 active。

## 实际检查与候选链

```text
原每次读取 *bound 的源循环
  → 原首次 header 许可 private capture
  → numeric／root 起点和次数检查
  → 逐 body 的实际 write-vs-bound 检查
      → 拒绝：保留原 loaded source fallback
      → 接受：证明所有活动 body 保持 bound
          → 导出实际 cached-source execution
          → 运输到检查后的入口（保留新 cache）
          → 运行旧多数组 alias guard
              → 拒绝：保留原 loaded source fallback
              → 接受：旧依赖 validator＋实际 candidate backend
                  → 实际 source/candidate memory 与公开出口对应
  → 语言 projected region contract／原源 progress／placement
  → CompCert backend → assembly
```

前一稳定性证书只保持原 public live temps，未表述新 cache 的值。候选要读取它，
因而这次从同一实际检查 execution 导出更强的入口关系：存在与原实际 Mint32 load
相等的缓存值，检查后保留 cache、参数、root 和 public live inputs。
这使用 kernel 已有的 accepted/refused entry relations；没有新增 kernel 字段，也没有
为迁就 frame-only helper 而重复读取 bound。关系在拒绝路径同样足以运输原 fallback。

Alias guard 的可执行性依赖完整 cached-source execution。本阶段仅在稳定性接受后
生产这项执行证据，再运行 alias guard；它不是检查安全的输入假设。
最终 P 保留原入口稳定性及与受保护输入关联的实际 alias-check reference。
候选从这个 reference 得到旧模型条件，使用同一 validator 和 candidate execution 定理。

## 使用者与三方责任

| 层次 | 本阶段新增／复用 | 使用者提供什么 |
| --- | --- | --- |
| 最小 kernel | 原 `guardify_preservation` 消费 guard certificate、局部 preservation certificate 和入口关系；源码未改 | 实例提交这些证书；核不认识数组、loop 或 cache |
| 语言库 | [检查写目标 checker](../prototype/interface/ClightCheckedTempWrites.v)；[保留入口关系的证书构造器](../prototype/interface/ClightMaterializedEntryCertificate.v)；已有 quiet determinacy、private safety、temp transport、实际 guarded choice | 构造器的执行／关系义务在本领域的 checked producer 中关闭，不暴露逐 body callbacks |
| 领域库 | [cache transfer](../prototype/interface/ClightLoadedAffineScanTransfer.v)、[候选局部证明](../prototype/interface/ClightLoadedAffineCandidate.v)、[组合 guard](../prototype/interface/ClightLoadedAffineMultiGuard.v)；复用旧 affine source/model、physical alias 和依赖 checker | 参数／操作／区间／private 名称提案；这些数据需通过检查 |
| 优化 pass | [checked factory](../prototype/interface/ClightLoadedAffineMultiFactory.v) 验证原 source key、cache allocation、整数 pool、guard/body syntax、候选与实际 code lowering | 不受信任 source 描述器和 candidate proposer；可以选择 mapped、schedule、tiling 等旧 checker 支持的 evidence |
| 语言 host | [region contract](../prototype/interface/ClightLoadedAffineMultiPreservation.v) 接实际小步；旧 loaded-region host 检查原源 progress、scope、placement、private allocation | 本次源符合 host 的真实 syntax/progress 检查；不以 bound 稳定性作为 fallback 进展假设 |
| 完整 compiler | [compile_loaded_affine_multi_regions_correct](../prototype/interface/ClightGuardedLoadedAffineMultiCompiler.v) 给出 `Csem → Asm` backward simulation | 用户 pass 提案；成功编译结论涵盖其输出，提案正确性无需可信 |

源描述器的类型是 `live → typed private pool → actual statement → option(parameters, proposal, bound pointer)`。
它不构造替代 source key；static checker 核对实际 loaded AST。
候选仍由旧 `affine_candidate_proposer` 提供。factory 检查候选 evidence，失败返回 `None`，
保持原程序；成功交出实际 guarded target 和已证明的 region contract。

Domain 是原 source 的有限正常完成，不预置 nonalias、未来稳定性或 cached completion。
支持根 signed32 repeated load、root=0／nonnegative bound 的动态 gate、checked canonical
任意有限 child 深度、参数化 affine bounds 和多指针 Mint32 operations。
局部 contract 只证明有限正常观察；整程序的进展／控制处理来自既有语言 host，
不能将这份局部证明扩称任意 divergence 或任意出口的通用 local equivalence。

## 核对的实例与证据边界

[具体 fixtures](../prototype/interface/ClightLoadedAffineMultiExamples.v) 核对：

- 原 loaded source key 接受，cached AST key 和重叠的私有 scan 名称拒绝。
- 三轴递归描述器和实际 source progress selector 接受。
- bound 与写目标自别名：真实源把 bound 从 2 写成 1 后停止；完整组合 guard 拒绝，
  实际 materialized-select 的原 repeated-load fallback 仍只执行一次并给出原最终 memory／公开出口。
- 同一 block 的相邻 aligned words：真实源两次写入完成；完整组合 guard 实际接受，
  生产 candidate P 和带捕获 cache 的入口关系。检查不执行 source stores，也不修改 memory。

这里的接受执行例是单数组写入，不能冒充不同 body bases 的新 runtime 验收；
多数组、递归 candidate 和完整 compiler 的一般证明与这些 concrete fixtures 分开记录。
尚无非空三轴完整执行 fixture，也没有本入口的新提取／真实 C／native 结果。
旧 native 矩阵没有重执行，不计作新增结果。

`make loaded-affine-multi-proof` 已通过：32 个新端点（2 语言、21 domain、9 fixtures），
692 个递归依赖和 1,021 个源摘要。新完整 compiler 与两条旧 compiler 回归均保持原 42 项假设；
语言端点仅在既有 CompCert 基线内，kernel composition 闭合，无新增全局公理。
前一 scan、旧 materialized compiler 和当前 cursor regression 的 source/object bindings 保持。

报告：`build/loaded-affine-multi/proof/report.json`，SHA-256：

```text
93421d4197c06c4eb29fed0b0d8ee775a571094644740a0baa5dc7f749f2cc5a
```

冻结报告不改写。独立新报告绑定所有新 proof sources／objects、审计脚本及继承报告，
Csem→Asm、candidate checker 的继承假设与语言-only 定理基线分别核对。

## 后续验收与 narrative 澄清

当前 compiler 证明关闭了 stability→cached source→alias→candidate→host 的缺口；
下一项仍是提取和实际 untrusted frontend adapter，完整 C 中非空递归候选／回退／上下文与 typed pool
安装证据。尤其要观测真正改变顺序的候选，不以 identity proposer 或 static descriptor 代替功能验收。

随后在已声明 affine 范围内改进 compact entry conditions：projection、range／footprint
包络或 certified sufficient-condition proposals。替换 guard 需证明 safety、acceptance soundness
和 private/public 入口运输，在契约仍成立时复用本次候选和 host 证明。
无需保持与旧 guard 完全相同的接受集，也不要求全局最优 guard。

生成代码大小、runtime 检查工作和接受范围分别测量。本次复用 cursor 形式的扫描，
没有消除逐点工作，也没有性能收益或作者负担减少结论。
CGO 2017 的具体 source／kernel、所需假设、启用变换、guard 成本、接受输入和 per-instance
人工工作仍要进行同例对照；frontend／算法／证明／具体语义的差距分别标明。
