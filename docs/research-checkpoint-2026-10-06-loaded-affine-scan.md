# Deep affine＋loaded bound：完整可执行的稳定性检查

2026-10-06。接续 [body domain 阶段](research-checkpoint-2026-10-06-loaded-affine-body-domain.md)，
本阶段把原 source receipt、numeric check、递归 child scan、root 拒绝短路和缓存源运输
连成实际 Clight 检查。重新 fetch 的 narrative 仍为 `7d94d81`，正文与 main 一致。
最小 kernel 和既有全程序 host 没有改动，完整多面体目标仍 active。

## 交付结果

现在可检查的源片段是一个每次 header 实际读取 `*bound` 的 signed32 根循环，
body 是 checked canonical affine nest，允许任意有限 child 深度、参数化 child bounds
和多指针 Mint32 读写。root 接受域要求初始 iterator=0、初次读取的 bound 非负；
这些要求由实际 runtime gate 检查，使用者不需把它们当作检查安全的输入。
整数包络／已用参数条件仍使用旧 checked affine package 的算法。

生成的检查执行以下步骤：

```text
原 loaded source 的真实初次 header
  → 安全读取并写入新鲜 private cache
  → 原首次 body 许可递归 headers／已用参数的 numeric check
  → numeric 拒绝：跳过全部物理扫描
  → numeric 接受：检查 root=0、cache≥0
  → gate 拒绝：写入 false，跳过全部物理扫描
  → gate 接受：以 private cursors 扫描当前 root body 的全部 child points
      → 比较每个写地址与原 loaded bound 的实际地址
      → body 拒绝：break，跳过 root increment 和后续 body
      → body 接受：byte separation → 当前真实 body 保持 bound
          → 运输实际源前缀，只许可下一 body
  → 整段接受：每个活动 body 保持 bound
      → 导出完整缓存源执行及原 public exit frame
```

cursor 只生成地址和比较，检查不执行 source stores。检查不改内存；
cache、cursors、Boolean 的改写在已证明的 public frame 下隐藏。
这里的“只读”指公开观察，不要求 private temporaries 也保持原值。

## 使用者接口与证明责任

[check_loaded_affine_scan_site](../prototype/interface/ClightLoadedAffineScanSite.v)
接收原 loaded AST、parameters／live、bound pointer 和 `affine_guard_proposal`。
proposal 仍只有语法、operations、区间、private control 名字与 result 名字。
它继承 numeric site 对原 source key、cache freshness 和 frameable syntax 的核对，
额外核对 pointer ports、body pointer freshness、child lowering、完整 scan namespace
以及 materialized 检查体／dispatch condition。失败返回 `None`。

描述器没有逐 body 的安全性、未来访问许可、non-alias 或观察保持回调。
源片段在语义证明中提供实际 finite normal completion；领域生产器据此取得初次
读取和当前 body 的证据，而不是要求调用者交出已经缓存的 root 循环执行。

| 责任 | 本阶段实现与证明 | 使用者还需提供的内容 |
| --- | --- | --- |
| 语言 | [ObservedWordProbe](../prototype/interface/ClightObservedWordProbe.v)：valid／aligned Mint32 地址上的实际 `One` 比较，Boolean 接受推出字节分离 | 具体地址证据由领域生产器取得；比较本身没有新 oracle |
| 语言 | [ShortCircuitPrefixLoop](../prototype/interface/ClightShortCircuitPrefixLoop.v)：private Boolean、拒绝 break、frame／result、接受时的全部前缀证据 | 通用 helper 的 BODY／ADVANCE 在 affine 实例中全部关闭，最终描述器不暴露这些回调 |
| 领域 | [ObservationLeaf](../prototype/interface/ClightAffineObservationLeaf.v)、[WriteTest](../prototype/interface/ClightLoadedAffineWriteTest.v)：只检查 writes；由真实当前 body 推出地址定义性和写分离→保持 | checked leaf 与 recursive model 仍限定允许的 affine／Mint32 子集 |
| 领域 | [BodyScan](../prototype/interface/ClightLoadedAffineBodyScan.v)：复用 general child scan，使用包围 root 的 private coordinate，证明实际全部递归扫描 | parameters、live 和 private names 的语法数据 |
| 领域 | [RootScan](../prototype/interface/ClightLoadedAffineRootScan.v)：逐 body 接受后推进真实前缀，并导出完整 cached source | 原 source execution receipt；不要求完整 cached source receipt |
| 领域生产器 | [ScanSite](../prototype/interface/ClightLoadedAffineScanSite.v)、[ScanExecution](../prototype/interface/ClightLoadedAffineScanExecution.v)：将 capture、numeric、gate 和 root scan 连成一段实际检查 | 源选择与 proposal；模型、域、实际安全证明由已验证库取得 |
| 已有框架／语言证书库的使用者 | [ScanCertificate](../prototype/interface/ClightLoadedAffineScanCertificate.v)：产出当前 `guard_certificate`，包括安全、defined dispatch、全部完成检查的 soundness 和 accepted/refused frame | 该实例仍以原片段正常完成为 D；没有新增 kernel 字段 |

`loaded_affine_scan_site_certificate` 的 D **只有原 source completion**。
numeric math、snapshot、root=0、count 非负以及每个 body 的 bound preservation
全部由实际检查和源证据链生产。
`loaded_affine_scan_presumption_cached_source` 消费这些事实，给出缓存后的源执行，
保留同一最终 memory，并只隐藏新鲜 cache 的 exit 值。

这是稳定性前提服务，尚未给出新的候选重排或全程序编译入口。优化方仍须消费
旧候选／依赖 checker，完成 source/candidate correspondence；Clight host 再提供
private resource allocation、原 fallback 和 program/backend installation。

## 具体执行与边界

[ScanExamples](../prototype/interface/ClightLoadedAffineScanExamples.v) 已通过：

- 三层 affine 源可由新描述器选中；缺少 body pointer port 时静态拒绝。
- 四字节真实 allocation 的零次迭代：child 参数与 body pointer 未定义，整段
  capture＋numeric＋gate／scan 检查仍安全完成并拒绝。
- 源初次 bound=2，body 把同一物理字写成 1：真实原循环运行一次即退出；
  新完整 guard 实际执行并拒绝，不需要许可第二个 source body。

[AcceptExample](../prototype/interface/ClightLoadedAffineScanAcceptExample.v) 使用真实八字节
allocation：bound 位于 block 1 的 offset 0，write pointer 位于同一 block 的 offset 4。
真实原源执行两次 store；完整 guard 接受、保留 memory／public temps，并实际导出
缓存源执行。这不是“不同 block 才接受”的检查。

检查不用逻辑 cell identity 的静态捷径：观察字本身被写入时必须拒绝，即使其
logical cell 与写 cell 恰好一致。只有 writes 必须与 bound 分离，reads 可 alias。
一个当前完整 body 已许可其内部全部 points，因此 child scan 可在 Boolean 已 false
时继续该 body；root scan 必须在 body 拒绝后停止，才能避免未获许可的未来 body。

仍未新增非空三层源的具体完整执行 fixture、编译入口、提取或 native 运行。
typed pointer-store body、多观察 dependent header 和任意 Presburger 域未由这个实例覆盖。
该 certificate 不宣称支持原片段发散；已有 open-host 案例保留其独立语义边界。

## 验证记录

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make loaded-affine-scan-proof
```

[audit_loaded_affine_scan.py](../scripts/audit_loaded_affine_scan.py) 审计 11 个新增 `.v`：
38 个端点＝6 个语言、19 个领域、13 个 fixtures；682 个当前依赖、1,012 份源摘要。
所有新增假设都在 CompCert 原有基线内，最大端点 6 项，minimal kernel 端点闭合。
两个既有完整 compiler 的 42 项假设保持；body domain、body、numeric、materialized
和 current cursor 的源／对象绑定在本轮前后保持。

报告：`build/loaded-affine-scan/proof/report.json`。
SHA-256：`cf590478290ed885b636d3e591db15e6c7715968b396e9c052ab477d5df17e51`。
Rocq 9.2／Stdlib 9.2、固定 CompCert v3.18。没有新增公理或改变旧 compiler。
既有 5,118 次 materialized native 调用仍是历史证据，本轮没有重跑或累加。

下一项验收是将新稳定性 producer 的 cached-source receipt 接到旧多指针 alias
guard 与 candidate checker，分配 typed private pool，保持原 loaded source key／fallback，
再接完整 Csem→Asm、提取和真实 C 的接受／拒绝／上下文验证。完整 goal 继续 active。
