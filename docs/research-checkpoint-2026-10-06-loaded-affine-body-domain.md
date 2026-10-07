# Deep affine＋loaded bound：从真实 body 生产地址许可与稳定性

2026-10-06。继 [body prefix／缓存运输](research-checkpoint-2026-10-06-loaded-affine-body.md)
之后，当前阶段实现递归 affine **body** 的语义、访问许可和写集合对应，
以及单点实际比较的安全域。重新 fetch 的 narrative 仍为 `7d94d81`，正文与
main 一致；继续按其最小 kernel／语言 host／领域库边界推进，完整目标 active。

## 实际证明链

```text
原 loaded source 的首次真实 body＋numeric 接受
  → 实际已用参数的 machine-word view
  → 更强的初始 loaded prefix

活动 prefix 的当前完整 body receipt
  → checked child Loop 模型的实际执行（包含全部递归 child loops）
  → 该 body 的全部实际点访问许可
  → 语言权限运输：这些地址在原 guard entry 也 valid／aligned
  → 当前 private cursor 的实际地址表达式可求值
  → 写地址与 loaded bound 的只读比较安全

模型写 trace＝这些点的写操作（不排除 alias reads）
  ＋ 所有点的写地址与观察字节分离
  → 实际完整 body 保持观察
  → 满足已有 loaded_body_preserved 接口
```

这里没有把完整缓存 root 源的完成、未来 body 的许可或 loaded bound 的
稳定性放在检查安全的前提里。缓存后的根循环仍须在整段 scan 接受后，
通过上一阶段的 transport 定理取得。

## 三方责任与已交付接口

| 层／文件 | 已证明的服务 | 输入与边界 |
| --- | --- | --- |
| 语言：[CellCapabilityTransport](../prototype/interface/ClightCellCapabilityTransport.v) | `memory_accesses_back` 运输 valid pointer 与字对齐 cell capability | 消费已有 assignment 权限定律；不假设观察值保持 |
| 语言：[CapableWordSeparation](../prototype/interface/ClightCapableWordSeparation.v) | valid／aligned 地址上的实际 pointer equality，接受推出 Mint32 字节分离 | 只读比较不要求 Writable；bound 端由实际 Mint32 load 许可；复用旧运行时代码 |
| 领域适配：[AffineChildBodyDecode](../prototype/interface/ClightAffineChildBodyDecode.v) | 固定包围坐标 prefix 的 checked leaf／递归 child 解码 | 实际 body 完成、numeric domain、word view、pointer frame；不要求整个 cached root 完成 |
| 领域：[AffineBodyCapabilities](../prototype/interface/ClightAffineBodyCapabilities.v) | 递归 child 模型的全部数学点具有实际物理 capability，并运输到 guard entry | coverage 来自 checked source trace；数学包络自身不授予内存权限 |
| 领域生产器：[LoadedAffineBodyDomain](../prototype/interface/ClightLoadedAffineBodyDomain.v) | 从原 source receipt 生产参数 word view／ready prefix；从当前 body 生产实际 Loop 执行与各点 capability | 复用 checked affine package、numeric certificate 和 pointer-register freshness；child model 是可计算的 option 编码 |
| 领域地址适配：[LoadedAffineBodyAddress](../prototype/interface/ClightLoadedAffineBodyAddress.v) | 为每个 checked access 在 private cursor state 生产实际比较 domain | 消费当前 prefix、point coverage、private cursor word view 与 pointer frame；这些 cursor 不执行源 stores |
| 领域：[WriteFootprint](../prototype/affine-nest/AffineNestWriteFootprint.v) | 任意有限深度 affine nest 的写 trace，及点写分离到 trace 写分离的对应 | 只要求 writes 与 bound 分离；reads 可以 alias bound |
| 领域适配：[LoadedAffineBodyStability](../prototype/interface/ClightLoadedAffineBodyStability.v) | 点写分离推出实际 body 的 load 保持，并构造 `loaded_body_preserved` | 写分离仍须由检查接受生产；不预置观察保持假设 |
| [Examples](../prototype/interface/ClightLoadedAffineBodyDomainExamples.v) | 三层 child model 构造、当前两次 body 分别 1／3 点、原 source 的 stronger prefix 实例化、具体 alias 比较域与拒绝 | 三层 prefix 是带实际源执行前提的符号实例；没有新增非空三层完整 compiler 执行 |

上述模块虽然有部分位于 `prototype/interface/`，其递归 affine 模型与
coverage 证明仍是领域实例的工作，不属于语言无关 kernel。语言层可复用的
权限与实际 pointer primitive 单独列出；全程序 host 和候选 checker 没有变化。

`affine_loaded_body_ready` 的 parameter view 不是用户另交的一项未经证明的
语义假设：生产器从原首次 body 推出它，再把 numeric 接受与初始 root=0
一起用于当前 body 的模型解码。支持范围保持 canonical affine child setup、
稳定参数／pointer registers、已 checked 的 Mint32 数组 body 和原源有限正常
完成。Numeric flag 的非空 first-path 限制保持；零次或 unknown 沿原 fallback。

## 尚未关闭的实际执行义务

本阶段尚未给出完整 recursive body check 的执行定理，也没有产生其
`BODY_CHECK` 证书、新的 compiler 入口、提取或 native 测试。

下一步应复用已有 general `affine_scan_execution` 的 **非空 coordinate
prefix** 能力，在 private root cursor 下执行 child scan，并将每个写地址的
接受组成 `affine_loaded_body_writes_apart`。已用的只读 prefix API 以
`decision_tree` 为检查体；private cursor scan 是实际 Clight statement。
两者不能直接视为同一种检查，须通过现行 materialized host 证明 root 扫描的
执行、public frame、结果与短路，随后消费同一 body preservation／advance。

Root 必须在当前 body 检查拒绝后立即停止，不能继续要求后续 body 的访问
许可。当前完整 body 的内部 points 已获实际 receipt 许可，可以复用递归
child 扫描；跨 loaded root header 的推进仍须等待本 body 的观察保持。
整段 scan 接受后，再接缓存源运输、旧跨数组 alias／依赖与候选 checker、
typed private pool、原 AST key／fallback 和完整 Csem→Asm 安装。

这项工作是在已有 kernel 可表达的义务内完成领域实现。当前没有证据要求
修改 kernel，或把语言安装与领域 assumption derivation 收进最小内核。

## 验证

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make loaded-affine-body-domain-proof
python3 scripts/validate_affine_nest_materialized.py
```

九个新增 `.v` 以 Rocq 9.2 编译。独立审计 25 个端点：4 个语言、16 个领域、
5 个 fixtures；绑定 674 个依赖对象与 1,001 份源摘要。新端点最多依赖 6 项
原 CompCert 假设，无新增全局公理；写 trace 与 capability 运输的相关端点
闭合。Kernel 闭合，两个当前 Csem→Asm 回归维持原 42 项假设；上一阶段 body、
numeric、materialized 与 current cursor 报告绑定的源码／对象全部不变。

历史 native validator 通过只是核对既有 5,118 调用的产物绑定；本阶段没有
重跑这些调用，也没有用它们验收新增 loaded＋deep compiler。

报告 `build/loaded-affine-body-domain/proof/report.json` 的 SHA-256：

```text
dd8896466da827d611738d17c95558db95d6cb14ac17774529b094d982512ed4
```
