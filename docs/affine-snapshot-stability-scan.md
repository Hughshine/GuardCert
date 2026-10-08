# N/M 稳定性检查与原源到缓存循环的完整运输

2026-10-08，本阶段接续 [原 loaded setup 的许可与 preparation](affine-header-snapshots.md)。
三个新模块共 462 行已编译；独立审计 11 个端点、1,314 个摘要绑定，至多
旧基线六项 globals，无新增公理。下面记录实际检查定义与定理边界。
它们仍是语言/domain
库的交付，尚未在新 checked factory、提取 compiler 或 native 程序中安装。

## 具体输入、检查与结果

原 source 仍是 `i<*N; K=i+*M`，leaf 使用既有 checked affine-pointer body。
前阶段 capture 先捕获 N，原首次比较 active 时才捕获 raw M；numeric
preparation 检查 row、affine width 与 body arithmetic，建立 `ready`。
新检查消费这些实际入口事实与 unchanged original source 完成执行：

```text
original source + conditional N/M receipts + numeric ready
    -> reached original row i and its physical write permissions
    -> check writes of row i separated from captured N cell
    -> if accepted, check writes of row i separated from captured M cell
    -> if accepted, prove observations survive original row i
    -> license row i+1; stop later rows on refusal
```

每次 probe 比较的是实际物理地址，消费 capability/alignment 和数学到机器
地址对应。原 source 的写权限由 reached row 生产，不能从 rectangular box
或抽象 nonalias 假设推出。检查本身不执行原 stores；proof prefix 中的
source execution witness 用于到达和权限证明。

新 `affine_snapshot_scan_tree` 是具体有限 decision tree，tests 使用真实
Clight expressions 和 `decision_run` 的实际表达式求值。它复用 readonly
short-circuit composition，保持整个 check entry；没有在本阶段新增
lowering、私有 flag allocation 或 selected installation。静态 fuel 来自
checked row limit，活动比较来自捕获的 N。接受结果是充分条件，不要求其
false 等价于“不稳定”。当前算法仍枚举实际 points，并非紧凑 range 条件。

## 定理、requires 与责任

| 交付 | 调用前提与保证 |
| --- | --- |
| [ClightAffineSnapshotRowChecks.v](../prototype/interface/ClightAffineSnapshotRowChecks.v)：`affine_snapshot_row_domain` | 当前原 prefix、active row、对应初始 cell receipt，和 checked package/static shape。复用前阶段 concrete decoder/write receipts 与旧 arithmetic/access services，自动生产单 pointer row-probe 的完整 domain。 |
| 同文件：`affine_snapshot_row_condition` | 在原 prefix 的 active row 上，readonly 地先检查 N、接受后检查 M；安全、available、same-entry，接受得到两项 write separation。普通 false 不提供 stability 的否定。 |
| 同文件：`affine_snapshot_row_condition_preserves` | 消费 row condition 的 accepted fact 和当前 source prefix，导出每个原 physical point 对 N/M observations 的 load preservation。Separation 充分性由既有 memory store 定律承担，不作为抽象 callback 输入。 |
| [ClightAffineSnapshotScan.v](../prototype/interface/ClightAffineSnapshotScan.v)：`affine_snapshot_scan_spec` / `affine_snapshot_scan_condition` | Concrete decoder、actual row condition 和 physical permission transport填满共用 `observed_body_prefix` 的 ports。Safe domain 是 conditional original domain 加 numeric ready；每个 row 接受才推进 next prefix，拒绝跳过所有 later rows。接受建立全域 `affine_snapshot_point_preservation`。 |
| [ClightAffineSnapshotTransport.v](../prototype/interface/ClightAffineSnapshotTransport.v)：`affine_snapshot_loaded_to_cached` | Ready、初始 current observation relation 和 pointwise preservation law。复用 `strict_active_loop_transport`，同时替换 actual root test 与 loaded body header，产生相同 trace、完整 temp exit 与 memory 的 cached loop execution；body decoder 是 concrete checked affine decoder。 |
| Scan 文件：`affine_snapshot_scan_accepted_cached_source` | Conditional original domain、numeric ready、实际 scan 接受。它从 unchanged original source 导出 complete cached source execution 和相同公开出口，自动提供运输所需 point law。调用者不再需要预先证明 complete cached source。 |

整段运输的 lemma 接收 point law；本阶段还实现了生产该 law 的实际条件，
并连接接受到 complete cached source。不能把单个 transport theorem 的
参数当作用户已经交付的 guard，但也不能忽略这个 concrete producer。

Kernel、host contract、candidate checker 和源码用户 API 均不变。Language
作者提供 actual load substitution、readonly/prefix execution、memory/public
frame 与 loop transport；domain 作者消费 separation/arithmetic/store 定律。
Factory 作者下一步把普通 checked source descriptors 自动变成这些静态
证据，连接候选 guarantee；language host/site 继续提供实际 progress、
placement、resources、continuation 和整程序 installation。

静态前提仍包括 checked affine package、header word grammar、cached-body
shape equality、N/M pointer identifiers 与 row/column/K 的保护关系，以及
Mcache 在 stable ports 中。捕获的 typed/fresh 私有 caches 在最终 source
factory 中由 allocator/site 提供。源码用户不应该手填这些证明或 semantic
callback。这里没有任意 source/candidate 的 assumption extraction。

Finite completion 边界保持：safe domain 使用原 `E0 / Out_normal` 完成
执行，不保证任意入口终止，不自动覆盖 open/diverging host。旧 preparation
仍要求首个 child positive；first-empty-child、general recursive loaded
domain 与 scalar/chunk 扩展未由本阶段解决。这里的 header stability 也
不替代候选所需全部 data-dependence/nonalias 条件。

## 验证与下一实际连接

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python scripts/audit_affine_snapshot_transport.py --validate
```

独立 proof report 绑定新模块可达 source/object closure、父 snapshot
report、compatibility report、helpers 和全部保留 build attempts。报告
`build/affine-snapshot-transport/proof-v1/report.json` 的 SHA-256 为
`c268a14e15924706a11863be23b3e1cc8fb527d0ef47d5caf2f1fbe5df556e79`。
11 端点、0 closed、1,314 绑定、至多原 allowed baseline 的六项 globals；
父 snapshot report 的 1,332 个绑定也复核。13 次 build snapshots/logs
保留并绑定：3 次成功、10 次 proof-source 拒绝（imports、名称和参数/tactic
用法），不是 native 误编译。成功输入冻结；
本次不重跑祖先 native 矩阵，不增加 guard 工作量/成本或作者时间结果。

下一连接按实际依赖顺序进行：

1. Checked source adapter 核对原 `K=i+*M` AST，自动构造 private cached
   affine package、grammar/shape/protected-port 证据及 typed fresh caches；
   保留原 row reset、label/site 与公开 i/j/K 出口。
2. 在实际 guard exit 上消费本阶段 accepted cached completion，运行既有
   alias/candidate checks，复用 source/model/candidate 定理；任何拒绝路径
   执行原 repeated-load source。Empty outer path 继续跳过 M capture。
3. Factory/selected host/Csem→Asm、提取和 original marked C 验收：接受、
   N/M header alias 改变次数、无效 M 的空外层、wrapping/cap、continuation
   与多个 sites。之后继续 compact sufficient conditions 与完整成本。

## Narrative c4b1395：方向与前提来源

本轮重新 fetch 的 narrative 增加的是呈现澄清，不新增实现任务或重命名
定理。`affine_snapshot_loaded_to_cached` 的方向是给定原 loaded Clight
执行与充分前提，构造 cached Clight 执行；`affine_snapshot_scan_accepted_cached_source`
进一步从实际 check 接受生产该执行。两者不是独立的双向 equivalence，
也尚未证明本族完整 Clight→Loop→transformed Loop→candidate Clight 链。

后续 cached Clight→source Loop 应接既有
[GuardMemoryAffineInnerPointerRegionSource.v](../adapters/compcert-memory/GuardMemoryAffineInnerPointerRegionSource.v)
的 `memory_affine_inner_pointer_region_source_under_ranges`，再接 checked
polyhedral transformation 和 candidate execution/public-exit 定理。现有
[multi_tensor_source_region_decode](../adapters/compcert-memory/GuardMemoryMultiTensorSourceRegion.v)
也只是其 supported active rectangular family 的 Clight→Loop 方向；
不能因为名字是 decode 就理解成 parsing 或双向等价，更不能迁移其源族范围。

本阶段静态前提由 package/shape/resource checker 负责，动态 ready/receipts/
preservation 由 preparation、capture、scan 与运输负责；原 source 完成执行
是证明的语义起点。没有 runtime source pre-execution，也不要求每个 theorem
前提都对应一项 emitted test。最终 compiler 仍须自动交付适用前提。

目标保持 active；本阶段不是 OLO 原例完整安装或新族 end-to-end 完成。
