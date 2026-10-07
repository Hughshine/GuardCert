# 验证责任、证书边界与最难的验收

2026-10-07 最新：[source-only reproduction](nested-frontend-reproduction.md)已从
锁定源码重建既有 compiler／运行路径，独立基线查询替代历史报告输入；kernel
与证明责任划分不变。[constant-word observation](constant-word-observation.md)
由语言库证明 typed `Mem.store` 保持和 actual Clight BODY checker soundness。
这是 fixed-address memory guarantee，不能替代 pointer-binding frame、读许可、
prefix／model 对应或候选正确性。Domain 后继 [same-word producer](nested-word-model.md)
已生产实际 subloop 保持、cached source／canonical 模型和两次比较的 Clight check，
接受后明确模型入口到 actual check exit 的 ports frame。它复用旧 source-derived
capture／numeric／helper receipts；不是新的 kernel 功能。后继
[same-word compiler](nested-stability-compiler.md)已完成实际 physical guard、
multi adapter、typed factory 和完整 Csem→Asm entry。新 guard certificate 直接
消费原 `ncs_multi_local_certificate`，经原 kernel 和语言 host 安装；域实现承担
实际 source/model 及 model-entry→check-exit frame。19 端点／597 依赖独立审计、
提取、完整数组和四个真实汇编 alias 路径探针通过，没有新增使用者语义回调。
同输入 old/new 对照分别记录局部检查工作、接受和代码增长；完整 timing、
更广条件与作者工作量仍待验收。最困难的证明环节仍是安全 capture、实际模型
对应及入口运输，不能用两次 Boolean 比较替代。

2026-10-07 后继：[nested frontend BODY／contexts](nested-frontend-coverage.md)在
同一 compiler 上扩展了实际读写、dependence、重复 sites 与程序上下文验证。
更强 child-count∈[1,2) profile 使 chain 的重排被同一 checker 接受，runtime guard
在前提外保留原 AST。这个使用过程保持三方责任：优化方提出候选和 profile；
domain checker／producer 证明条件正确性及入口到模型义务的覆盖；语言库解释
安全 capture、检查、实际状态运输和 region 安装；kernel 消费既有证书。
三方是证明归属，四个 certificate links 是逻辑环节，不增加四份用户手填 record。

重新 fetch narrative `271f6fc` 后确认 main 正文一致。下一项紧凑条件工作必须
分别提交安全、accepts⇒所需义务和入口状态运输的证据，复用现有 C_opt／host；
整程序安装继续由语言实例与具体 region／site 证据共同完成。当前没有 generic
WP、最优 guard、任意 contract-clause 组合或第二 IR 实现；成本／作者负担待测。

以下为先前固定阶段；其后继待办以本段及最新 checkpoint 为准。

2026-10-07 最新实运行：[actual nested frontend](nested-frontend-native.md)已在既有
Figure 2 适配源实际安装并运行 interchange／tiling；zero-index root 和 prefixed
resets 的执行对应由语言库证明，fallback 保留原 AST。新 Csem→Asm entry 已提取；
75 full assembly calls、16 Clight dispatch calls 与 6 machine probes 单列并通过。
Kernel 未改，三方责任／四条证书链保持。下面旧阶段与原 16-call `not-supported`
报告固定保留其当时范围；当前能力以新 native 报告为准，仍无 compact 条件／
成本／完整 BT layout／作者工作验收，完整目标 active。

2026-10-07 最新后继：[nested guarded candidate／compiler](nested-constant-multi.md)
已连接实际 canonical source→alias guard→candidate→kernel preservation→projected region
contract→typed factory／语言 host→Csem→Asm。Model anchor 及实际 checked-entry frame
由执行 receipt 生产，没有 source/model 语义回调；kernel 不变。三层原 AST 的 host
progress 支持有 fixture。后文阶段记录保留当时边界；新入口的 extraction／实际 C
识别和非空数组非 identity 优化运行仍待验收，原 Figure 2 16-call report 不变。
Narrative 重新 fetch 到 `271f6fc`，正文与 main 一致；三方责任和四条证书链按新文档核对。

这是当前活动目标的一部分，按用户的补充要求维护。研究叙事沿用 `topdown/research-positioning` 的 [paper narrative](topdown/paper-narrative.md)，10 月 7 日重新 fetch 并读完 `271f6fc`，main 正文一致。该稿是方向；本文区分已经实现的设施、使用者还需提交的证明和后续验收。完整多面体目标仍未完成。

最新澄清已采纳：最小 semantic kernel 止于局部 guarded correctness；只读前台、条件组合、prefix scan、simplification 和 assumption derivation 是核上的库。完整程序安装属于 language/IR host，generic lifting record 只是组合入口。这里的“框架责任”包含可复用库，不等于这些服务全部属于最小 kernel。此边界不要求重排文件；只有真实 optimizer／host 暴露无法表达的语义义务时才考虑修改 kernel。

[当前源码核对](narrative-implementation-check-2026-10-06.md)已更新到 `fa8cbd8` 及本轮后继，
并记录 [实际 BODY joint scan](constant-body-joint-scan.md) 和 inner loop 的连接。语言库提供
observer expression receipts、真实 pointer comparison、private Boolean 积累和
store-load 保持；domain 从已到达的原 `<5` BODY 许可全部写地址比较，证明完整
子域覆盖和接受后保持所有 observations，填入 inner-prefix preservation／advance。
30 端点审计保持，kernel 不变。[Inner loop 后继](constant-joint-inner-scan.md)已将
检查 producer 接到真实短路循环，并从整行接受直接生产全 column 的 preservation
和 outer-prefix advance。固定入口的 header 定律足够，不要求任意无关入口的 cache
对应。[Outer 后继](constant-joint-outer-scan.md)现已接通真实扫描和全部 rows
preservation，导出同出口／memory 的整段双缓存源。14 端点／565 依赖审计保持，
无新增语义 BODY／PRESERVE 回调。[Canonical 后继](nested-constant-model.md)已证明实际三层
source transport 和 checked-package Loop 内存解码，静态 leaf/frame 输入在
该实例内部生产。[原源 numeric 后继](nested-constant-numeric.md)现已从首次实际
leaf 和 checked 参数使用生产定义性，运行 ordered capture／双 gate，接受后
生产逐点 DOMAIN／SOURCE_WORDS；新服务不要求调用者预设这些事实。
24 端点审计通过。[Checked entry 后继](nested-constant-site.md)已生产原 AST／
scope／namespace 的静态证据，并由实际检查接受生产当前入口的 observers 和
初始 prefix；两项具体 header 定律复用实际 raw receipts。代码对 observer ghost
fields 不敏感，有完整 AST 等式；入口 ROW0 通过 runtime gate 检查而非 context
语义前提。37 端点审计通过。[完整 physical guard 后继](nested-constant-physical.md)
已执行 helper 准备并填入全部 outer inputs；接受生产真实 canonical/Loop source
执行，明确 model entry 到 actual guard exit 的 frame。39 端点审计通过。语言
服务原有实现被 domain 实例消费；kernel 不变。安全域为原源 silent normal
completion，candidate 跨入口、dependency/alias guard 与 host progress/divergence
安装仍须完成；完整 header-stability guard 不等于完整 guarded candidate rule。
`ENCODE`／`PRESERVE` 等参数本身仍不是能力，须逐个
记录其 producer；这次没有把未完成的整段 guard／factory 计作已经自动取得。

验收继续按 `226ba94` 的 proof-first 顺序；compact 条件、实际检查成本、有用
接受域和实例作者工作是最终要求。`271f6fc` 的并行写作已落实到
[LNCS 稿件](../paper/README.md)，每个相关实现阶段同步正文及证据。
以下后继段落保留各阶段的固定能力边界；当前缺口以上述核对及工作计划为准。

[最新 numeric producer](research-checkpoint-2026-10-06-loaded-affine-numeric.md)已按该限制实现：语言从原 header 提供安全 capture／temp 运输与真实 first body；domain 将 receipt 接到旧递归 headers／已用参数及 numeric/profile 编码；当前 certificate 库负责 primitive safety、defined dispatch 和全部完成检查的 soundness。静态 site checker 绑定原 loaded AST 和 cache freshness。25 个新端点通过，kernel 不变。Prepared-entry snapshot 是当前读值，由 producer 取得；不是未来稳定性。扫描 coverage、字节级观察保持、conditional candidate 和实际语言安装仍是后继义务，不能从这张 numeric certificate 推出。

[body prefix／缓存源桥](research-checkpoint-2026-10-06-loaded-affine-body.md)进一步划清复用责任：语言统一从 actual structured body 证明权限运输和 protected-temp frame，prefix library 组合 domain 的逐 body check，语言再从已证明的观察保持取得完整缓存源执行。递归 affine adapter 复用 checked package，增加 loaded/body pointer register freshness 核对；domain 仍须生产实际 body 的全部访问许可、覆盖和 byte separation，并构造 `BODY_CHECK`。34 个端点及 alias 源／拒绝／具体 allocation fixtures 通过；不是新的完整 recursive physical scan 或 compiler。

[body domain 阶段](research-checkpoint-2026-10-06-loaded-affine-body-domain.md)已生产上述实际访问许可与写 coverage：原 first-body receipt 提供参数 words，当前完整 body 提供递归 Loop 执行，语言权限运输把实际点 capabilities 带回 guard entry；领域地址适配许可 private cursor 的实际比较。点写分离经真实写 trace 推出 body preservation，reads 可以 alias bound。25 端点审计通过，kernel／旧 host 不变。领域库仍须证明完整扫描覆盖与检查执行／接受结果；语言 materialized host 负责其 private frame、结果和 root 短路实现，之后完整程序安装继续由现行 Clight host 承担。单点比较域和写 footprint 不算已经完成该扫描或 compiler。

非矩形 pointer 阶段的具体归属见 [接入设计](affine-pointer-domain-next.md)：kernel 保持不变；语言提供 stable frame 的 counted-loop decode、实际 first-body 到达和公开游标恢复；domain 提供实际 ragged 点集、pointer body 模型对应、访问覆盖与充分条件推导。candidate checker 仍独立证明域／重排合法性。[完整条件](research-checkpoint-2026-10-06-affine-pointer-alias.md) 从真实 source prefix／有限正常源执行生产 D；[新 compiler](clight-affine-inner-pointer-compiler.md) 已进一步组装两套 candidate ranges、独立 certificate、实际 lowering／restore 和 local contract，消费已有 progress／placement host 接到 Csem→Asm，不归作 framework 自动发现优化前提。

[完整 scan 后继](research-checkpoint-2026-10-06-loaded-affine-scan.md)已关闭前段的检查执行与接受结果义务：语言提供实际 Mint32 地址比较和 root 拒绝短路；领域库用当前 body 的真实许可实例化递归 child scan，并在 body 接受后推进实际源前缀。静态描述器将 capture、numeric、runtime gate 和全部 scan 合成一段代码，没有逐 body 语义回调；现行 certificate 库以原 source completion 为 D，给出安全、分派、全部完成检查的 soundness 和 public frame。接受导出完整缓存源执行与同一最终 memory。38 端点审计及真实自别名拒绝／同 block 接受通过，kernel 和现行 host 不变。优化方仍须连接候选 checker；完整程序安装、typed allocation、提取和真实 C 是后续语言／使用者验收，不从这张稳定性证书推断已完成。


[候选／compiler 后继](research-checkpoint-2026-10-06-loaded-affine-multi.md)关闭上一段当时未连接的
candidate 与完整编译证明：语言构造器支持 kernel 已有的 arbitrary entry relations，携带新 cache；
domain 从稳定性接受生产真实 cached execution，再运行旧多数组 alias，取得旧 candidate validator／backend
的实际执行与出口。checked factory 接受数据提案，语言的既有 loaded-region host 独立核对原源 progress
和 private placement。32 端点审计、新 Csem→Asm 与旧两条 42-assumption 回归通过，旧对象绑定保持。
最难关闭的是 cached completion 只能是 stability 的结果而不能是 guard safety 的假设；整个连接没有新增
kernel 能力。该阶段当时尚未验收 frontend／提取／新 native；后继结果如下，成本和作者负担仍待验收。

[可运行后继](research-checkpoint-2026-10-06-loaded-affine-multi-native.md)关闭上述运行缺口：
不受信任 frontend 只提出 source metadata、cache 和 candidate；checked factory 仍绑定实际 source AST。
语言层保留完整 typed allocation，候选资源池剔除受保护 cache 所在 pair；domain 的原 disjointness
checker 与候选证明继续负责安全，无新 kernel 接口。六配置 624 次 C→assembly 调用、208 次
Clight 路径调用和 21 个未修改汇编探针确认非空递归重排、多数组、两次 rewrite 及原 loaded fallback。
独立证明报告绑定资源修复后的 factory，前一报告不改写。下一项是 compact guard 的安全、接受与
入口运输，不能仅凭包络的数学正确性或 runtime 成功推断这些证明已经完成。

narrative 本轮更新为 `226ba94`：先闭合约定范围的证明链，然后改进条件推导／生成；scan 是中间实现。
自动化／可用性是最终要求。代码大小、运行检查成本和接受域分开评估，具体同例对照仍待完成。

[后继 guard 简化](research-checkpoint-2026-10-06-loaded-affine-reduced.md)把接受事实的复用落到当前
domain library：`affine_first_path_flag_frame` 根据 header dependencies 运输事实，未来 child controls
无需一致；语言的 protected-temp entry relation 提供输入 frame。`affine_multi_alias_only_execution`
在已证 numeric=true／result=true 下执行实际 residual scan。优化方继续提供原 metadata／candidate，
不新增每个实例的语义回调；factory、候选 P、local rule、host 和 kernel 不变。
此为具体 domain 的 residualization，不称通用 assumption extraction 或完整 guard minimizer。
35 端点、当前新 native／路径通过；旧 native proof/object binding 保持历史。
工作量探针证明 point／point-pair comparisons 没有减少，Figure 2 的组合源也未安装优化。
后续职责与难点见 [具体覆盖差距](olo-figure2-coverage.md)。

## 1. 三方各自证明什么

“框架提供 conditional correctness 接口”不表示框架替优化作者证明任意候选正确。“语言提供语义”也不表示每个优化作者都要重新证明语言的 if、load 和上下文定律。

| 责任 | 需要提供／证明 | 可以复用的交付 | 不由这一方自动解决 |
| --- | --- | --- | --- |
| 语言无关框架 | 最小 kernel 消费证书、证明局部 guarded rewrite；上层库提供条件组合／短路／安全后处理，并消费 host 安装证书组合有限次 rewrite | 参数化生成／简化算法的正确性；readonly 前台；消费语言安装定理的通用组合 | 哪个优化成立、任意语义命题的检查代码、具体语言的 guard 或上下文定律 |
| 语言／IR 实例 | 实际执行与观察；原子测试的机器语义和定义性；具体分派；私有资源与状态运输；effect／frame；合法位置／出口／小步匹配；后端连接 | 一次证明并供多条规则调用的原语、direct/shared 实现和 host；例如真实 `Mem.load/store`、temp agreement 与 CompCert simulation | 某个程序的足迹完整性、某候选的依赖保持、某处入口为什么具备所需事实 |
| 优化实现者，含 domain library | 寻找片段、提出实际候选／模型义务 A；候选条件正确性；入口条件 B 对 A 的覆盖；实例专属源／模型／候选对应和作用域证据 | 经验证的 candidate checker、受限投影／范围／足迹算法及证书；这些可以在一个领域内再复用 | 未证明的 oracle 答案不会因接入框架而获得正确性；没有一般 `extract_assumptions(S,T)` |

框架的组合证明以已经证明的语言定律为参数。优化实现者既可以直接提交证明，也可以提交不受信任候选、条件和 witness，由已验证 checker 产生证书。候选生产器和搜索启发式无需可信；成功输出仍必须绑定**实际** source、candidate、condition 和安装位置。语言、domain、核心的证明可以由同一开发者写，但接口和成本归属保持分开。

语言库可以提供“实际字节足迹分离 ⇒ load 穿过 store 保持”的定理；规则作者证明本次 body 的访问属于这些足迹，并满足权限／chunk 条件。核消费这个证据，不了解指针，也不允许只把 `p!=q` 当成任意字节区间分离。

最新 topdown 补充也已采纳：抽象接口应能由 SSA／CFG 或汇编实例解释，Clight 继续是主验收。CFG 实例另证明 live-out／phi／控制出口；汇编实例另证明 scratch registers、flags、memory 和分支控制。若实际检查改变 flags，语言不能只说逻辑 condition 是只读：必须证明这些变化私有且不影响分支，或给出保存／恢复与真实状态运输。第二 IR 是可选的表达力证据，当前没有宣称已经实现，不把它加入主功能的强制验收。

Clight 的 readonly tree／单 Boolean realization 与循环式私有 footprint 扫描有不同的检查状态。扫描后的游标可能依赖 memory 和拒绝位置；语言无关 host 已允许实际 checked state 和入口关系。10 月 6 日的 [公共 private-scan compiler](clight-private-check-migration.md) 已完成这条实例化，不将它描述成任意 stateful 检查的通用合成器。

本阶段分工可以在源码中核对：[Safety](../prototype/interface/ClightPrivateScanSafety.v) 和 [Host](../prototype/interface/ClightPrivateScanHost.v) 由语言解释实际求值、有限循环续行、结果解码与任意完成分支的 exact dispatch；[Preservation](../prototype/interface/ClightPrivateScanPreservation.v) 提供公开观察、分支 temp 运输，并调用既有 kernel 的 `guardify_preservation` 和小步安装。domain 的 [Certificate](../prototype/interface/ClightParamPointerCertificate.v) 提供实际 source-derived D 下的扫描安全、protected frame 和 `accepts⇒P(original)`；候选对应和依赖核对继续由优化方的旧数学证书承担。source／candidate 的实际表和 private pool 接到了 Csem→Asm，并完成提取和原生验证。

`check_safe` 使用覆盖已到达 `eval_expr`、if 测试和有限 loop 续行的归纳判断；它不是完成见证的改名。实际 bounded scan 的既有执行与确定性可构造该判断，再由语言定理推出可用性。保护集同时覆盖公开入口与前提所依赖的 header、参数和 pointer binding，语言无需知道这些维度的具体意义。局部保持接口观察完成的 silent normal region，完整程序结论是 backward simulation；没有新增任意无限 pointer fallback 宿主。38 个端点和实际运行的证据见 [阶段记录](research-checkpoint-2026-10-06-private-scan-compiler.md)。

## 2. 四张证书与一个安全域

下面四项是逻辑环节，与上述三方责任不是一一对应，也不要求每个使用者手填
四份 record。库与 checker 可以共同生产一个环节的证据。这里 `C_host` 表示
实际 guarded choice／checked-state 运输；region 安装与具体 rewrite site 的合法性
仍在后续独立验证，不能把分派 law 当作整程序定理。

对真实 source S、candidate T，区分局部／模型义务 A、入口语义条件 B、实际 guard G，以及 G 可以有定义地执行的域 D：

```text
源路径／placement 证据 ──► D
                         │
                   C_guard: 在 D 中安全、可用；G accepts ⇒ B
                         │
                   C_derive: 在 D 中 B ⇒ A
                         │
                   C_opt: 在 D 且 A 中 T 对应 S
                         │
                   C_host: 实际分派与状态运输
                         │
                   语言安装定理＋实例 region／site 证据
                         │
                   guarded program ──► CompCert 后端
```

D 不能预先包含待检查的 no-alias／稳定性事实。它说明当前哪些观察可安全取得；后续观察可以依赖已完成检查的正结果。false／unknown 只触发回退，不承诺 B 的否定。语义充分条件可以保守加强，因而 `C_derive` 不要求最弱条件或逻辑等价。

| 证书 | 主要生产者 | 当前可核对的接口／证据 |
| --- | --- | --- |
| `C_opt` | 规则／优化实现者或已验证候选 checker | [conditional_equivalence](../prototype/interface/GuardedRewrite.v)、局部状态还原；完整循环也可使用 [open_region_protocol](../theories/ClightOpenRegionContract.v)，须提交实际执行的匹配 |
| `C_derive` | 优化／domain library | [readonly_condition_entails](../prototype/interface/GuardedRewrite.v) 消费推导证明；[盒状 affine 包络](affine-box-condition-derivation.md) 提供受限符号算法及实际宽度使用者，不是通用投影算法 |
| `C_guard` | 框架上层库＋语言原语＋实例域证据 | [只读 tree 合成](../prototype/interface/ClightReadonlyTreeSynthesis.v)、[loaded tree](../prototype/interface/ClightReadonlyLoadedTreeSynthesis.v)、[依赖 prefix scan](../prototype/interface/ReadonlyPrefixScan.v)、[实际 private-scan host](../prototype/interface/ClightPrivateScanHost.v)；实例仍证明 coverage、原语安全和 source 支持 |
| `C_host` 与后续安装 | 语言实例证明 choice／运输定律及安装；优化／site 提供 region 与 placement witness | [select_exact](../prototype/interface/GuardInterface.v) 与 [实际 realization](clight-guard-realization.md) 解释局部分派；[direct](../prototype/interface/ClightReadonlyProjectedCompiler.v)、[shared](../prototype/interface/ClightSharedProjectedCompiler.v) 和 [open host](../theories/ClightOpenRegionProof.v) 另证具体安装；完整 Csem→Asm 结论是 backward simulation |

这些是逻辑责任，不强迫每个使用者填四个重复的 record。可以将证书封装在一个已验证库中；验收仍逐项回答它们来自哪里。不能把 normal-completion 的 big-step 观察接口说成已经观察了全部无限行为，也不能把实际 forward 小步安装证明改称任意目标执行的双向等价。

证书的方向也要和宿主一致。核已经分别提供 refinement 与 preservation；`readonly_projected_clight_rule` 要求双向局部等价，但 private-region 安装实际消费的是源执行到候选执行的一边。旧 [encoded_private_rule](../theories/ClightPrivateRule.v) 及 [named candidate compiler](../adapters/compcert-memory/GuardMemoryNamedCompiler.v) 主要交付条件性 source-to-candidate 保持，并且局部端点量化实际 program 的 globalenv。10 月 6 日新增 [readonly_preserving_clight_rule](../prototype/interface/ClightReadonlyPreservation.v)，直接消费这一保持证书；双向规则和保持规则共用实际安装证明。真实 [named affine／tiling 使用者](clight-polyhedral-preservation.md) 已经连接候选／依赖核对、只读合成、direct/shared 分派与 Csem→Asm，没有要求旧 checker 提供未证明的反方向。统一 realization 复用分派／运输，optimizer 仍承担实际模型对应和入口覆盖。

## 3. 用当前完整循环逐项落实

实际例子是 [unsigned memory-bound 缓存](clight-guarded-circular-case.md)：

```c
for (; i != *bound; ++i) *out = i + 2U;
```

候选先私有缓存 `*bound`，随后用 cache 作相同循环的测试。这里允许 unsigned wrap；不是把所有循环都强加 no-overflow。

1. **优化方的 A／局部证明。** 非空时 out 与 bound 的实际 word 单元分离，store 保持 bound load；候选／源每步对应并保持公开 i、内存和外围 continuation。[CircularTransport](../prototype/interface/ClightCircularTransport.v) 和 [CircularSimulation](../prototype/interface/ClightCircularSimulation.v) 承担具体规则的这部分，不能称为任意循环自动化。
2. **入口 B 与编码。** B 是活动头部加当前 word 分离；这一例 B 接近 A，推导很短。它不替代多面体实例中“入口 B 覆盖所有迭代处义务”的全称覆盖问题。
3. **D／guard 的安全。** 先进行源头部本就要进行的 bound 读取；只有活动时才比较 out/bound。比较依据来自实际源首次 store 的有限前缀，[circular_domain_from_prefix](../prototype/interface/ClightCircularGuard.v)。不用整个源循环完成，也不执行 ghost 权限查询。生成器消费已认证原子，接受才取得单元分离。
4. **语言与宿主。** 私有 cache 写入位于已选择候选内部；direct guard 本身只读。[open_region_protocol](../theories/ClightOpenRegionContract.v) 保留完整 source fallback 的逐步执行。非空 alias 源和 guarded 目标均有真实 Clight 无限执行证明；小步进展只约束零步匹配，未加 source 无条件终止假设。语言库复用作用域、temp／memory 运输和全程序 simulation。
5. **输入绑定。** 实际 C frontend 的 body `Ssequence Sskip`、signed `1` 自增常量必须与 matcher 和执行模型一致。模型定理、完整程序 theorem、实际选中编译和 native 回归是不同证据，均不能省略。

这个例子检验语言宿主和有条件读取／稳定性机制，不是完整多面体 optimizer。真实 affine／tiling 迁移还须消费外部候选、依赖核对和本节没有自动解决的 `B⇒A`。

## 4. 最难的地方和怎样验收

| 难点 | 不能用什么替代 | 必须交付的证据与责任 |
| --- | --- | --- |
| 入口 B 覆盖全部局部 A | 枚举上限、扫描 fuel、逻辑 implication 字段、永远拒绝 | domain 算法的源实例覆盖；循环控制、机器值与数学域对应；非空接受域与保守拒绝。优化／domain 方证明，核复用后续编码 |
| guard 自身安全 | 假设 P 后证明检查无错误；用数学整数计算机器条件；先 preload 尚未定义的参数 | 语言原语的机器算术／指针定律；按源活动和已接受事实组织依赖读取；检查自身溢出、空路径、alias、权限边界反例。语言库＋实例 D 证据 |
| 候选模型与真实执行一致 | 只验调度矩阵、不验证实际 body／地址；把另一配置的能力算入当前 pass | 实际候选／依赖 validator 消费；源／候选 C AST 和执行对应；no-wrap、footprint、layout、公开游标出口。优化方，复用语言运输设施 |
| 保持有限／无限行为和公开上下文 | 仅 completed-run 等价；native 超时；把 cache 当不存在 | 正常出口／frame、私有 state 关系、局部小步匹配及宿主 forward simulation，明确内部 call／return／label 限制；最终 Csem→Asm 端点。规则 witness＋语言宿主 |
| 降低作者负担且有实际价值 | 增加 record／端点／相似模板；只量 Clight 打印字节 | 至少两条规则消费同一 condition／realization；记录专属 obligations 与证明代码；同源 direct/shared 对照和同版 CompCert 原生成本。核／adapter 复用、domain 接入、测量分别报告 |

第一行与第三行是主多面体使用者的核心难点；第二行是条件处理设施必须真正解决的难点；第四行是不可被抽象 if 隐去的语言实例工作。10 月 6 日的第一项迁移复用矩形范围与 named memory 的全实例对应，第二项 [参数化仿射内层源](clight-parametric-preservation.md) 复用已有端点覆盖、机器范围 lowering 和不同布局／偏移／多读取的 body 对应，并运行实际 schedule generation 后重新核对候选。二者都消费仿射／分块依赖核对器，通过公共保持、分派和安装接入。此次没有新增一般 B⇒A 推导算法，实际参数化 pointer footprint 随后经公共 private-scan 路线迁移；一般深度 affine 源与该 pointer package 的组合仍待扩展。都纳入 [当前计划](current-work-plan.md)，不以完成其中一行宣布全部目标完成。

随后新增的 [符号包络使用者](affine-box-condition-derivation.md) 明确分开三项新工作：domain 库证明系数符号推导覆盖任意有限维盒内的全部点，Clight 库证明 modular 仿射求值及最终 signed 比较范围，优化使用者证明接受建立所有行宽义务并接到旧局部证书。语言检查替换服务保留原 D／P／candidate，复用已有 reachable-test 安全、分派与安装证明。实际 compiler 替换宽度树，尚未替换 pointer scan。其困难观察边界是 `p+k` capability 不蕴含原始 p weak-valid，不能在没有源前缀证据时插入 base 比较；下一项 alias 条件推导必须同时取得这一观察许可和全实例足迹覆盖。

## 5. 研究主张与持续维护

[源观察支持的 alias 包络](source-observed-affine-separation.md) 进一步关闭了受限片段上的这两项证明：语言库从真实保留的 source load prefix 导出地址有效性，并安装 prefix 后的局部条件；domain 库将任意点包络接到实际 source footprint 与 modular 物理单元。readonly shortcut 复用同一 candidate C_opt、原 scan 和 kernel 组合。[新完整 compiler](clight-observed-pointer-compiler.md) 已实现 normalized AST 定位、三类实际 checker 的适配、提取和机器路径验收；原生矩阵由独立报告绑定。一般 affine pointer 源继续待扩展。这组服务的 proof audit 与前一阶段 compiler/native 报告分开，不从源码或端点数量主张性能或作者负担收益。

这次接入还暴露了 `C_host` 的具体责任：局部 `(loads;loop);suffix` contract 不能自动满足旧选择器只针对根部 loop 的 source progress。Clight 库新增 [序列 contract 运输](../prototype/interface/ClightSequenceContracts.v) 与 [序列 placement checker](../prototype/interface/ClightSequenceProgressSelector.v)，组合已有 framed 小步协议，保持正常后缀的真实 memory effect。domain 适配器核对源 AST、scope 和原候选证书后调用这些语言服务；kernel 不认识 loads、loops 或 pointers，也不增加 source progress 假设。最难义务中，安全许可和全部 footprint 覆盖已在受限模型关闭，宿主通过实际序列协议关闭；一般控制出口、一般多面体域和作者负担收益仍未由本例证明。

[共享 fallback 的实际接入](clight-shared-pointer-shortcut.md) 已按同一边界实现：语言库证明 direct tree 的真实正常执行运输到共享 AST，保持 trace／temps／memory；domain 将已有 matcher／三类 checker 的最后一步参数化，复用 D／P／candidate 与 coverage，核心组合定理未变。新的 compile_realized_observed_pointer_correct 对两个 lowering 值都给出 Csem→Asm 结论。79 端点审计及提取、两个完整十五配置矩阵和二十个机器路径探针全部通过；每种模式 5,640 次配置内调用，全本轮新编译，十五份 direct Clight 摘要保持冻结基线。见 [阶段记录](research-checkpoint-2026-10-06-shared-pointer.md)。一个真实二维配置的 scan AST 13→1，linked 函数 11,750→1,566 字节。这是有实际编译产物支持的语言服务复用和代码规模结果，没有扩大 condition／源域，也不是计时或总证明负担减少的证据。候选与对称 base 比较的冗余继续保留。

整体叙事是“小的语言无关 verified optimistic transformation 框架＋有实质算法与条件正确性证明的 CompCert 循环实例”。kernel 的组合定理较短，这不要求框架承担优化发现；贡献必须由实际可复用的证据处理服务、语言宿主和困难 optimizer 的接入共同证明。更广泛 conditional rewrite 作为接口实例；未实现的 vectorization、layout specialization 等不计 evaluated 能力。

每次 P1／P2／P3 验收记录三方新写了什么、复用了什么、哪张证书尚缺。和 OLO／CoreJIT／Chamois／Peek 做同例对照后再判断增量；未取得的文献／artifact 能力保留未知。[10 月 6 日一手补核](related-work-interface-check-2026-10-06.md) 已确认 Chamois oracle 的 CFG／invariant 输出和实际 CFG expansion 模拟，以及 Peek 的局部证明、normalization 与 liveness 宿主；这些已有服务不能单独算作 GuardCert 增量。性能、证明负担和新颖性各有独立证据，不能从正确性计数互相推导。

新的 [非矩形 source preparation](research-checkpoint-2026-10-06-affine-pointer-source.md) 进一步按这一责任划分实现：框架上层库的 `sequence_readonly_conditions` 负责有依赖条件的组合；语言服务 `readonly_completed_tree_condition` 利用真实表达式确定性，把有限完成路径证据包装为 reachable-test 安全、完成及接受 sound；domain 负责 normalized 源／操作／范围 checker、header 和第一轮 body 的参数证据、范围／宽度阶段以及源 Loop／公开出口对应。该阶段先连接同一 package／入口的算术条件与源对应，随后继续组装其他证书。D 明确要求有限正常源完成，不据此声称处理无限源或依赖加载参数。

[前一完整 source guard](research-checkpoint-2026-10-06-affine-pointer-alias.md) 关闭 prefix receipt 和该实例物理 non-alias。静态 column cap 的 affine 代入由 domain 数学库证明，实际比较继续使用语言的 modular 求值／signed 范围定理，框架上层库提供已有 sequencing。`affine_inner_pointer_source_guard_execution` 将接受、实际源 Loop 与精确公开出口绑定同一入口；`source_prefix_domain` 是有限入口 producer。该阶段当时未完成候选和安装，其历史报告不扩称全程序证据。

[后继完整接入](clight-affine-inner-pointer-compiler.md) 已把独立 `C_opt`、两套范围与实际 candidate/restore 绑定到同一 source package。guard 消费 上层库 readonly sequencing，局部分派和 source-prefix contract 消费已有语言服务，table 的程序 simulation 复用旧 host；具体新源形状由实际 progress fixture 核对。103 端点审计、提取、六个原生配置共 486 次调用和五个机器写入顺序探针通过。这里新增的是 domain 实例连接与不受信任候选整理，语言/核心的原定律未改；没有性能或 proof burden 收益结论。

后继 [分块接入](research-checkpoint-2026-10-06-affine-pointer-tiling.md) 关闭同一受限 pointer 源的 quotient witness／实际 candidate 对应：domain 用旧独立 tiling checker 产生与 mapped 相同的 `C_opt`，两条路径共用条件、lowering、restore 和 local contract，kernel／语言 host 未改。109 端点审计、提取、十一配置共 891 次调用及七个机器路径通过。tile 控制数从 caps 在编译时取得；不增加通用运行时 floor/ceil 语义，也不据此主张 proof burden 收益。

最难义务继续落实到下一项：多个依赖 preload 的读序与稳定性，以及一般深层 affine 源/出口。生成器的数学测试可能无法安全编码，故未证明的整理输出只能经完整 checker 再取得证书。框架不将候选整理视为自动条件推导；原 `C_derive` 和 `C_guard` 仍各自有实际证明。

[Loaded pointer 局部规则](research-checkpoint-2026-10-06-affine-loaded-pointer.md) 进一步检验这个顺序。语言从实际 retained preload 取得值观察，沿 loaded headers／rows 运输执行；domain 从第一次真实活动 body 取得 scalar 定义性，随后由接受范围和已验证写足迹排除 bound 单元。load 保持由实际 stores 推出，不写进 D。框架复用域限制与 `sequence_readonly_conditions`，将新的 preliminary 接到原候选条件；独立 package 和 actual lowering 仍由优化方提供。

该局部阶段的 `alp_observed_candidate_contract` 保持实际 prefix、公开出口与完整 memory，当时安装还缺 loaded nested source progress／matcher；31 端点 proof audit 不计为新 full compiler 或原生证据。三角实例以源已有 public n 缓存 p[0]；generic 运输允许任意观察 pointer，具体 exclusion rule 核对同一 write buffer 的静态逻辑单元。

[后继 placement](research-checkpoint-2026-10-06-loaded-placement.md) 将一个困难区分落实到实际协议：`C_host` 对原 loaded loop 的进展不依赖优化待检查的 bound 稳定性。语言的 strict nested 协议要求 body 每步保护 iterator，用机器最大值保证成功 increment 下降；syntax checker／sequence host 消费该协议。body 改变 bound 单元的 fixture 也通过进展检查。Domain 仍独立负责接受时的全部写足迹排除、源缓存运输和候选证书，kernel 未修改。

该阶段的固定 optimizer profile 已将原 mapped／tiling／schedule checker、实际 guard／restore／fallback、prefix/suffix 和 table host 组合到新的 Csem→Asm 定理。语言 progress 支持任意标识符，但优化 matcher 仍绑定 fixture 标识符；因此没有把一般 frontend 接受、提取或原生结果算作完成。下一验收必须实际推广 source adapter 并验证完整 C 的非空接受。多个依赖 preload、private snapshot 和一般 bound-pointer guard 继续待证；完整目标 active。


[最新 context-lifting 评审](topdown/context-lifting.md)的 [Clight 源码核对](clight-boundary-contract-review.md)进一步区分语言库定理与每次 placement 证据。`projected_region_contract` 和 `open_region_exit` 都复用 temp agreement 与 memory equivalence，但 completed-run host 还需要独立 source-progress 协议；open host 直接匹配每一步及到达的出口。不能将前者削弱为完成路径后声称支持任意 divergence，也不能因字段相似自由互换两类契约。当前全程序 live 集合保守包括全部源 temps，没有实现 context 最小 requirement 推断。

[参数化 loaded compiler](research-checkpoint-2026-10-06-affine-loaded-compiler.md)已经实际落实三方分工：语言从任意 prefix 位置生产值 receipt，复用不假设 bound 稳定性的 progress／table host；domain 通过 checked package 的真实 header/body 生产 preparation evidence，范围接受后才证明全部 writes 排除 bound，并运输到原候选证书；框架上层库用域限制和原 readonly sequencing 组合检查。源 snapshot、loaded fallback、quiet suffix、不同 normalized identifiers 与 candidate/restore 都进入真实 C 编译及机器验收。新 evidence 接口由 loaded 入口消费；旧 cached 入口仍用其原证明，不把两条实例的相似证明说成已经共享同一实现。

当前最难的下一义务是不同名 bound buffer 与写缓冲区之间的动态物理分离，随后是依赖读序／private cache 的 original-entry 事实与上下文运输。静态逻辑单元排除没有证明不同 base 的实际无 alias；仅 `bound != destination` 也不足。kernel 的抽象 `lift_refinement` 字段不解决这些问题。

[源顺序稳定性服务](research-checkpoint-2026-10-06-affine-loaded-stability.md)进一步分开这些责任：语言证明实际 store 的权限运输、已到达 loaded header 的整行执行取得和成功后续行；domain 从真实 row decode 取得每个 write receipt，生成不修改公开坐标的仿射地址表达式，并将其等号检查接到物理 byte separation／load 保持。当前行的全部检查已消费上层 `ReadonlyPrefixScan` 库；不同 memory blocks 的安全等号比较和 alias 后停止有真实 Clight proof fixtures。最小 kernel 未修改。

该阶段仍缺 checked source package 到逐行扫描实例的完整连接，以及候选／whole-program compiler 安装。`loaded_rows_prefix_spec` 的 `ROW_CHECK`、`DECODE` 和 `PRESERVE` 是有类型的使用者证明参数；`memory_affine_row_domain` 的参数／范围／receipt 字段要由实例交付，不能把接口字段算作已经解决。新的 row probe 定理和旧 compiler 回归各有审计边界；这次不新增原生能力、private snapshot 或 proof burden 收益主张。


[独立 bound pointer 的后继证明连接](research-checkpoint-2026-10-06-affine-dynamic-loaded.md)已关闭上述实例参数：checked package 的访问编码／范围／word、真实 row decode 和实际 store receipts 共同构造每次到达的 row 安全域；足够 fuel 覆盖全部活动点，完整 guard 接受后才得到 bound 保持。新 matcher 允许独立 bound pointer，原三类 candidate checker 与 language host 接到新的 Csem→Asm theorem。这里没有把这些领域证明交给 kernel。

下一困难位置是实际 guard lowering：嵌套 tree 在成功出口复制后续 scan，column cap=3 的实际 fixture 已显示 7／35／147 个测试随 outer fuel=1／2／3 增长。共享 fallback 不等于共享 scan continuation。需要保留顺序结构，并证明 private 状态、短路、安全和分派，再完成提取／真实 C 运行；当前只有 compiler proof，没有新增独立 pointer 原生能力。multiple dependent preload／private snapshot 的入口事实和上下文运输继续待证。

[顺序 plan 后继阶段](research-checkpoint-2026-10-06-affine-planned-loaded.md)已完成这一 lowering 和运行验收。语言库提供 plan/tree 精确运行对应、实际 private Boolean 代码、先写后读、原入口 branch 运输和公开 frame；资源反射 checker 把 freshness／structured branch 条件变成静态拒绝。domain 接入证明实际 affine plan 等于原完整条件，从而复用之前的检查安全、coverage、bound 保持、候选正确性。原 matcher、candidate checker 和语言 table host 接到新的 compiler theorem及实际提取入口，没有修改 minimal kernel，也没有重证 `C_opt`。

新正常 branch 运输仍有具体边界：E0／Out_normal，structured 分支，不接受 calls／labels／returns／switch；whole-program host 继续承担独立 progress，不从局部正常等价自动获得 contextual closure。六配置 222 调用、十三个机器路径验证实际安装、接受、拒绝和 bound 改写后的出口；默认 64×64 cap 亦已运行。当前最难的下一义务是缺失 public snapshot 时的 private 读取安全、original-entry 事实和私有状态运输，以及多个依赖读取。按 cap 展开的 guard 仍有代码成本，性能、一般深层域和同例 proof burden 尚未完成。

[private snapshot 后继](research-checkpoint-2026-10-06-affine-private-loaded.md)落实了单个 direct header 读取：语言 `private_source_preparation_contract` 把原执行运输到实际入口，安全构造 prepared execution，消费扩展 scope 的契约后投影回原 public scope；私有初值无需一致。`loaded_header_snapshot_read` 从实际首次 header 提供 nonvolatile Mint32 许可，零次 body 也有这个 header，不预置未来稳定性。源 selector 提供 flattening／frameability，freshness 静态核对；domain adapter 仅委托整个原 planned-loaded factory，原 `C_derive`、`C_guard`、`C_opt` 保持。host 的 progress 与 rewrite key 都作用于真正原 source，prepared source 只是内部证明和验证接口。

两个无 bound 快照的实际 C 域通过提取、444 次新入口调用、74 次旧入口对照和 28 个机器探针（含两个旧入口对照）；公开 marker=123 保持，读取 bound 的 fresh temp 没有泄露进 public scope。五个新 `.v` 与 140 端点审计通过，无新增公理，完整 compiler 沿原 42 项基线。该结果不代表任意 preload 安全：仍要求 body-pointer receipts；下一困难是多个依赖读取和 Mint64／Mint32 等不同 chunk 的 byte footprint 保持。现有 preparation 桥不自动提供这些 domain 证据；默认展开 guard 的代码成本和 P4 仍未解决，kernel 截止保持。

[依赖 header 服务](research-checkpoint-2026-10-06-dependent-header.md)继续沿此边界：语言证明实际双读取／captures／public preparation、可运行 byte-separation 条件、全部观察保持后的 prefix 和缓存执行运输；domain 将该条件接到已存在的 affine 地址编码、reached-write receipts 与真正 physical write sequence。当前已证明一个 point 接受后保持 pointer cell 和 bound cell 的实际 load；完整 checked-package row／outer scan 的 decode、范围和覆盖仍是未接入的实例义务。源 progress 独立证明，只用实际成功的 signed header 与保护 iterator 的 body；允许 memory observation 改变不等于已证明缓存优化合法。

51 个新增审计端点均在原 CompCert 基线内，kernel 与原 candidate checker 未修改。泛型缓存运输所要求的 body decode／观察保持，以及 host 的 typed private pool、placement／source key 和 program installation 不能由局部接口自动取得。尚无新 dependent compiler／extraction／native 端点；现有 body 仍是 Mint32 operations，progress selector 接受 pointer store 不增加 optimizer 的 body 表达力。

[完整局部实例链](research-checkpoint-2026-10-06-dependent-joint.md)已填入上述 checked-package 参数：domain 提供真正 reached-row decode、全部 write receipts、坐标范围和内外 caps 的 coverage；语言库运输权限、双观察 header／root temp frame 和实际缓存执行；上层条件库组合 preparation、joint scan 与 candidate guard。首次实际 header/body 的类型证据也已接到同一 preparation evidence；现有 candidate certificate 证明实际候选执行，局部接受／拒绝保持 memory 和 live temps。七模块／29 端点审计通过，没有把这些实例证据归为 kernel 自动提供。

未完成责任集中在实际接入：source selector／factory、safe captures 后入口 producer、不同类型的 private pool、progress／scope／placement 和 whole-program host；这些不由“局部 correctness”自动推出。本轮没有 new factory／compiler／extraction／native 结果，原 private-loaded 42 项完整 compiler 基线的回归与新六项局部端点分别记录。

[实际 dependent compiler 后继](research-checkpoint-2026-10-06-dependent-compiler.md)已关闭这组接入责任：语言 preparation 桥以实际原 header 许可有序 captures，入口 adapter 生产 typed pointer／bound／body receipts，并将扩展 scope 契约收回原公开 scope；domain 将 exact original AST、checked cached model、完整双观察 condition 的顺序 plan 和原三类 candidate checker 绑定。语言 host 分配 typed fresh pool，实际消费原源进展、位置／scope 和整程序 simulation。新 Csem→Asm 定理、40 端点审计、提取及两种实际 C 域 444 调用／28 store-order 探针通过，无新增公理；没有把 language host 的安装计作 kernel 自动提供。

难点现在转到实际 guard 成本与更一般的源：默认 caps 的函数约有 20,700 个 if，尚未循环化或给出性能收益；body 仍只消费 Mint32 operations 和源已有 pointer receipts。合法 pointer-store body、一般深层 affine 域、不同 body base 的 alias 接受及同例 proof burden 保持未完成。每个后继任务仍需注明新语言定律、domain 专属证据和真正复用的上层库，不能因局部证书已组合就省略实际源码／context 的义务。narrative `7d94d81` 的 kernel 截止有效，本阶段没有修改它。

[短路 cursor scan](research-checkpoint-2026-10-06-cursor-scan.md)进一步将这一成本工作拆成可复用的实际服务：Clight 库证明 cursor specialization 的表达式／lvalue／decision 运输，实际初始化、拒绝即退出和 signed increment，以及 check-plan body 的 private/public frame；domain 证明符号列地址和两种 chunk 探针对应原常量列 probe，完整 row spec 等于原已认证条件。实际 reached-row domain 给出可用检查，再取得真实有限执行和 primitive safety；实际接受通过 quiet determinacy 接到旧 row observation-preservation theorem。kernel 没有新增责任。

七模块／34 端点审计通过，每个新增端点最多六项原 CompCert 假设；旧 compiler 回归保持 42 项。row 域、freshness 和 public read scope 在此服务接口中仍是调用者证据，outer-prefix 推进和全 rows 覆盖尚未接实际循环；不能把这些有类型的义务或旧 compiler/native 回归说成新 factory 已完成。后继须由 checked package／typed pool／语言 host 实际生产并消费这些证据，再提取和验收成本。narrative 最新澄清与本地正文已再次核对一致，没有因此重排文件或修改最小 kernel。

[完整 cursor compiler](research-checkpoint-2026-10-06-cursor-dependent-compiler.md)已关闭该具体 package 的这些调用义务。Clight 库提供双 cursor 执行、private/public frame 和前置／扫描／后置的实际短路分派；domain 将其精确绑定原完整条件和已有 source-prefix coverage。有限资源 checker 从实际模板证明输入不与 cursors 冲突，factory／语言 pool 生产并消费证据；原 preparation、候选证书、source progress 与 whole-program host 保持。guard cursors 与候选 counters 分开，需要 21 个 typed private slots；这属于真实状态运输义务，不是新 kernel 能力或最小资源证明。

43 新端点、提取、两个 C 域共 444 调用、28 store-order 与 18 guard comparison 探针通过。后者在实际机器指令上核对源点顺序和拒绝后停止。默认 caps 的展开代码增长已在这两个 compiler 使用者中关闭，Clight／linked 函数大小分别报告；没有性能、一般多面体覆盖或作者负担收益结论。当前仍是 silent normal region、实际 body-pointer receipts 和 Mint32 operations 的具体 host/domain 范围。kernel 截止、语言安装与 optimizer/site evidence 的边界继续按 narrative `7d94d81` 明确保留。


[Deep affine 的当前接口接入](research-checkpoint-2026-10-06-materialized-affine.md)进一步检验这条边界：已有 guard 正常返回并在 private temp 中写/read Boolean，不能直接作为 result-fresh／break-refusal scan。新的 Clight library 提供实际执行、primitive safety、defined dispatch、全部完成执行 sound 和原入口／checked-entry 运输；domain 提供原源 quiet／writes、实际 guard execution、足迹／范围及 conditional candidate-local。两类实际 factory 消费同一语言服务，kernel 使用 `guardify_preservation`，原 table host 另证程序安装。六个新模块／26 端点、提取、5,118 次 assembly 调用和四组独立 Clight 插桩通过；没有把旧递归 IR、旧 source/candidate checker 或库参数算作新功能。

本实例的 source domain 仍是有限正常完成；actual select 的有限执行分解不要求所选分支完成，但该 host 不因此获得任意 divergence 定理。Stable-temp 深层域与两层 loaded/dependent 源尚未组合；新 alias scan 复用旧多指针能力，typed pointer stores／general source domains、P4 和同例责任／负担比较仍待交付。共享 proof 对象重编后的旧 cursor 精确摘要验证失败另记，当前 proof regression 不改写旧 frozen/native 报告。

[Expression-header 服务](expression-header-services.md)的最新切口延续 narrative `226ba94`：
语言库提供真实 signed header 求值、safe private capture、actual body receipt、generic source
prefix 与接受后的缓存源运输；raw memory observation 和 computed cache 不再合成一个值。
Affine client 核对原 AST／类型／private scope，复用旧递归 numeric checker，证明第一阶段
检查可用与接受后的 cached-word math domain。最小 kernel 与 candidate validator 保持。

剩余 domain 责任是由 actual body receipts 解码写 trace、给出每一轮观察覆盖／许可，并证明
实际 readonly body check 接受 ⇒ 观察保持；library 的 HEADER／PRESERVE／coverage 参数不
自动完成这些证明。语言 host 仍须生产 typed allocation、entry transport、source progress、
scope／placement 与全程序安装。43 端点审计、新空域／回绕检查及具体 alias 源执行只验证
上述服务和第一 numeric client；没有新完整 guarded rule／factory／compiler/native 能力。


[Loaded＋offset 后继](loaded-offset-affine.md)已用 actual body receipt 填入上述 prefix 服务：
raw load 与 computed upper 不再要求相等；body 检查由真实到达权限许可，接受后保持原观察，
再导出 cached-source 执行。新 domain producer 提供 guard soundness、candidate P 和 entry
transport，signed-expression 语言 host 提供安装。generic kernel、旧候选 validator／backend
均保持；新 Csem→Asm 与提取运行有独立验收。主使用者当前只自动提出 loaded-plus-constant
根，不能把一般 signed-expression 库的证明参数算作已经自动支持的语法。


[第二 loaded header 的新服务](nested-header-services.md)继续遵守上述分工：语言从原 outer
和 child headers 提供 conditional captures、actual child receipts、temp 运输和 indexed read
定律；prefix 库携带全 observation list，单 row 的 preservation 成立才推进 outer。语言再导出
双 cached-source execution，structured stores 的权限运输复用现有定律，优化方不用额外交任意
memory-effect 回调。Affine 库从 captured words 许可旧 numeric probe，不借完整缓存源执行。

48 端点审计和原 compiler／native 绑定保持，kernel 不变。joint physical scan 的许可／覆盖／
接受⇒preservation、原 nested syntax 到 canonical model 的 projected transport，以及新 factory
和语言安装仍需实际接入。点比较和相邻 word 的真实 Clight 接受证明不算新完整 optimizer；
整程序责任没有搬入 kernel。先闭合这些连接，再按 narrative `226ba94` 验收 compact 条件和
实际 guard 工作／接受域／计时，最终仍需自动化与作者负担证据。
