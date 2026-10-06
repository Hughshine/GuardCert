# 验证责任、证书边界与最难的验收

这是当前活动目标的一部分，按用户的补充要求维护。研究叙事沿用 `topdown/research-positioning` 的 [paper narrative](topdown/paper-narrative.md)，10 月 6 日更新到 `f7936299fa6272fbf50db6b94a1bd0333808ea09`。该稿是方向；本文区分已经实现的设施、使用者还需提交的证明和后续验收。完整多面体目标仍未完成。

## 1. 三方各自证明什么

“框架提供 conditional correctness 接口”不表示框架替优化作者证明任意候选正确。“语言提供语义”也不表示每个优化作者都要重新证明语言的 if、load 和上下文定律。

| 责任 | 需要提供／证明 | 可以复用的交付 | 不由这一方自动解决 |
| --- | --- | --- | --- |
| 语言无关框架 | 证书消费、条件组合／短路／安全后处理、条件 rewrite 的语义定理、在宿主定律下提升以及有限次组合 | 参数化生成／简化算法的正确性；readonly 前台；不同规则共享的安装定理 | 哪个优化成立、任意语义命题的检查代码、具体语言的 guard 或上下文定律 |
| 语言／IR 实例 | 实际执行与观察；原子测试的机器语义和定义性；具体分派；私有资源与状态运输；effect／frame；合法位置／出口／小步匹配；后端连接 | 一次证明并供多条规则调用的原语、direct/shared 实现和 host；例如真实 `Mem.load/store`、temp agreement 与 CompCert simulation | 某个程序的足迹完整性、某候选的依赖保持、某处入口为什么具备所需事实 |
| 优化实现者，含 domain library | 寻找片段、提出实际候选／模型义务 A；候选条件正确性；入口条件 B 对 A 的覆盖；实例专属源／模型／候选对应和作用域证据 | 经验证的 candidate checker、受限投影／范围／足迹算法及证书；这些可以在一个领域内再复用 | 未证明的 oracle 答案不会因接入框架而获得正确性；没有一般 `extract_assumptions(S,T)` |

框架的组合证明以已经证明的语言定律为参数。优化实现者既可以直接提交证明，也可以提交不受信任候选、条件和 witness，由已验证 checker 产生证书。候选生产器和搜索启发式无需可信；成功输出仍必须绑定**实际** source、candidate、condition 和安装位置。语言、domain、核心的证明可以由同一开发者写，但接口和成本归属保持分开。

语言库可以提供“实际字节足迹分离 ⇒ load 穿过 store 保持”的定理；规则作者证明本次 body 的访问属于这些足迹，并满足权限／chunk 条件。核消费这个证据，不了解指针，也不允许只把 `p!=q` 当成任意字节区间分离。

最新 topdown 补充也已采纳：抽象接口应能由 SSA／CFG 或汇编实例解释，Clight 继续是主验收。CFG 实例另证明 live-out／phi／控制出口；汇编实例另证明 scratch registers、flags、memory 和分支控制。若实际检查改变 flags，语言不能只说逻辑 condition 是只读：必须证明这些变化私有且不影响分支，或给出保存／恢复与真实状态运输。第二 IR 是可选的表达力证据，当前没有宣称已经实现，不把它加入主功能的强制验收。

Clight 的 readonly tree／单 Boolean realization 与循环式私有 footprint 扫描有不同的检查状态。扫描后的游标可能依赖 memory 和拒绝位置；语言无关 host 已允许实际 checked state 和入口关系。10 月 6 日的 [公共 private-scan compiler](clight-private-check-migration.md) 已完成这条实例化，不将它描述成任意 stateful 检查的通用合成器。

本阶段分工可以在源码中核对：[Safety](../prototype/interface/ClightPrivateScanSafety.v) 和 [Host](../prototype/interface/ClightPrivateScanHost.v) 由语言解释实际求值、有限循环续行、结果解码与任意完成分支的 exact dispatch；[Preservation](../prototype/interface/ClightPrivateScanPreservation.v) 提供公开观察、分支 temp 运输，并调用既有 kernel 的 `guardify_preservation` 和小步安装。domain 的 [Certificate](../prototype/interface/ClightParamPointerCertificate.v) 提供实际 source-derived D 下的扫描安全、protected frame 和 `accepts⇒P(original)`；候选对应和依赖核对继续由优化方的旧数学证书承担。source／candidate 的实际表和 private pool 接到了 Csem→Asm，并完成提取和原生验证。

`check_safe` 使用覆盖已到达 `eval_expr`、if 测试和有限 loop 续行的归纳判断；它不是完成见证的改名。实际 bounded scan 的既有执行与确定性可构造该判断，再由语言定理推出可用性。保护集同时覆盖公开入口与前提所依赖的 header、参数和 pointer binding，语言无需知道这些维度的具体意义。局部保持接口观察完成的 silent normal region，完整程序结论是 backward simulation；没有新增任意无限 pointer fallback 宿主。38 个端点和实际运行的证据见 [阶段记录](research-checkpoint-2026-10-06-private-scan-compiler.md)。

## 2. 四张证书与一个安全域

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
                   C_host: 实际分派、状态运输与上下文安装
                         │
                   guarded program ──► CompCert 后端
```

D 不能预先包含待检查的 no-alias／稳定性事实。它说明当前哪些观察可安全取得；后续观察可以依赖已完成检查的正结果。false／unknown 只触发回退，不承诺 B 的否定。语义充分条件可以保守加强，因而 `C_derive` 不要求最弱条件或逻辑等价。

| 证书 | 主要生产者 | 当前可核对的接口／证据 |
| --- | --- | --- |
| `C_opt` | 规则／优化实现者或已验证候选 checker | [conditional_equivalence](../prototype/interface/GuardedRewrite.v)、局部状态还原；完整循环也可使用 [open_region_protocol](../theories/ClightOpenRegionContract.v)，须提交实际执行的匹配 |
| `C_derive` | 优化／domain library | [readonly_condition_entails](../prototype/interface/GuardedRewrite.v) 消费推导证明；[盒状 affine 包络](affine-box-condition-derivation.md) 提供受限符号算法及实际宽度使用者，不是通用投影算法 |
| `C_guard` | 核心参数化算法＋语言原语＋实例域证据 | [只读 tree 合成](../prototype/interface/ClightReadonlyTreeSynthesis.v)、[loaded tree](../prototype/interface/ClightReadonlyLoadedTreeSynthesis.v)、[依赖 prefix scan](../prototype/interface/ReadonlyPrefixScan.v)、[实际 private-scan host](../prototype/interface/ClightPrivateScanHost.v)；实例仍证明 coverage、原语安全和 source 支持 |
| `C_host` | 语言实例／宿主库，规则提交边界 witness | [select_exact](../prototype/interface/GuardInterface.v) 是抽象定律；[共用实际 realization](clight-guard-realization.md)、[direct](../prototype/interface/ClightReadonlyProjectedCompiler.v)、[shared](../prototype/interface/ClightSharedProjectedCompiler.v) 和 [open host](../theories/ClightOpenRegionProof.v) 是具体证明；完整 Csem→Asm 结论是 backward simulation |

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

后续共享 fallback 也按同一边界验收：语言库证明真实 lowering 的分派／frame，domain 复用原 D／P／candidate 与 coverage，核心组合定理保持。当前一个二维 fixture 有 13 份 scan AST 和两个对称 base 比较；减少这些冗余需要新的 proved lowering／语义保持证据，然后才能量最终机器成本。代码规模问题不能由声明“共享实现”或只比较逻辑 condition 消除。

整体叙事是“小的语言无关 verified optimistic transformation 框架＋有实质算法与条件正确性证明的 CompCert 循环实例”。kernel 的组合定理较短，这不要求框架承担优化发现；贡献必须由实际可复用的证据处理服务、语言宿主和困难 optimizer 的接入共同证明。更广泛 conditional rewrite 作为接口实例；未实现的 vectorization、layout specialization 等不计 evaluated 能力。

每次 P1／P2／P3 验收记录三方新写了什么、复用了什么、哪张证书尚缺。和 OLO／CoreJIT／Chamois／Peek 做同例对照后再判断增量；未取得的文献／artifact 能力保留未知。[10 月 6 日一手补核](related-work-interface-check-2026-10-06.md) 已确认 Chamois oracle 的 CFG／invariant 输出和实际 CFG expansion 模拟，以及 Peek 的局部证明、normalization 与 liveness 宿主；这些已有服务不能单独算作 GuardCert 增量。性能、证明负担和新颖性各有独立证据，不能从正确性计数互相推导。
