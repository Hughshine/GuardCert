# 验证责任、证书边界与最难的验收

这是当前活动目标的一部分，按用户 2026-10-05 的补充要求维护。研究叙事沿用 `topdown/research-positioning` 的 [paper narrative](topdown/paper-narrative.md)，读取提交为 `4521f76ab11c2df1332ce06a5cf4b83a613be27b`。该稿是方向；本文区分已经实现的设施、使用者还需提交的证明和后续验收。完整多面体目标仍未完成。

## 1. 三方各自证明什么

“框架提供 conditional correctness 接口”不表示框架替优化作者证明任意候选正确。“语言提供语义”也不表示每个优化作者都要重新证明语言的 if、load 和上下文定律。

| 责任 | 需要提供／证明 | 可以复用的交付 | 不由这一方自动解决 |
| --- | --- | --- | --- |
| 语言无关框架 | 证书消费、条件组合／短路／安全后处理、条件 rewrite 的语义定理、在宿主定律下提升以及有限次组合 | 参数化生成／简化算法的正确性；readonly 前台；不同规则共享的安装定理 | 哪个优化成立、任意语义命题的检查代码、具体语言的 guard 或上下文定律 |
| 语言／IR 实例 | 实际执行与观察；原子测试的机器语义和定义性；具体分派；私有资源与状态运输；effect／frame；合法位置／出口／小步匹配；后端连接 | 一次证明并供多条规则调用的原语、direct/shared 实现和 host；例如真实 `Mem.load/store`、temp agreement 与 CompCert simulation | 某个程序的足迹完整性、某候选的依赖保持、某处入口为什么具备所需事实 |
| 优化实现者，含 domain library | 寻找片段、提出实际候选／模型义务 A；候选条件正确性；入口条件 B 对 A 的覆盖；实例专属源／模型／候选对应和作用域证据 | 经验证的 candidate checker、受限投影／范围／足迹算法及证书；这些可以在一个领域内再复用 | 未证明的 oracle 答案不会因接入框架而获得正确性；没有一般 `extract_assumptions(S,T)` |

框架的组合证明以已经证明的语言定律为参数。优化实现者既可以直接提交证明，也可以提交不受信任候选、条件和 witness，由已验证 checker 产生证书。候选生产器和搜索启发式无需可信；成功输出仍必须绑定**实际** source、candidate、condition 和安装位置。语言、domain、核心的证明可以由同一开发者写，但接口和成本归属保持分开。

语言库可以提供“实际字节足迹分离 ⇒ load 穿过 store 保持”的定理；规则作者证明本次 body 的访问属于这些足迹，并满足权限／chunk 条件。核消费这个证据，不了解指针，也不允许只把 `p!=q` 当成任意字节区间分离。

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
| `C_derive` | 优化／domain library | [readonly_condition_entails](../prototype/interface/GuardedRewrite.v) 消费推导证明；它本身不是已实现的通用投影算法 |
| `C_guard` | 核心参数化算法＋语言原语＋实例域证据 | [只读 tree 合成](../prototype/interface/ClightReadonlyTreeSynthesis.v)、[loaded tree](../prototype/interface/ClightReadonlyLoadedTreeSynthesis.v)、[依赖 prefix scan](../prototype/interface/ReadonlyPrefixScan.v)；实例仍证明 coverage、原语安全和 source 支持 |
| `C_host` | 语言实例／宿主库，规则提交边界 witness | [select_exact](../prototype/interface/GuardInterface.v) 是抽象定律；[共用实际 realization](clight-guard-realization.md)、[direct](../prototype/interface/ClightReadonlyProjectedCompiler.v)、[shared](../prototype/interface/ClightSharedProjectedCompiler.v) 和 [open host](../theories/ClightOpenRegionProof.v) 是具体证明；完整 Csem→Asm 结论是 backward simulation |

这些是逻辑责任，不强迫每个使用者填四个重复的 record。可以将证书封装在一个已验证库中；验收仍逐项回答它们来自哪里。不能把 normal-completion 的 big-step 观察接口说成已经观察了全部无限行为，也不能把实际 forward 小步安装证明改称任意目标执行的双向等价。

证书的方向也要和宿主一致。核已经分别提供 refinement 与 preservation；当前 `readonly_projected_clight_rule` 要求双向局部等价，但 private-region 安装实际上消费的是源执行到候选执行的一边。旧 [encoded_private_rule](../theories/ClightPrivateRule.v) 及 [named candidate compiler](../adapters/compcert-memory/GuardMemoryNamedCompiler.v) 主要交付条件性 source-to-candidate 保持，并且局部端点量化实际 program 的 globalenv。P2 需要核对并接入这种证书，不假定旧 checker 已交付任意 globalenv 上的双向等价，也不将其单向结果改名为等价。统一 realization 复用分派／运输，不消除这一 optimizer 与语言边界的真实义务。

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

第一行与第三行是主多面体使用者的核心难点；第二行是条件处理设施必须真正解决的难点；第四行是不可被抽象 if 隐去的语言实例工作。都纳入 [当前计划](current-work-plan.md)，不以完成其中一行宣布全部目标完成。

## 5. 研究主张与持续维护

整体叙事是“小的语言无关 verified optimistic transformation 框架＋有实质算法与条件正确性证明的 CompCert 循环实例”。kernel 的组合定理较短，这不要求框架承担优化发现；贡献必须由实际可复用的证据处理服务、语言宿主和困难 optimizer 的接入共同证明。更广泛 conditional rewrite 作为接口实例；未实现的 vectorization、layout specialization 等不计 evaluated 能力。

每次 P1／P2／P3 验收记录三方新写了什么、复用了什么、哪张证书尚缺。和 OLO／CoreJIT／Chamois／Peek 做同例对照后再判断增量；未取得的文献／artifact 能力保留未知。性能、证明负担和新颖性各有独立证据，不能从正确性计数互相推导。
