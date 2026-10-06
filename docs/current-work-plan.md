# 当前工作计划：评审吸收后的验收顺序

2026-10-06 更新。主目标仍是顺序 CompCert 中可运行的 verified guarded polyhedral transformation，PolCert 是功能与证明能力参照；片段选择和候选由用户提供，框架核心组合条件证据和局部 reasoning，语言 host 负责完整程序安装。完整目标没有因阶段结果而完成。

最新可运行交付是 [private bound snapshot](research-checkpoint-2026-10-06-affine-private-loaded.md)：原源没有公开 bound 快照时，安全私有读取、original-entry／public frame、真实 source-key 安装、提取和两类 affine 域运行已通过。后继 [依赖 header 证明阶段](research-checkpoint-2026-10-06-dependent-header.md)已落实双读取、字节分离、逐点保持及语言运输／progress；完整 checked-package scan 与编译接入尚未完成。以下阶段保留各自历史范围，当前未完成项以文末依赖 header 后继验收为准。

本计划吸收 [三个分支的评审](review-synthesis-2026-10-05.md)。既有研究路线保留在 [contribution-plan.md](contribution-plan.md)，当前执行优先级以下表为准。

活动目标补充（用户 2026-10-06）：持续按 `topdown/research-positioning` 的 [paper narrative](topdown/paper-narrative.md) 改进整体定位；以“小的语言无关框架＋实质 CompCert 循环实例”组织研究，明确框架、语言实例、优化／domain 实现者的验证责任。具体约束与最难验收见 [责任矩阵](framework-responsibilities.md)。这项补充与原完整实现目标同时有效，每个阶段检查，不将方向文档算作功能完成。

10 月 6 日阶段同步吸收 `f793629` 的 cross-IR 补充：保持核心不依赖 Clight 语法；SSA／汇编使用者须实例化自己的控制、live-out／phi、scratch／flags 定律。它们是接口讨论和同例 related-work 比较的方向，第二 IR 实现是可选证据，当前主实现／验收继续是 CompCert/Clight。

最新同步到 `8c098ed` 的 [context lifting](topdown/context-lifting.md)：kernel 的局部正确性与语言的程序安装分开陈述；host 提供可复用 region/boundary 契约，优化与具体位置提供 guarantee／placement 证据。已完成 [源码核对](clight-boundary-contract-review.md)，已有 temp/memory／scope／private 运输继续复用；finite 与 open 的 progress 是实质差异，不按自由 clause 组合重新设计 kernel。guarantee/requirement API 仍待实际受阻案例支持，不称已经实现。

最新 `7d94d81` 的 kernel 截止澄清已同步：只读前台、条件组合、prefix scan、simplification 和 assumption derivation 属于上层库；语言 host 承担完整程序安装。沿此边界继续实现和记录责任，不做无实例依据的文件重排或新 kernel 接口。

| 顺序 | 工作与状态 | 必须交付的验收 |
| --- | --- | --- |
| P0：本次交付 | 实现、实际 frontend 对应、提取与回归已通过；提交／push 以阶段记录为准 | 一个真正完整的 unsigned memory-bound 循环；guard 域来自有限源前缀；源／目标实际 alias 发散；540 次有限调用、六处新 loop 与两处混合旧 preload；401 端点／862 摘要、25 配置／40 报告绑定当前产物，39 份旧 C／Clight 摘要保持；准确文档并 push |
| P1：统一实际 realization | [公共设施](clight-guard-realization.md)与三个实际路径已接入；411 端点／863 摘要、25 配置／40 报告验证通过，相对 `26956a4` 的 40 份 C／Clight 摘要保持 | direct/shared 复用同一个 readonly condition 与 local rule，公共证书说明实际代码、私有资源／freshness、状态／观察运输、defined dispatch 和相应宿主模拟；两个 finite 安装路径和完整 unsigned 循环消费同一设施。分派前缀不要求分支完成；shared whole-loop 尚未安装，finite host 仍要求 source progress |
| P2：主多面体路线迁移 | [named rectangle 使用者](clight-polyhedral-preservation.md) 的证明、提取、40＋8 原生配置已通过；第二项 [参数化 affine 内层源／多类数组 body](clight-parametric-preservation.md) 通过 12 个证明端点、六份完整 C fixture／134 个原生配置，以及四个实际接受／回退顺序探针；主接口 415 端点／864 摘要保持；第三项实际参数化 pointer scan 已接入一般公共证书、kernel 保持、Csem→Asm 和提取，38 端点／15 个原生配置／四个执行顺序探针通过，另有 222 组完整上下文输入／三配置通过 | 不受信任的实际候选、源／候选对应、机器范围／alias 检查、private 观察、Csem→Asm 与提取接受／拒绝均通过公共接口；记录旧证书复用和专属义务。此次第二项仍不包含一般深度 affine polyhedron、指针切片或 stateful 足迹；单个新 helper 或脱离编译器的模型不计完成 |
| P3：一个符号化条件／足迹算法 | [盒状 affine 包络](affine-box-condition-derivation.md) 与实际宽度使用者通过 29 端点、完整证明／提取、134 配置和十个顺序探针，[证据](research-checkpoint-2026-10-06-envelope.md)。后继 [源观察 alias 编译入口](clight-observed-pointer-compiler.md) 已接实际 source matcher、三类候选、序列 placement、Csem→Asm 与提取；67 端点审计、十五原生配置各 376 调用和十个机器路径探针全部通过，[本阶段](research-checkpoint-2026-10-06-observed-compiler.md)保留分块首轮超时及八份绑定产物重执行的事实 | 固定受限 affine 表达／域和允许观察；输出条件和可核对证书；证明实际源实例覆盖、Boolean／机器表示、安全与接受蕴含语义前提；实际编译一个候选，给出拒绝策略和非空接受域。不把逻辑 projection 定理描述成已有 QE 实现 |
| P4：机制性能与复用量化 | [测量方案](native-performance-plan.md)和[schema](native-performance-report.schema.json)已采纳，尚未测量 | 同版原 CompCert 对照，实际接受／回退／静态拒绝分开；tree/simplified 的同源对照；最终 kernel bytes、guard／完整运行成本、编译成本、原始批次和环境。测量期间没有并发证明／构建；负收益照实报告 |
| 持续：已有工作／主张校准 | 保留 [cf4d442 证据矩阵](evidence-to-claim-2026-10-05.md)；新增 [Chamois／Peek 一手接口补核](related-work-interface-check-2026-10-06.md)，阶段性读取新评审 | Chamois oracle 签名和 CFG 扩展证明已取得，不再保留这两个访问未知项；动态条件推导能力和同例作者负担仍需核对。比较 OLO、Chamois、Peek 的安全、覆盖、freshness 和宿主义务；不以端点数、C 层或 abstract if 单独主张 novelty |
| 持续：论文方向与验证责任 | 目标的组成部分，沿 topdown narrative 更新 | 每个阶段区分框架证明、语言定律和 optimizer／domain 证书；分别落实 `C_opt`、`C_derive`、`C_guard`、`C_host`。重点验收 B 覆盖全部 A、guard 自身安全、实际模型对应、有限／无限宿主行为及证明复用，不以责任表代替这些证明 |

P0 关闭的是一个明确语义缺口。P1 服务于 P2 的真正接入；P2 是主功能目标的一次迁移验收，之后仍需一般 affine 域、复杂读写 body、依赖 preload 和布局组合。P3 是 optimizer/domain library 的受限推导算法，核心不承担 universal assumption extraction。P2 的首个使用者已实际消费候选／依赖核对和条件正确性；新的保持接口沿用旧证书在实际 globalenv 上的方向，与双向规则共享安装证明，没有改称等价或只重做 guard 包装。后续优先迁移参数化源／访问及真实 pointer footprint；区分可直接复用的 readonly 证书和需要私有检查状态的路线。P3 必须说明 `B⇒A` 的入口推导，再交给 `guard accepts⇒B` 的编码与 host。P3 与 P4 用来检验算法和实际价值，不将测量结果预设为收益。新增 [paper narrative](topdown/paper-narrative.md) 已在 P0 后同步读取并吸收。

P2 第二项已经复用 `encoded_private_rule`，接入参数化 readonly 使用者、实际 schedule generation／rechecking 与不同数组 body。第三项 [private-scan compiler](clight-private-check-migration.md) 将真实参数化 pointer footprint 接入一般公共 host 和 guard／preservation 证书：覆盖归纳检查安全、实际检查后状态、result 初始化、原入口 P、全部完成检查 sound、任意完成分支的 exact dispatch、分支运输及 kernel 消费。scope、private pool、source progress 和完整 CompCert 安装均沿用已证明的语言设施。38 端点、465 项实际依赖、812 份摘要；15 个原生配置各覆盖同一组 637 次调用，另有四个实际 disjoint 接受／alias 回退的汇编顺序探针。完整研究目标仍未完成。

参数化 readonly 结果见 [阶段记录](research-checkpoint-2026-10-06-parametric.md)，private-scan 的前一事实阶段见 [历史记录](research-checkpoint-2026-10-06-private-scan.md)，公共 pointer compiler 的证据见 [新阶段记录](research-checkpoint-2026-10-06-private-scan-compiler.md)。当前 pointer 源是稳定寄存器矩形 bounds 下的参数化仿射访问，不与 `j<U(i,parameters)` 非矩形源混称；source-derived D、footprint coverage 与范围理论仍复用既有 domain 证明，没有新增一般 projection 算法。

P3 已实现受限 affine 范围／足迹的符号化条件推导，明确允许观察和保守拒绝策略，输出可核对条件证书，并让实际候选消费。其范围仍是盒状源／受限 pointer package；一般 projection 不在已实现能力中。P4 仍需同版原 CompCert 对照、实际 guard／运行成本，以及与已有接口的同例证明负担比较。一般深度 affine pointer 域和多个依赖 preload 继续作为功能差距维护。

P3 的 pointer 快捷检查计划已据实际语义修正：`p+k` 是合法源访问，不蕴含原始 `p` 是 weak-valid pointer。CompCert 对指针比较的定义性要求因此不能仅由当前访问足迹推出；“先比较 base，再按 offset 包络判分离”不能直接插入普通循环。只有源前缀或合法 placement 证书提供比较所需的实际地址有效性时才可接入，不将它偷偷加进 source-derived D。首次实现切口是通用盒状 affine 包络及有符号参数范围编码，替换参数化 readonly 源的宽度检查，让真实候选消费所有迭代点的覆盖证明；该 compiler 的 pointer scan 保留。后继新入口在 source receipt 足够时支持 alias 快捷接受，拒绝继续原 scan。旧宽度检查本来也是一轴符号化 endpoint 检查，替换它不等于已消除 footprint 枚举或实现一般 projection。

P3 后继的 [源观察与 alias 包络](source-observed-affine-separation.md) 实现真实 prefix receipt、实际 Boolean 编码、modular 四字节分离、全部源 footprint coverage 及 readonly shortcut／原 scan 的局部组合。[完整 compiler](clight-observed-pointer-compiler.md) 进一步绑定 normalized source AST，复用原 mapped／tiling／schedule checker，并通过已证明的 sequence progress 接到程序。真实 prefix load 与后缀 store 均保留；机器路径探针确认快捷接受跳过扫描、拒绝继续扫描，随后选择候选或源循环。缺失／破坏观察许可时只能使用原 scan。

共享 fallback 的实际 lowering 已接入 [共用 compiler factory](clight-shared-pointer-shortcut.md)：同一入口按 Boolean 选择 direct／shared，同一 source matcher、三类 candidate checker、D／P 和条件推导只有一份。语言层新增真实正常执行运输，核心未变，优化方不重证 C_opt／coverage。79 端点审计、提取、两个完整十五配置矩阵及二十个机器路径探针通过；本轮三十个配置全部新编译，共 11,280 次配置内调用，十五份 direct Clight 摘要与冻结基线一致，见 [阶段记录](research-checkpoint-2026-10-06-shared-pointer.md)。已通过的二维 interchange 配置将 scan AST 13→1、linked 函数 11,750→1,566 字节；候选仍可重复，两个对称 base 比较保留，尚无运行成本测量。后续优先扩展非盒状 affine pointer 域和依赖 preload，并按 P4 在无并发构建时测量同版 CompCert 对照。优化作者的 obligations／证明负担继续单独统计，与 related work 做同例对照。

下一阶段的具体非矩形 pointer 切口、三方义务、包络与安全扫描的区别及验收见 [affine pointer 域计划](affine-pointer-domain-next.md)。先关闭真实域／候选对应和非空符号接受，再扩依赖 preload；不把 bounding box 当作源权限覆盖的扫描域。

非矩形 pointer 接入的前一阶段交付局部证明支持：语言的 framed source decode／实际 first-body frame；domain 的 `[i;j]++entry_context` Loop、实际 pointer 源对应、ragged footprint／capability／包络覆盖；原 candidate checker 的显式源模型接口，以及候选 Clight lowering 与公开 affine 出口恢复。核心未改，原矩形包络实例复用同一 pair compiler／物理分离服务。

该支持阶段通过 36 端点／515 项实际依赖审计；原 compiler 经当前 81 端点审计、重新提取与两模式各一配置的 376 次调用回归，见 [新记录](research-checkpoint-2026-10-06-affine-pointer-support.md)。候选运输与条件支持已有具体三角域实例，尚未由新 package 组装。全十五配置没有重跑，新 pass 没有原生运行；此前 `f144d45` 的完整矩阵继续是冻结历史证据。计划与 goal 保持未完成。

后继 [源 package 与条件阶段](research-checkpoint-2026-10-06-affine-pointer-source.md) 已实现 normalized AST／元数据 checker，并从真实源有限正常执行取得 header／body 参数读取证据；按 row／N、header range、width、body range 组织 readonly condition，消费 kernel 的组合服务。其实际接受已经接到同一 package 的 pointer 源 Loop 执行和精确公开出口；旧一维 affine-access API 保留。Clight fixture 证明接受，以及破坏增量、窗口、pointer 覆盖、未使用几何的拒绝；n=0 的实际 decision_run 不读取未定义 body 参数。

后继 [完整 source guard](research-checkpoint-2026-10-06-affine-pointer-alias.md) 已将保留 prefix 的真实 pointer receipt、实际域包络／物理 non-alias 接到同一 source package 和入口，继续消费 kernel sequencing。静态 column cap 先在 domain 层代入 endpoint，语言层复用 modular 求值和 signed 范围编码；不需要虚构源 count 寄存器。79 端点／526 项依赖／871 份源码摘要审计通过，没有新增全局公理。完整条件接受已绑定实际源 Loop／精确公开出口，尚未绑定新的候选或完整程序。

后继 [非矩形 pointer compiler](clight-affine-inner-pointer-compiler.md) 已关闭上述同一入口连接：两套 candidate ranges、独立 mapped-domain／dependence certificate、实际 lowering／公开出口 restore 和 local rule；normalized source/prefix/suffix 运输接入已有 progress／placement host，得到新 `compile_affine_inner_pointer_correct`。原进展 checker 在具体新源 fixture 上通过，没有重复发明宿主定律。103 端点／533 项依赖／878 份摘要审计和提取通过；六个新原生配置每个 81 次调用、共 486 次，五个机器路径探针区分真正候选／源执行。实际 `j<i+1`、`j<2*i+1` 的不受信任候选和 schedule generation 均已选中；错误域、直接除法边界、资源耗尽与缺失 source receipt 保留源。该结果独立于旧 compiler/native 矩阵。

本次也明确了 optimizer/domain 的一项表示责任：generated 参数检查含 `2147483648` 或 `-a` 时不能直接降到 signed32，除法边界也不能直接通过 affine extractor。不受信任的候选整理器提出参数 guard 删除与粗范围／affine 条件替换，整个结果再经原 checker；不把整理器当作 `C_guard` 的证明或可信 residualizer。两个实际域消费同一证书和 host，kernel 未改，性能和作者负担尚未测量。

后继 [nonrectangular pointer tiling](research-checkpoint-2026-10-06-affine-pointer-tiling.md) 已把实际 candidate Loop 和 quotient witness 接到同一 package、候选证书与完整编译器；2×3／4×1 在两个源域实际安装，错误 link、缺失源点和非正 tile 大小拒绝。mapped／tiling 共用条件、restore 和 local contract，kernel／语言 host 未改。109 端点／535 依赖／879 摘要、十一原生配置共 891 调用和七个机器路径通过。tile 控制数来自 metadata caps 的编译时除法，不宣称已有通用运行时 floor/ceil lowering。前阶段的 103 端点／六配置记录保留为历史证据。

后续按难点排序：优先实现多个依赖 preload 的安全读序、原入口事实和参数稳定性，再推广一般深层 affine 域。当前完整 guard 的 D 仍使用有限正常源完成和 retained source receipt，不能替代依赖加载／无限源的有限前缀协议。保守不同-base 拒绝与真实 ragged scan 的组合也需独立 capability／private-state 证明。P4 和同例 near-neighbor／作者 obligations 比较继续有效，完整 goal 保持 active。

OLO 的需求验收仍以义务区分：当前已安装实例提供机器范围／no-wrap、真实 nonrectangular footprint、物理 alias 条件、mapped／tiling 候选依赖保持和全程序安装；该 compiler 尚未覆盖每次循环测试重新读取的 memory bound。不能把“源已 preload 到稳定寄存器”作为这一困难情形已解决的证据。

后继 [loaded pointer 局部规则](research-checkpoint-2026-10-06-affine-loaded-pointer.md) 已证明一个真实三角源的 bound 反复读取／缓存运输，并接到原候选证书与保留 prefix 的 contract。语言提供 preload 值观察和 active-loop 运输；domain 提供 byte 级观察保持、保守 affine cell exclusion，以及 source 活动支持的 first-body words。kernel 未改，实际 full condition 消费依赖顺序组合，D 不预设未来稳定性。31 端点／540 依赖／884 摘要审计通过，无新增全局公理；原 42 假设 compiler 独立回归通过，原 891 调用报告重新核对绑定、未重执行。

该局部阶段当时没有新 loaded 选择器、完整程序端点、提取或原生结果。其安装验收要求 source progress 不假设 bound 稳定，并实际连接 frontend／matcher、原候选工厂、完整程序端点和运行证据；各项不能互相替代。

后继 [loaded placement 阶段](research-checkpoint-2026-10-06-loaded-placement.md) 已关闭语言 progress 和程序证明连接。strict signed nested 协议按机器最大值计算距离，不依赖 memory bound；真实 AST checker 允许 body 改写 bound 单元，拒绝改写外层 iterator。table host 复用 private-pool、scope 与原程序安装定理。固定 source profile 的 mapped／tiling／schedule checker 已消费原 loaded 局部 contract，支持 sequence association 和保留 quiet suffix，得到新的 Csem→Asm endpoint；kernel 未修改。55 端点／546 依赖／890 摘要审计通过，无新增全局公理；新 compiler 与独立旧 regression 均继承 42 项假设。旧 891 调用报告再次核对绑定，没有重执行。

下一项优先推广这个 source adapter 到真实 frontend names／AST，并在完整 C 上给出非空候选接受、提取、回退／alias／公开出口／外围上下文的原生证据。当前 profile 的固定标识符和 proof endpoint 不构成这项功能验收。随后推广任意 bound pointer 与多个依赖 preload；后项读取的许可、original-entry 条件和 private snapshot 稳定性继续独立验收。本例使用源已有公开 preload，仍使用有限正常源完成域，不宣称解决全部依赖读取或一般无限源。更一般深层域、P4 和同例作者负担保持在目标内。

## 每个阶段固定记录什么

1. 输入／候选／condition 的实际定义和选择器支持域；selector cap 与局部定理范围分别列出。
2. D 从哪里获得，P 在哪里建立，哪些后续访问需要已接受事实；不得在 D 偷放 P。
3. 局部有限等价或小步协议、公开出口／frame、宿主覆盖的发散和控制出口。
4. 完整程序端点、继承假设、源码／报告／编译器 stamp；native 回归与形式证明各自的边界。
5. 同一 source／D／P／candidate 下复用了什么，专属 obligations 和 proof code 有多少；新增模板不自动计作独立贡献。
6. 未完成项、评审意见处理状态、commit 与远端 push。原评审保存固定 SHA，新状态另记，不把历史判断默默改成当前事实。
7. 三方责任与难点：框架新增服务、语言实例新定律、优化方专属 proof／checker 各是什么；最难义务实际如何关闭，哪些仍由调用者承担。更新 [责任矩阵](framework-responsibilities.md) 和研究定位。

接口原则保持不变：最小 kernel 的 `select_exact`／局部证书组合保持；只读前台是上层库；语言实例解释语义、观察、安全和控制，使用者决定寻找片段、rewrite 提案、遍历、优先级与资源预算。框架不能只要求一份任意等价定理，而要通过实际复用的检查、frame、表示和上下文设施降低规则作者工作。

## 阶段性读取评审

完成 P0、冻结 P1 接口、完成 P2 迁移，以及取得第一批 P4 样本时，重新同步评审分支，记录新增 SHA 和相对上次读取的变化。每条新增意见更新“采纳／已解决／仍待证／未采纳理由”及对应验收，不仅追加阅读链接。正文中历史能力按其固定提交解释，当前主张依最新实际产物更新；不因评审分支比 main 旧就整体忽略意见，也不把已被后续证明关闭的缺口继续列为当前缺口。


## 参数化 memory-loaded 源的完整运行验收

[本阶段](research-checkpoint-2026-10-06-affine-loaded-compiler.md) 已关闭固定标识符、真实 frontend 接受、提取和原生验收缺口。源 snapshot 可处在直接 load prefix 的任意位置，输出须唯一且不覆盖 pointer；checked source/metadata 来自实际 AST。新 source evidence 接口以真实 loaded header/body 提供机器值读取证据，再执行 range/width 检查、全部实际 write exclusion、loaded→cached 运输和原候选 checker。框架原 sequencing、语言 progress/host/backend 继续被实际入口消费。47 端点／549 依赖／893 源摘要审计和新 Csem→Asm、提取通过；十一新编译配置各 150 次调用，七个机器探针确认候选和原 loaded fallback。

下一必交付调整为独立 bound pointer 的动态 write-footprint 分离：source 保留的 bound load 要能进入当前 source package，alias/bound stability 条件共同覆盖所有 stores，guard 失败仍用不预置稳定性的语言 host。之后实现依赖 preload 的安全读序和 private snapshot，扩展一般深层 affine 源。当前同 write-buffer cell 0 的静态 exclusion 不称动态任意 pointer 支持；新版 preparation 接口先由 loaded 入口消费，旧 cached 入口仍保留原证明，尚未证明总 proof burden 降低。P4 和同例 related-work/作者负担验收继续独立，完整目标 active。

## 独立 bound pointer：源顺序稳定性证明服务

[本阶段](research-checkpoint-2026-10-06-affine-loaded-stability.md)完成实际 stores 到原 guard entry 的权限运输、实际完整 row 的 write receipts、坐标替换后的 Clight 地址求值、支持不同 blocks 的 pointer equality／物理分离，以及实际当前行 guard 的安全／完成／接受保持。语言的 loaded-prefix invariant 保存剩余真实源执行，正结果才允许续行；没有在 D 中放未来 bound 稳定性。上层 prefix library 被实际消费，kernel 不变。

下一必交付保持独立 bound pointer 的完整安装，顺序固定为：

1. checked source package 消费现有 range／word／row-decode 定理，证明每次到达的 `memory_affine_row_domain`；完成初始 loaded-prefix witness 和足够 fuel 的覆盖证明。不得把界限稳定性或完整未来 footprint 当作安全域。
2. 让实际逐行 guard 消费上述实例证书，推出全部实际源 writes 的观察保持，并接到新的 external loaded→cached 运输与原 mapped／tiling candidate 证书。
3. matcher 接受独立 bound pointer，核对它受 frame 保护并来自 retained source read；保留真正 loaded fallback，复用语言 progress／placement，取得 Csem→Asm、提取和完整 C 运行证据。
4. 验收独立 blocks、同 block 不同 offsets、写中 bound 后提前停的源、当前行 alias 拒绝而后续危险地址不被检查。记录 guard AST／shared lowering 成本，性能独立测量。

本阶段是证明服务，不称已经完成这个安装。当前行 domain／decoder 仍由实例证明；编译器能力仍以此前 loaded compiler 为准。之后才推进依赖 preload 和 private snapshot。


## 独立 bound pointer：实例和 compiler proof 已连接

[本阶段](research-checkpoint-2026-10-06-affine-dynamic-loaded.md)已完成上一列表的前两项，以及第三项的 matcher／候选／Csem→Asm 证明：实际 checked package 填完所有 scan callbacks，range 与 count/width 证书证明足够 fuel 覆盖；完整分离 guard 接到 exact loaded→cached 运输及原 mapped／tiling／schedule checker。新 normalized AST fixtures 核对独立 pointer 接受、缺 receipt／pointer 覆盖／控制变量冲突拒绝。最小 kernel 不变，原上层 prefix/sequencing 库和语言 host 被实际消费。

提取／真实 C frontend／原生验收仍未完成。新的优先顺序为：

1. 保留 sequential/branching 结构的检查 plan 或 nested scan lowering，避免在每个 row 的接受出口复制后续扫描。实际 syntax fixture 已显示此增长；单独共享 candidate/fallback 不解决它。
2. 证明新 lowering 与已认证 guard 的求值／短路顺序对应，公开 temp/memory frame、private result/cursor、checked-entry 与 defined dispatch；复用既有安装 host。
3. 提取新 compiler、绑定真实 C，运行独立 blocks／同 block 不同 offsets／bound 被写后提前停／alias 后危险后续地址未求值；机器探针验证候选与 repeated-load fallback。
4. 完成这一运行验收后，推进依赖 preload／private snapshot 和一般深层 affine 源。性能与同例作者负担仍独立验收，不把编译定理或 AST 计数当作这些结果。

原 1,650／891 次调用的 native 报告仅重新核对产物绑定，本阶段没有重执行旧矩阵，也不把旧结果算作独立 pointer 新运行证据。完整 goal 保持 active。

## 独立 bound pointer：顺序 plan 与完整运行已验收

[后继阶段](research-checkpoint-2026-10-06-affine-planned-loaded.md)已关闭上述顺序 plan、private frame／defined dispatch、提取、真实 C 和机器路径缺口。plan 直接降低为顺序 Clight，旧 tree 只作为证明规格，提取不包含其展开函数；原完整条件、源 package、三类候选 certificate 和语言安装 host 被实际复用。119 端点／587 依赖／931 摘要审计，六个新编译配置各 37 调用、十三个机器探针通过。不同 blocks 的 bound 和同 block 的非写 offset 确实接受；第一／第二行写中 bound 确实保留提前停止；小数组探针确认拒绝后不执行未来 row 的地址比较。默认 64×64 caps 也有实际安装和候选运行证据。

这一进展没有改变 kernel 截止位置。语言 plan/code 对应、scratch 初始化、frame 和实际分派是上层库；优化实例证明 plan 等于原条件，host 继续负责 source progress 和 Csem→Asm。当前保持有限正常源完成域；不将正常 branch 运输定理扩大成一般 divergence／任意控制出口支持。body alias 的同-base 快捷条件仍保守拒绝不同 body base。

新的优先验收：

1. 原源没有 public bound snapshot 时，插入 fresh private snapshot。由实际到达的原 header 证明读安全，保留 original-entry 谓词并证明 private/public 运输；源 fallback 保持 repeated-load 语义。单独记录新增 matcher、私有资源和 placement 证据，不用一条假设或预置稳定性替代这些证明。
2. 扩展多个依赖读取的合法顺序、定义性、stores 稳定性；body pointer 观察不能因被命名为 preload 就自动合法。复用当前 prefix／private-state 库，真实案例受阻才讨论 kernel 接口。
3. 将按 cap 展开的 scan 循环化或进一步符号化。当前默认 cap 的完整 Clight 函数有 12,518 个 if，虽然消除了旧 tree 的 continuation 复制，代码成本仍需处理；与 P4 的完整成本、同版 CompCert 对照及同例作者负担比较分别验收。
4. 扩展一般深层 affine 源／复杂 body 和不同 body base 的物理 alias 条件；当前新运行矩阵是独立 bound 的三角源，不与旧两域矩阵混称。

旧两个 native validator 的绑定复核通过，矩阵未重执行。narrative 仍为 `7d94d81`，本地正文与再次 fetched 分支一致，另两个评审分支也无新增。完整 goal active。

## Private snapshot：原 source scope 与两类 affine 源已验收

[新阶段](research-checkpoint-2026-10-06-affine-private-loaded.md)关闭上一列表的第一项：语言 preparation 桥由原 source 的实际首次 header 取得 typed read，在原入口安全插入一个 fresh private cache；只用 public agreement 运输执行，消费 prepared source 的扩展 scope 契约后收回原 scope。真正原 source 仍为安装 key，原 host 的 source progress 保持，不要求使用者另证中间源 progress。新的 domain adapter 委托整个既有 planned-loaded factory，没有重证条件／候选或修改 kernel。

审计 140 端点／43 语言端点／592 依赖／936 source 摘要，提取和三角域、`j<2*i+1` 各六配置共 444 次新入口调用通过。74 次旧入口同源对照确认其静态不安装；28 个机器探针含两个旧入口对照。新增实际 bound cache 私有，公开 marker 始终为 123；写中 bound 的源提前停止和只有第一行合法的短数组得到保持。旧三套矩阵只绑定复核，不计入新验收。仍需源已有 body-pointer receipts，当前功能不包括依赖 dereference。

当前后继优先顺序：

1. **多个依赖 header 读取。** 以 `i<**pp` 这类真实源为切口，语言从实际 header 分别提供 pointer-cell 和 bound-cell receipt；domain 证明两种 chunk 的 byte footprint 排除、正结果之后才安全推进的源前缀，以及接受后两次观察的保持。原复合 header fallback 必须保留。private capture 的运输桥继续复用，不能把已有单个 `Mint32` 不等比较推广为 `Mint64`／`Mint32` 不重叠。
2. **guard 大小与成本。** 按 cap 展开仍产生约 12,500 个 if；实现 scan 循环化或经证书的符号足迹，继续独立 P4 测量。公开 AST 文本、最终机器大小、编译成本和执行成本分开报告；当前没有性能收益结论。
3. **主 domain 表达力。** 一般深层 affine 源、复杂 body、多参数／布局组合及不同 body base 的物理 alias 接受。两个实际 affine 域是本次表达力证据，但不代表任意多面体已迁移完成。
4. **同例责任与已有工作比较。** 用当前私有读取／前缀安全例检查 OLO、Chamois、Peek／COVE、CoreJIT 的条件、语言、安装义务；记录真正复用的 certificate 链，尚不主张 total proof burden 或 novelty 收益。

沿 narrative `7d94d81`，上述读取／条件推导留在语言和 domain 库，kernel 仍只组合局部证书；host 负责 progress／context 安装。guarantee/requirement clause API、第二 IR 或新 kernel 能力只有实际接入受阻时才推进。完整 goal active。

## 依赖 header：服务已证明，完整实例继续接入

[最新阶段](research-checkpoint-2026-10-06-dependent-header.md)落实上述第一项中的语言与逐点 domain 服务：实际 `**pp` header 的两个 typed reads、安全 ordered captures／public-scope preparation、不同 chunk 的 byte separation、实际 affine write sequence 保持两项观察、全部观察保持后才推进的 prefix，以及 source→cached 实际执行运输。另有 signed-expression progress selector，不把未来稳定性写进 source progress。九个新增模块、51 端点审计通过；没有新 native 或 compiler 入口。

下一验收按依赖顺序推进：

1. 从真实 checked affine package 生产 joint row／outer scan 的所有证据：实际 header、row decode、全部坐标范围、write receipts 与足够 fuel。使用现有 concrete HEADER 和逐点双观察 condition；不以 generic scan 的参数或 exhaustion 冒充源覆盖。
2. 接完整 guard 到原三类 candidate certificate，保留原 `**pp` fallback；actual host 消费新 progress selector，并落实 pointer／bound／Boolean／counter private pool 的不同类型、freshness 和真正 original source key。
3. 提取新入口，运行完整 C 接受／回退／上下文。当前 memory 后半单元重叠 fixture 不是 defined C loop benchmark；先用合法 bound 改写拒绝和稳定依赖读取接受。需要 typed pointer-store body 才能覆盖合法改变 pointer cell 的更一般源，不能将 progress fixture 计作 optimizer body 支持。

guard 循环化、一般深层域、不同 body base 的 alias 接受、P4 和同例 proof obligations 比较保留后继优先级。该接入不要求新 kernel 能力，完整 goal active。
