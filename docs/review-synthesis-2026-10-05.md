# 2026-10-05：三个评审分支的综合判断与采纳记录

这次读取的是远端分支的固定提交，没有切换或覆盖实现工作树。三份评审共同以 main `cf4d44292cd1e834e79db31d0ac3a75696a7d40c` 为基线；原评审材料保留这一时间边界，后续实现状态单独更新。

| 分支 | 已读取提交 | 材料 |
| --- | --- | --- |
| `docs/evidence-to-claim-2026-10-05` | `9673381676e18ed0afbc6114e0a62bea9c48002c` | [逐能力证据矩阵](evidence-to-claim-2026-10-05.md)、`research-position.md` 修订 |
| `docs/minimal-native-performance-cf4d442` | `3e9f0080def8c029cceedbd35184b4de7b8b96bc` | [最小性能方案](native-performance-plan.md)、[报告 schema](native-performance-report.schema.json) |
| `topdown/research-positioning` | `39df0d0a40c2c16642b4e4ed91fd8137a87a46c6` | [main 源码评审](topdown/main-review-cf4d442.md)、[C/Clight 宿主](topdown/c-level-host.md)、[抽象选择](topdown/host-control-structure.md)、索引 |

评审的文献复核、源码阅读和历史回归记录不等于本轮独立复现。特别是 evidence 分支明确说明 Chamois 全文／当前 oracle 文档未取得，其能力不能据此被否定。本轮综合核对现有接口和当前新增源码；新的文献能力判断仍需原论文／artifact 的同例调查。

## 核心判断

框架值得发展的部分是**把真实源路径给出的定义性、权限和稳定性依据处理成安全的可执行检查，再复用条件证书完成简化、lowering 与完整程序安装**。已有的抽象 select 定理、C/Clight 层、runtime fallback、多次 pass 组合或新鲜 cache 本身，不能单独承担研究差异。

这个判断收紧了定位，没有缩减用户要求的功能目标。多面体／乐观循环变换仍是重要验收；但验收要以实际候选、机器检查、局部证明、完整程序端点和提取执行构成一条链，而不能把旧 affine 路线的能力与新只读接口的能力相加后宣称迁移已完成。

## 逐项采纳

| 评审意见 | 当前核对与决定 | 已采取／后续动作 |
| --- | --- | --- |
| 不要再设计第二个抽象 choose record | 采纳。`GuardInterface.select_exact` 已经是语义接口；右侧 Gallina `if` 不要求目标语言有 literal if | 固定现有核心，不把 unsigned、alias 或 Clight continuation 放进核；更新 [工作计划](current-work-plan.md) |
| 继续保留小的只读前台 | 采纳。具体 lowering 可以写私有 state，但不能静默放宽 `checked=entry` | 以 realization 的状态／观察关系证明具体实现；不让每个优化作者默认处理任意 effectful guard |
| direct/shared 还没有完全共用 realization 边界 | 采纳，这是模块化缺口，不是已确认的 soundness bug | 优先用已存在的 direct/shared 两种实现检验一个证书边界；计入资源、freshness、公开观察、actual dispatch 和宿主模拟，避免只增加空 record |
| 整段回退可能无限必须优先于新矩形模板 | 采纳，当前实现已正面处理 | `open_region_protocol` 不要求 source completion；有限实际源前缀建立检查域，后续逐步匹配。unsigned memory-bound 源和 guarded 目标均有实际 alias `forever_silent`，Csem→Asm 端点已编译；提取／原生以 [阶段记录](research-checkpoint-2026-10-05.md) 为准 |
| prefix scan 的 fuel／活动结束不自动等于完整足迹覆盖 | 采纳 | 后续算法必须有源实例覆盖证明；记录 caller 提供的 coverage、源 cursor、权限运输和检查专属 obligations，不能把 generic scan 定理当成自动完整性 |
| `entry_derivation` 不是一般投影／条件发现算法 | 采纳 | 明确 certificate interface 与算法实现的区别；选一个受限 symbolic 条件／足迹路径，并实际接入候选和编译入口；不承诺任意 Prop 或最弱 guard |
| 旧 affine／tiling 未迁移，两个 loaded 与参数 stride 未一般组合 | 采纳 | 单独验收迁移和组合，不将不同配置的能力拼接成一个通用 pass；选择一次真实 affine/tiling 迁移作为后续主线 |
| endpoint／native 次数不是创新或 kernel 数量 | 采纳 | 保留计数作为审计与回归覆盖；来源、假设基线、selector cap 与定理域分别报告 |
| 静态 Clight 缩小不能推出性能或实际接受率 | 采纳 | 吸收最小性能计划与 schema；主基线使用未修改的同版 CompCert，分开接受／回退／静态拒绝，记录实际产物与分支证据 |
| 应量化复用和同例比较，而非堆模板 | 采纳 | 记录 generic／adapter／规则专属证明与作者 obligations；对 OLO 的 loaded-bound/alias 场景列相同语义义务，Chamois/Peek 未核实处标未知 |

## 对当前新实现的影响

新增的是具体语言的上下文宿主，不是另一个通用 guard 核。规则作者提交任意 enclosing continuation 上的局部小步协议；通用宿主连接 scope、freshness、memory 和控制上下文。目标正步数匹配不用下降索引，零步匹配才下降，因此拒绝分支可以持续执行。初始规则沿头部／首次 store 的有限真实前缀取得 guard 安全依据，不用整段源完成性，也没有 runtime ghost 权限查询。

真实 C 验证还揭示了表示义务：frontend 在循环 body 加 `Ssequence Sskip`，`++i` 使用 signed `1` 常量。局部模型、选择器和阶段机必须匹配这些实际节点；生成代码没有选中时，模型定理不能被计作运行实例。这项修正纳入本次接入，而不是放宽选择器绕过核对。

新接口当前只有同函数 `State`、label-free 和正常公开出口；初始规则是 quiet Mint32 模板。它解决一个完整无限回退案例，不自动覆盖一般内部调用、异常出口或任意 guarded tiling。新树每处仍有两份完整回退，也给 realization 统一提供了实际后续测试对象。

## 性能方案的采用范围

采用四个机制 fixture：双动态矩形的 shared-tree／simplified 对照、loaded stride、双 loaded 幂等写入消除、固定 2×2 对照。正式主比较是相同 backend 的原源 S 与含真实 guard／candidate／fallback 的 V；GCC -O0 继续作为正确性 oracle。候选单独执行只用于已接受输入，诊断派生代码要标明不属于生产证明端点。

测量必须等待证明／构建任务停止后，在可记录环境中运行；本轮持续构建期间不采集并发噪声下的计时。首先核对真实路径、最终符号字节、产物 hash、reset 和公开出口，再取得原始 batch。没有合格样本时报告 planned／invalid，不填速度结论。schema 的结构校验也不能代替跨产物引用、实际分支或测试正确性。

优先级和每项验收已落入 [当前工作计划](current-work-plan.md)，后续阶段汇报同时核对该表；评审不只作为附加阅读材料。

## P0 验收后的第二次同步

再次同步远端后，topdown 分支新增 `90b8520`／`4521f76ab11c2df1332ce06a5cf4b83a613be27b` 的 [paper narrative](topdown/paper-narrative.md)；其余两个评审分支没有新增提交。新增意见已读取并采纳：保持“小的语言无关语义框架＋有实质算法与条件正确性证明的 CompCert 使用者”作为同一研究论证，明确区分 `C_opt: A⇒candidate correct`、`C_derive: B⇒A`、`C_guard: accepts⇒B` 和 `C_host`。条件提取仍由 optimizer/domain plugin 提供，符号化推导作为受限 domain library，不重新定义一个 universal extractor。

这影响后续 P2／P3 的验收：P2 不能只有围住预先给定候选的 guard，还要实际消费候选／依赖验证和源／模型对应；P3 要说明逻辑入口 B 如何覆盖模型义务 A，而非把编码 Boolean 当成已完成推导。论文路线仍是设计建议，不作为未实现能力。P0 已通过 401 端点／862 摘要、25 配置／40 报告；具体结果见 [阶段记录](research-checkpoint-2026-10-05.md)。

## 用户确认方向后的目标补充

用户要求持续沿 `topdown/research-positioning` 的 `paper-narrative.md` 改进，并特别区分框架、语言实例和优化方的验证责任。再次 fetch 确认该分支仍为 `4521f76ab11c2df1332ce06a5cf4b83a613be27b`。已将这一要求作为 [活动目标](current-work-plan.md) 的持续组成部分，新增 [责任与难点矩阵](framework-responsibilities.md)，同步当前研究定位。

阶段验收必须回答四张证书各由谁提供、哪里复用以及最难义务如何解决。优先核对 `B⇒A` 的全部源实例覆盖、guard 自身机器安全、实际候选／模型对应、有限与无限宿主行为，及规则作者证明负担；不再仅以文档分层或 theorem 数量计作这方面完成。P0 实现已以 `593ebf1` 推送 main；后续实现继续按这一目标推进。

## P1 接口冻结与验证

2026-10-06 冻结实际接口时再次 fetch 三个分支，全部维持上次 SHA，没有新增意见。direct/shared 已接到 [公共 realization](clight-guard-realization.md)，完整 unsigned 循环另消费其有限 dispatch prefix；三个路径的语言证明复用、private state／frame 与能力限制已明确。411 端点／863 摘要没有新增公理，25 配置／40 报告重建通过，40 份 C／Clight 摘要相对 `26956a4` 不变。P1 的这项实现验收通过；不据此声称 shared whole-loop、一般 affine 迁移、符号条件算法或性能已经完成。

旧 `encoded_private_rule` 与 named affine／tiling compiler 的源码核对揭示条件性 source-to-candidate 保持及实际 globalenv 的边界；已补入责任矩阵和 P2 验收。P2 将实际消费候选／依赖核对、复用其对应证书，并按语言宿主需要的正确证书方向接入，而不是把原证明强称为双向等价。

## 10 月 6 日：首个真实 P2 使用者及新 topdown 补充

再次 fetch 后，evidence 和 performance 两分支仍为原 SHA；topdown 新增 `f7936299fa6272fbf50db6b94a1bd0333808ea09`。增量仅为 paper narrative 的 cross-IR 讨论，已经同步到本地快照并采纳：SSA/CFG 可以把 code/check 解释为区域和检查 CFG，汇编可以暴露 registers/flags/memory；对应语言实例另证明 phi/live-out、scratch、flags 与控制。Clight 仍是主验收，第二 IR 是可选证据，不将讨论中的实例标作已实现。

Peek、COVE/cSTOKE、Chamois 和 CoreJIT 继续约束跨 IR 的研究主张；新方向文档不是对它们能力的新的独立文献核实。不声称 runtime-conditioned assembly 优化或 local-to-global lifting 是首次提出。语言状态运输必须覆盖实际检查的 flags 副作用，不能因抽象 readonly 条件省略这一义务。已纳入[责任矩阵](framework-responsibilities.md)与[当前计划](current-work-plan.md)。

首个 [named affine／tiling 使用者](clight-polyhedral-preservation.md) 已实际复用旧 source/model/candidate 和范围／alias 证书，消费真实 candidate/dependence checker，并通过主 readonly condition 与 direct/shared realization 接 Csem→Asm。source-to-candidate 保持与双向规则共用安装证明，未增加旧 checker 没有提供的反方向。原生多数组 40 配置和连续替换／空参数 8 配置已通过；主接口兼容性回归与阶段提交以[当前记录](research-checkpoint-2026-10-06.md)为准。这关闭首个使用者迁移；一般 affine 源、stateful pointer footprint 与新符号化 B⇒A 算法仍未关闭。

## 10 月 6 日：条件推导阶段的再次同步

再次 fetch 后，三个评审分支仍分别为 `f7936299fa6272fbf50db6b94a1bd0333808ea09`、`9673381676e18ed0afbc6114e0a62bea9c48002c` 和 `3e9f0080def8c029cceedbd35184b4de7b8b96bc`，没有新增意见。已有 narrative 对责任和困难位置的要求继续进入实现：[盒状 affine 包络](affine-box-condition-derivation.md) 将数学覆盖、机器编码和实际候选消费分别落实，复用局部与安装证明；性能／proof burden 和同例 related-work 对照仍待完成。

本次实际语义核对还修正了 P3 的 pointer 计划：访问 `p+k` 有效不保证原始 p 可比较，不能把 base-valid 偷放到 D。先交付宽度条件的实际使用者，pointer separation 的符号推导继续要求源前缀／placement 提供合法观察，并证明覆盖全部源访问。旧一轴宽度检查本来就是符号算法，因此本次不把它描述成 footprint 枚举的替代。完整 P3 和研究目标继续保持未完成；当前实现／验证见[阶段记录](research-checkpoint-2026-10-06-envelope.md)。

后继 [源观察 alias 阶段](research-checkpoint-2026-10-06-observed-pointer.md) 再次 fetch 三分支，SHA 不变。已把这项计划落实为真实 prefix receipt、modular 物理分离、全部实际 footprint coverage 和同一 C_opt／scan 的 checked fragment lowering，17 端点审计通过；新 compiler 接入／提取／实际快捷执行仍待完成。责任矩阵与计划已据此更新，保持 P3、性能和作者负担验收开放，不以片段证明完成代替完整目标。

## 10 月 6 日：源观察条件的真实程序安装

再次 fetch 后三个评审分支仍保持上述 SHA，没有新增意见。后继 [完整 compiler](clight-observed-pointer-compiler.md) 已完成实际 prefix matcher、原 mapped／tiling／schedule checker 的适配、Csem→Asm 和提取。真实程序检查暴露旧 placement 只接受根部 loop 的限制，语言库以已有 framed 小步协议证明序列组合，并运输 prefix／suffix 的 public state 和实际 memory effect；没有弱化宿主或加入 source progress 假设。67 端点的审计继承 CompCert 和原 PolCert/VPL 基线，没有新增全局公理。

十五个原生配置各 376 次调用和十个实际机器探针通过，分别确认快捷接受没有执行 footprint 地址比较、条件拒绝后 scan 接受或源回退，以及空路径没有新增 pointer 比较。完整原生矩阵由 [本阶段新报告](research-checkpoint-2026-10-06-observed-compiler.md) 绑定：首轮分块超时后，八份已有绑定产物重新执行、七个配置新编译；前一阶段报告不计作新路径运行证据。核、语言服务和 domain 适配器的责任已同步到 [责任矩阵](framework-responsibilities.md)。

评审提出的成本问题继续落实为下一项验收：当前一个二维 fixture 的 direct tree 复制 13 份 scan，接受时也保留两个方向的 base 检查。先证明并安装共享 fallback／保持同一接受含义，再依性能方案量最终机器产物；同例作者负担比较仍未完成。这些后续工作进入 [当前计划](current-work-plan.md)，不把功能正确性或端点数量当作成本收益。

## 10 月 6 日：同一条件的共享 scan 实现

再次 fetch 后三个评审分支维持 `f7936299fa6272fbf50db6b94a1bd0333808ea09`、`9673381676e18ed0afbc6114e0a62bea9c48002c` 和 `3e9f0080def8c029cceedbd35184b4de7b8b96bc`，没有新增意见。继续按 narrative 的三方边界落实：[共享 fallback](clight-shared-pointer-shortcut.md) 只新增语言正常执行运输，既有 source matcher／candidate checker／D／P／coverage 共用一条参数化管线，框架组合定理保持。实际提取入口对 direct／shared 都有 Csem→Asm 结论。

79 端点审计、提取、两个完整十五配置矩阵和二十个真实机器路径探针全部通过。三十个配置均本轮新编译，共 11,280 次配置内调用，唯一源调用集合仍为 376 组；十五份 direct Clight 与冻结基线一致。一个实际二维 interchange 配置的 scan AST 13→1、linked 函数 11,750→1,566 字节。它回应回退复制的具体问题；条件接受域、候选复制和对称 base 比较未改变。没有运行计时、总证明负担减少或新颖性结论；下一项一般 affine pointer 域／依赖 preload 和同例成本／obligations 比较继续进入计划。最终状态与摘要已在 [新阶段记录](research-checkpoint-2026-10-06-shared-pointer.md) 冻结，不覆盖 `00b9dbf` 历史报告。

## 10 月 6 日：非矩形 pointer 局部证明支持

再次 fetch 三分支，SHA 仍保持上述值，没有新增评审文本。新 [支持阶段](research-checkpoint-2026-10-06-affine-pointer-support.md) 继续按 narrative 区分工作归属：kernel 未改；语言服务提供实际 counted-loop stable frame、first-body 到达和公开出口；domain 负责 ragged 点集、真实 pointer 源／模型对应、实际 footprint 覆盖与条件推导，candidate checker 继续独立核对域／依赖。36 端点审计和原 compiler 重提取的两模式 752 次调用回归通过。

最难的剩余义务已落实到下一项验收：源定位器必须按两个实际 active header 安排 body-only 参数读取，完整生产 D 并将 view、范围、receipt、候选 certificate 和 restore 绑定同一个真实入口，随后完成程序安装。局部 readonly certificate 已可消费调用者给出的 D，不能据此宣称自动安全域提取。原运行路径的回归不计新非矩形 pass 运行；性能、同例作者负担和依赖 preload 仍开放。没有新增 novelty 结论。

## 10 月 6 日：源 package 与分阶段参数检查

再次 fetch 后三分支仍为上述 SHA。按 topdown narrative 实现的 [后继阶段](research-checkpoint-2026-10-06-affine-pointer-source.md) 将一部分高难义务变为可消费证书：真实 normalized 源／元数据 checker；从有限正常源执行生产参数类型；用 framework 的条件组合先检查 header／width，再检查 body-only 参数；实际接受接到同一入口的源 Loop 与公开 i／j／k 出口。语言 completed-path 包装、domain source/model 证明、kernel sequencing 各自有源码端点，不把优化假设推导交给 kernel。

尚未关闭的重点是 prefix receipt 与物理 alias 条件的实例连接、独立 candidate 及两个表示范围、source progress／全程序 host、提取和新 C 原生接受／回退。当前源 package 的 Clight fixture 检查不算 frontend 或机器运行；算术 D 的 completed-source 义务不等于有限前缀或无限行为支持。下一计划按这些缺口推进，论文不增加性能、新颖性或作者负担收益主张。

## 10 月 6 日：完整源条件的 receipt／alias 连接

再次 fetch 后三分支保持 `f7936299fa6272fbf50db6b94a1bd0333808ea09`、`9673381676e18ed0afbc6114e0a62bea9c48002c` 和 `3e9f0080def8c029cceedbd35184b4de7b8b96bc`，没有新增文本。[本阶段](research-checkpoint-2026-10-06-affine-pointer-alias.md) 将上项未闭合的 receipt／alias 连接变为同一 source package 的完整 readonly condition：domain 证明静态 column 代入和 ragged footprint 覆盖，语言复用源读取 receipt、真实 modular／signed 比较、完成路径与 reachable-test 安全，kernel 继续消费条件组合。完整接受同时连接源 Loop 与精确公开出口；79 端点审计没有新增全局公理。

下一计划据此去掉“尚未连接 receipt／alias”，保留独立候选、validator／encoder 两套范围、实际候选与 local rule、source progress／placement、新 Csem→Asm、提取与原生执行。源 prefix producer 的 finite-domain 证据不算完整 host，n=63 的数学 Boolean 接受也不算 native 路径。性能、新颖性和总作者负担继续等待独立证据；责任表不代替难点的实际证明。

## 10 月 6 日：非矩形 pointer 的完整候选／程序接入

再次 fetch 后三分支仍为 `f7936299fa6272fbf50db6b94a1bd0333808ea09`、`9673381676e18ed0afbc6114e0a62bea9c48002c` 和 `3e9f0080def8c029cceedbd35184b4de7b8b96bc`。本地 paper narrative 与该 topdown SHA 的正文逐字节一致，没有新增意见。

按已有意见完成 [新 compiler](clight-affine-inner-pointer-compiler.md)：domain 绑定独立 candidate certificate、两套 ranges、实际 Clight candidate／restore、源 normalized AST 与 local contract；kernel 的条件组合和语言的 prefix／sequence/progress/private-pool／程序 simulation 继续复用。新 Csem→Asm 定理、103 端点审计与提取通过，六个配置共 486 次调用、五个机器探针确认非空候选路径和真实别名回退。实际三角域和 `j<2*i+1` 共用这条管线，schedule generation 的输出也真正通过重新核对并安装。

实例暴露一项高难表示义务：数学生成检查含 `2147483648`、`-a` 或除法边界时，不能直接交给 signed32/affine lowerer。新增不受信任候选整理器提议参数检查删减及 quotient-to-affine 控制表达，再由原域／依赖 checker 对整个候选取得证书；没有把整理器当作新公理或通用 guard synthesis。直接除法提案的静态拒绝作为原生配置保留。当前只用 direct readonly tree、保守同-base 符号接受，没有新 ragged scan/shared capability。

当前计划据此关闭该实例的候选连接、placement、提取和新原生证据缺口；进一步接 quotient/tiling 证书、一般深层域、多个依赖 preload 的合法读序／稳定性，并保留 P4 与同例作者负担比较。这是对 narrative 的实际接入检验，不新增 novelty 或盈利性结论。完整 goal 继续 active。

## 10 月 6 日：同一非矩形 pointer package 的分块接入

阶段性再次 fetch，三个分支仍为前述 `f793629`、`9673381`、`3e9f008`，没有新增意见。按 narrative 对可复用边界的要求，[tiling 接入](research-checkpoint-2026-10-06-affine-pointer-tiling.md) 将原 quotient/域/依赖 checker 转为与 mapped 相同的 candidate certificate，共用条件、机器 lowering、出口恢复和 local contract；kernel 与语言 host 保持。源／候选的实际绑定仍由 domain 负责，不归作核自动提供。

实际两个源域安装 2×3／4×1 分块，错误 witness、少一行和零 tile 的拒绝被完整 C 矩阵核对。109 端点、提取、891 次配置内调用和七个机器路径通过，阶段记录保留摘要与验证范围。tile 控制数依据 caps 在编译时计算，未增加通用运行时 floor/ceil lowering。已有接口复用事实不等于 proof burden、性能或 novelty 结论。

当前计划将依赖加载的安全读序和 memory-bound 稳定性提升为下一必交付。先前 loaded 矩形／singleton 的语言设施是可复用基础，但没有因此称它们已经接入非矩形 pointer 候选。一般深层域、第二机会 ragged scan 和同例比较继续保留，完整 goal 未完成。

## 10 月 6 日：loaded pointer 的 source activity 与稳定性

本阶段 fetch 确认三个评审分支未更新，paper narrative 与 `f793629` 正文字节一致。按已采纳的困难义务，[新局部规则](research-checkpoint-2026-10-06-affine-loaded-pointer.md) 将初始 preload 观察、首次真实活动 body 的参数定义性、接受范围覆盖全部写入和 bound 稳定性分开证明。语言提供实际执行运输；domain 提供 conservative affine cell exclusion 与真实 pointer body 对应；kernel 的域限制和条件顺序组合被实际 full condition 消费。D 没有预置未来 load 稳定性。

候选继续使用原认证 package，保留 prefix 的 projected contract 已编译。31 端点、540 依赖、884 摘要审计通过，无新增公理；原 full compiler 的 42 假设独立回归和 891 调用报告绑定核对通过。本次没有新 loaded compiler、提取或原生证据，也没有重跑旧矩阵。当前计划先实现不假设稳定性的 loaded nested source progress／matcher，随后实际安装；一般 bound pointer、多个依赖 preload 和 private snapshot 继续独立验收。


## 10 月 6 日：loaded source progress 与固定 profile 安装

本阶段再次 fetch，三个评审分支仍为 `f793629`、`9673381`、`3e9f008`，topdown 正文与 fetched narrative 字节一致。按已吸收的责任划分，[新的安装阶段](research-checkpoint-2026-10-06-loaded-placement.md) 将 bound 稳定性留在 domain 的接受证明，将原 loaded fallback 的 progress 单独落实到语言协议。新协议用机器最大值计算距离，只要求嵌套 body 保护 iterator，不假设 memory bound 保持；改变 bound 单元的 fixture 通过进展检查，改写 iterator 的 fixture 被拒绝。

原 mapped／tiling／schedule checker、实际 guard／restore／fallback 和保留 prefix/suffix 的局部 contract 已接到新 table host 与 Csem→Asm endpoint。Kernel 未改，scope/private-pool/程序安装和 backend 定律复用。Optimizer profile 仍绑定固定 normalized 标识符，frontend 的非空接受、提取和新原生矩阵尚缺；不能仅凭新的 compiler 定理称 loaded optimizer 已完成。这项事实边界已进入当前计划，下一项推广真实 source adapter，再做完整 C 接受／回退／上下文验收。一般依赖 preload、private snapshot、P4 和同例作者负担比较继续保留，goal active。


## 10 月 6 日：context boundary 新意见与真实 loaded compiler

再次 fetch，topdown 更新为 `8c098ed`；另两个评审分支仍为 `9673381` 和 `3e9f008`。paper narrative 新增 [context-lifting](topdown/context-lifting.md) 讨论，已逐字同步；[源码核对](clight-boundary-contract-review.md)回答当前 finite/open/shared/sequence host 的 clause 复用与实质差异。计划明确 language host 负责 region 契约与程序安装，优化和位置负责相应保证／放置证据，不将 kernel lifting 字段当作已完成 contextual closure。没有仅因图更整齐重写契约或 kernel。

[参数化 loaded compiler](research-checkpoint-2026-10-06-affine-loaded-compiler.md) 已消除固定 optimizer names，保留 snapshot 可在 direct prefix 任意位置；真实 frontend、Csem→Asm、提取与十一配置共 1,650 次调用、七个机器路径通过。Domain 由实际源 header/body 取得读取证据，条件范围接受后才用全部真实 writes 排除 bound；language 的进展独立于稳定性，kernel sequencing 复用。旧 affine-inner 入口因共享提取脚本修改而重新构建／验收，结果另记。仍不主张 total proof burden、性能或 novelty 收益；独立 bound pointer／private snapshot／依赖读取列为下一验收，完整目标 active。

## 10 月 6 日：最小 kernel 的截止与动态稳定性服务

再次 fetch，topdown 更新为 `7d94d81`；另两个评审分支仍为 `9673381` 和 `3e9f008`。新增十五行明确最小 semantic kernel 止于局部 guarded correctness：readonly 前台和 condition processing／prefix scan 是上层库，whole-program installation 是 language-host 责任；此澄清不要求重排文件。paper narrative 已逐字同步，责任矩阵与当前计划明确区分“框架库”和“最小 kernel”。

已采纳并在 [稳定性服务](research-checkpoint-2026-10-06-affine-loaded-stability.md)落实：既有 prefix library 保持；Clight 新增 store 权限运输和实际 loaded-row 取得／正结果续行；domain 新增真实 writes 的 receipts 和仿射地址探针编码。当前行 guard 的安全、可用性和物理保持已证明；source package 到完整逐行扫描的实例证据仍待连接，不能把 callback 参数或者旧 compiler 回归算作新完整编译器。后续计划优先完成该连接和真实运行，再讨论新 kernel 能力或 proof burden 收益。完整 goal 保持 active。


### 独立 pointer 的后继连接与运行实现风险

[新阶段](research-checkpoint-2026-10-06-affine-dynamic-loaded.md)已用 checked package 的真实访问编码／范围／word、row decode 和 write receipts 填完完整 source-order scan 实例，接受后取得全部写的 bound 保持；新 source matcher、三类候选 checker 和 Csem→Asm theorem 已连接。此前“callbacks 尚未落实”的缺口在此具体实例关闭，原泛型语言服务仍保留参数以供其他使用者实例化。

narrative `7d94d81` 的边界继续有效：没有修改 kernel；条件／prefix 是库，context 安装属于语言。另发现实际 nested tree 的 syntax 增长，下一验收增加保留顺序结构的 guard lowering 及其 private frame／短路／dispatch 证明，再完成提取与真实 C 运行。新 compiler proof 不冒充这些运行结果，旧 native 矩阵只有摘要绑定复核。尚无性能、total proof burden 或 novelty 收益结论，完整 goal active。

## 顺序 plan 与独立 bound 的运行验收

阶段性再次 fetch，三个评审分支仍为 `7d94d810685a691efbf07df734f5fad8abfb4724`、`9673381676e18ed0afbc6114e0a62bea9c48002c` 和 `3e9f0080def8c029cceedbd35184b4de7b8b96bc`，narrative 本地与远端正文字节一致，没有新增意见。

按最新澄清完成的 [顺序 plan 阶段](research-checkpoint-2026-10-06-affine-planned-loaded.md)把检查结构、private Boolean 初始化／frame／分派放在 Clight 库，domain 只追加 plan 与已认证 guard 的规格对应，复用其 C_guard／coverage／候选 certificate；原 host 提供新 Csem→Asm。最小 kernel 和 proof responsibility 边界保持。实际提取、六配置 222 调用与十三个机器探针关闭此前独立 bound 的运行缺口；小数组例子的机器探针记录拒绝后停止地址比较，默认 64×64 cap 也实际安装／执行。

当前计划已转到 private snapshot 的安全读取和 original-entry／public frame、多个依赖 preload，以及 guard 循环化／一般深层 affine 源。默认 cap 的实际 AST 仍很大，body alias 快捷条件仍保守同-base；没有把结构改善当作性能收益、总作者负担下降或相对已有工作的新颖性证明。旧两套 native 矩阵仅绑定复核，历史意见按固定 SHA 保留。完整 goal active。

## Private capture：用一次实际接入检验 kernel 截止

再次 fetch，三个评审 SHA 仍与上一节一致，paper narrative 与远端字节一致。按 `7d94d81` 澄清完成的 [新阶段](research-checkpoint-2026-10-06-affine-private-loaded.md)没有重排或扩展 kernel：safe preparation／original-entry／public-scope 运输由 Clight 库提供，domain wrapper 委托既有完整条件／候选 factory，程序安装继续由语言 host 证明。原 source 的实际首次 header 许可 private bound capture，私有初值可以任意；host 不要求准备后的中间源额外有 progress，rewrite key 也没有换成中间源。

两类实际无 bound 快照的 affine 源完成 140 端点审计、同一编译器提取、六配置各 37 输入共 444 次新入口调用和 28 个机器探针（含两个旧入口对照）；74 次旧入口同源对照确认“不安装→能安装”的实际 frontend 差异。公开 marker 保持、写中 bound 提前停止、危险未来 row 检查跳过均有机器证据。旧三套矩阵仅绑定复查。责任区分因此有实际消费证据，但不据此推出总作者负担下降或 novelty。

当前计划将单个 direct private snapshot 标记验收，依赖 header 读取的合法顺序／不同 chunk byte footprint、循环化 guard、一般 affine 源、P4 和同例已有工作比较继续未完成。新增 preparation 桥不会自动证明 `**pp` 的 pointer 与 bound 稳定性；继续由语言／domain discharge，只有真正不可表达的义务才调整 kernel。完整 goal active。

## 依赖读取：澄清落实到不同 chunk 的实际义务

本阶段再次 fetch，三个评审分支仍为 `7d94d81`、`9673381`、`3e9f008`，没有新增意见。沿 narrative 的 kernel 截止完成 [依赖 header 服务](research-checkpoint-2026-10-06-dependent-header.md)：语言处理 `**pp` 实际表达式、安全顺序捕获、公开运输、字节条件、观察列表下的 prefix／缓存运输和独立 progress；domain 将实际 affine writes 接到双观察保持。九个新模块和 51 端点审计通过；完整 checked-package scan、candidate factory／whole-program 入口、提取及原生执行仍未连接。

这次的实质难点是八字节 pointer cell 与四字节 write 的重叠，起点不等不足以证明观察保持；安全第二地址比较的许可也必须来自已到达的真实 load。CompCert memory fixture 已验证后半单元拒绝，但不将可能破坏后续 pointer 的单元实验当作 defined C 优化案例。计划已据此区分逐点服务、全部源覆盖、候选合法性和宿主安装；仍没有 total proof burden、性能或 novelty 结论。

## Joint scan：从服务参数到真实 package 证据

再次 fetch 后三分支仍是 `7d94d81`、`9673381`、`3e9f008`，本地 paper narrative 与远端正文一致。[后继局部链](research-checkpoint-2026-10-06-dependent-joint.md)用实际 checked affine package 填完多观察 prefix／cache 的 header、body decode、word／permission 和 cap coverage 义务；从首次真实 header/body 生产 preparation evidence，组合双观察 scan 与旧候选 guard，再证明实际 candidate／原 source 分派的 memory／public-temp 保持。七个新模块、29 端点审计通过，最小 kernel／原 checker 保持。

此前“generic callbacks 未落实”的问题在该实例关闭，仍不将其当成 framework 免费提供的能力。计划继续追踪 source matcher／factory、typed private pool、capture domain producer 与 whole-program 安装／提取／运行；旧 private-loaded compiler 回归保持原 42 项基线。当前没有 dependent native、性能或作者证明负担减少的证据，完整 goal active。

## Narrative 澄清：在实际 compiler 接入中落实

再次 fetch 三个评审分支，仍为 `7d94d810685a691efbf07df734f5fad8abfb4724`、`9673381676e18ed0afbc6114e0a62bea9c48002c`、`3e9f0080def8c029cceedbd35184b4de7b8b96bc`。核对最新 narrative commit 的十五行澄清，本地正文相同：最小 kernel 只到局部 guarded correctness；readonly 前台／条件处理／prefix scan 是上层库；整程序安装由具体 language／IR host 提供。它明确不要求立即重排文件，只在真实实例无法表达义务时讨论 kernel 变化。

已吸收到 [dependent compiler](research-checkpoint-2026-10-06-dependent-compiler.md)和当前后继计划：language 层负责 actual-header 安全 captures、私有运输、typed pool、progress 和安装；domain 负责 exact source／checked model、两项观察的 footprint 保持、条件 plan 对应及候选 checker；最小 kernel 不变。九个模块、40 端点审计、新 Csem→Asm、提取、444 次新入口调用及 28 store-order 探针关闭上一阶段的完整接入缺口，仍不主张 generic assumption extraction、自动 contextual closure 或 proof burden 收益。

## Narrative 再核对：cursor scan 服务的责任与剩余验收

按用户提示再次 fetch；topdown 仍为 `7d94d810685a691efbf07df734f5fad8abfb4724`，另两个评审 refs 仍为 `9673381676e18ed0afbc6114e0a62bea9c48002c`、`3e9f0080def8c029cceedbd35184b4de7b8b96bc`。paper narrative／context note 与远端无差异。最新十五行澄清已经采纳，不重复算作新增意见。

按该边界完成 [逐行 cursor scan 服务](research-checkpoint-2026-10-06-cursor-scan.md)：最小 kernel 保持；语言库提供真实循环的短路／私有初始化／frame／signed increment，domain 精确对应旧 row condition，并复用 reached-write／coverage／观察保持。七模块／34 端点审计通过，旧 dependent compiler 42 项回归和两套冻结 native 绑定复核通过。不是新的 compiler／native 能力，也未声称 guard 成本已解决。

当前计划据此将逐行实际 lowering 标为已证明，把 outer prefix、resource producer、factory／host 安装和提取／成本验收保留为明确的下一交付；一般深层域、合法 pointer-store body、distinct-base physical alias 和同例已有工作／作者负担比较仍未完成。只有实际实例暴露当前证书接口无法表达的语义义务时才调整 kernel。

按评审的 evidence-to-claim 要求，原 29 个局部端点与本次 compiler／native 报告各自保留。两个实际域不是 arbitrary polyhedral 覆盖；pointer-cell memory 反例不是 defined C loop，短数组 store probe 不是 guard comparison-order probe。默认 cap 的约 20,700 个 if 明确进入下一优先验收；循环化／符号扫描、一般 domain、合法 pointer stores、P4 和同例 related-work 比较继续 active。

## 最新 Narrative 澄清与实际 Cursor 接入

本轮再次 fetch 并读 `7d94d81`：最小 semantic kernel 仅负责局部 guarded correctness，readonly 前台和 condition processing／prefix／simplification 是核上库，whole-program 安装是语言 host 的定理与具体 site evidence。这是责任边界，没有要求重排源码；main 的 narrative 和 context note 与分支正文一致。责任矩阵进一步明确四张局部证书之后仍需实际语言安装及实例证据，不把 generic lifting hook 说成已经解决 context closure。

[完整循环化阶段](research-checkpoint-2026-10-06-cursor-dependent-compiler.md)按这个分工连接双 cursor 执行、finite resource checker、staged dispatch、原 source package／candidate checker 和 Csem→Asm。43 新端点／537 依赖／976 source 摘要、提取、两个域共 444 次新入口调用通过。21 槽 private pool 解决 guard cursors 与 candidate counters 的真实状态隔离；kernel 和原模型／coverage／候选证书保持。没有用 interface 字段代替 checked-package 的扫描 callbacks。

本次代码规模验收关闭默认 caps 的展开增长：实际完整函数约 13 MB→25 KB，机器函数 72,083／105,857→879／916 字节。18 个**新**机器 guard comparison 探针直接核对点顺序和拒绝后停止；它们与 28 个 store-order 探针分别报告。旧 dependent 两套矩阵仅绑定复核，不累计旧运行。先前短数组的证据限制保留为其历史范围，不再把它当成本轮 comparison-order 缺口。

计划已吸纳实际进展：下一主任务转为一般 domain／复杂 body、不同 body base 的物理 alias 接受与合法 pointer stores；P4 计时、同版 CompCert 对照和同例 proof obligations 比较仍独立未完成。代码大小不证明性能或 total proof burden，也没有单凭小 kernel、C 层或端点数主张 novelty。


## Narrative cutoff 的深层 affine 接入检验

本次 fetch 后 topdown 仍为 `7d94d810685a691efbf07df734f5fad8abfb4724`，paper narrative／context note 与 main 无差异。按最新 cutoff 实现 [normal-returning materialized check](clight-materialized-check.md)：变化来自具体 Clight check 的返回形式，新增的是语言 host／certificate／状态运输服务；kernel 未改。旧 deep 源对应和 candidate-local 被直接消费，原 stateful region theorem 没有充作新的 local correctness。

后继 [loaded deep numeric guard](research-checkpoint-2026-10-06-loaded-affine-numeric.md)已实际实现 source-derived first-path producer：原源 header／first body 许可 private capture 和参数读取，不假设完整缓存源完成或未来稳定性。语言的 capture／执行运输、domain 的递归 header／leaf 接入及原 numeric/profile 证书、核上 certificate 库分开记录；kernel 未改。25 个端点审计和实际零次 Clight 检查 fixture 通过，旧两条 compiler 的 42 项假设及当前对象绑定保持。这里接受只证明 numeric math domain，下一困难仍是按原源前缀生产递归 physical scan 的许可／coverage，再接观察保持、候选和 whole-program host；没有新增 compiler/native 或新颖性／性能结论。

[阶段证据](research-checkpoint-2026-10-06-materialized-affine.md)给出 26 端点、Csem→Asm／提取、十二配置 5,118 次新 assembly 调用和四组另记的 Clight 插桩。它纠正计划中两个过宽“未支持”表述：递归 affine IR 已存在，多指针 physical scan 也能接受分离 views；当前任务是迁移到现行证书并与 loaded/dependent 路线组合，不能称重新包装创建了一般算法。共享 `.vo` 重编令旧对象摘要绑定失配，独立当前 cursor regression 与历史 native 分开；不将旧 validator 的失败抹掉。计时、总作者负担、新颖性与一般 polyhedral 覆盖均无新增结论，完整 goal active。

## 完整 body 的前缀与缓存运输：后继责任落实

再次 fetch `topdown/research-positioning` 后仍为 `7d94d81`，正文与 main 一致。按其责任边界完成的 [body prefix 阶段](research-checkpoint-2026-10-06-loaded-affine-body.md)没有修改 kernel：语言从真实结构化执行取得权限运输和 temp frame，prefix library 组合 domain 的 body check，语言从接受后的观察保持导出完整缓存源执行。递归 affine adapter 复用 checked package 并核对 pointer register freshness。

34 端点／665 依赖审计通过，numeric 和两个当前 compiler 的对象绑定保持；具体 allocation 下的 alias 源、首次 guard 拒绝、实际 lowering 与观察不保持均有证明。下一项仍须实际实现 recursive physical body probe 的访问许可、覆盖和接受后字节分离，不能把 `BODY_CHECK` 参数或缓存运输桥算成该 domain 算法已经完成。完整 body receipt 可许可其内部全部稳定-temp child points；跨 loaded root header 的推进必须等待 body 观察保持。这一粒度已吸收到计划；新增 compiler、提取、native／性能结果仍未交付。
