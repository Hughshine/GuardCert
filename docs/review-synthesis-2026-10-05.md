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
