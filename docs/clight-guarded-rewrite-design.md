# 只读 guarded rewrite：语言接入与循环实例设计

2026-10-05。主契约是 [guarded-rewrite-contract.md](guarded-rewrite-contract.md)。本文固定语言实例、循环使用者和框架之间的责任，记录已编译的接口及仍需实现的连接。当前新接口没有取代旧编译器入口。

## 使用者提交什么

一次替换绑定 `source`、`candidate`、`condition` 和实际上下文。使用者自己的 pass 找到片段并生成这些对象。框架构造 `if condition then candidate else source`，不承担片段识别或候选搜索。

| 提交项 | 使用者证明 | 框架提供 |
| --- | --- | --- |
| 语言实例 `H` | 实际执行与条件分派的精确对应；检查安全语义 | 不解释机器整数、地址或语言语法的 `guard_host` |
| 入口域 `D` | 合法插入点在每次到达时满足 `D` | 放置证书与上下文接口 |
| 前提 `P`、检查 `g` | `D` 下检查安全、可完成、只读，接受蕴含 `P` | `readonly_condition`；Boolean 公式合成与原子检查协议 |
| 局部模型 | 两个实际片段的执行均与模型对应 | 相同入口 view／出口重建关系上的局部提升 |
| 局部改写 | `D ∧ P` 下源与候选的观察等价 | 交换链、调度等价和 guarded rewrite 等价定理 |
| 出口与上下文 | 活跃值、内存、控制出口与 continuation 兼容；目标进展 | 满足宿主契约后的程序等价组合 |

`D` 不能预先包含只有 guard 接受后才成立的 `P`。某条数学前提不能因为 checker 能检查它就自动成为合法的运行时操作。例如，证明中可查询 CompCert 的 block；Clight 程序没有这一操作。

## 前提如何成为入口条件

[AssumptionDerivation.v](../prototype/interface/AssumptionDerivation.v) 给每个实际求值位置登记 `site_occurs(parameters, point)` 与 `site_holds(parameters, point)`。位置包括初始化、循环头、退出前增量、地址计算和必要的 preload，不局限于优化后的循环体实例。

`collected_obligations` 要求所有登记且发生的位置满足要求。`projected_violation` 表示存在一个实际位置违反要求。`projection_complement_exact` 证明前者等价于不存在后者。这个定义不提供一般量词消去算法。

一个 `entry_derivation` 将入口参数上的条件连接到全部要求。求解器可以提出消去变量或简化后的条件，但必须提供可靠性证书。`strengthen_entry_condition` 允许更保守的条件；框架不要求接受所有合法输入，也不声称得到最弱条件。`derived_guarded_rewrite_equivalent` 将该证书、实际检查和片段证明连接起来。

[EntryProjectionExamples.v](../prototype/interface/EntryProjectionExamples.v) 已证明矩形地址的端点界足以覆盖全部实例，以及 minor dimension 界内时 row-major 地址的单射性。它还给出两个机械化反例：空循环体仍可能执行溢出的初始化表达式；未检查的机器加法可使 guard 错误接受。这些是数学证书示例，不是已生成的 Clight 地址检查。

## Clight 检查的实际语义

[ClightReadonlyRewrite.v](../prototype/interface/ClightReadonlyRewrite.v) 实例化 `guard_host`：片段是实际 `statement`，检查是有限的 `decision_tree`，降低为 `Sifthenelse`。`readonly_tree_execution_exact` 双向分解实际 `exec_stmt`；检查不改 temps／memory，也不产生事件。

`readonly_tree_safe` 要求每个可能到达的测试都有定义，并对所有可能的结果继续证明后续安全。有限树消除了检查自身的循环。`compiled_tree_safe` 和 `synthesized_readonly_condition` 将原子 validity／value 证明提升到合成检查。原子 value 测试只在 validity 成功后执行；unknown 直接回退，否定不会将 unknown 变成接受。

[阶段检查接口](condition-stage-interface.md) 还允许后一个原子的安全域使用先前建立的事实。语言无关 `sequence_readonly_conditions` 及有限列表合成只依赖检查代数；Clight 提供实际树 bind 的安全／分派定律。内存上界规则已将 `i==0` 证书与依赖该事实的活动路径／alias 证书组合，生成 guard 与原来相同。

[分支／前缀扫描接口](readonly-prefix-scan-interface.md) 增加两个结果各自的证据，以及活动前缀结束后的提前接受。indexed 内存上界规则消费通用扫描：当前 store 提供比较权限，non-alias 后才运输 bound load 与剩余真实源执行到下一点；所有实际测试仍使用同一入口。合成树与既有手写树相等，局部 rewrite 和宿主契约保持相同。

[ClightPreloadExample.v](../prototype/interface/ClightPreloadExample.v) 实现一个实际内存读取例子：先测试计数，仅在非零路径上读取指针中的整数。域要求计数有整数值；活动路径还要求实际 `Mem.loadv` 返回整数。计数为零时，指针可以完全没有定义。已证明检查安全、拒绝路径不需要指针，以及接受前提下的实际分支删除等价。[ClightPreloadSynthesis.v](../prototype/interface/ClightPreloadSynthesis.v) 将该原子接入 Boolean 公式合成，证明单原子生成的检查正是上述延迟树，并证明空路径在取否定后仍拒绝。

`preload_domain_from_source_execution` 已从这个源模板的实际终止执行导出域，供后述编译器实例消费。它不是任意循环入口的放置证明；不同源循环须提供自己的执行对应／进展证书。

[ClightAdministrative.v](../prototype/interface/ClightAdministrative.v) 处理 C 前端插入的空 sequence。它证明 skip 规范化保持实际终止执行的 trace、outcome、temps 和 memory。识别器对规范化后的完整语法作比较，再将证书运输回实际源片段；没有把打印时看起来相同当成语法相等。

## 局部 effect 与公共出口

[RegionLocalization.v](../prototype/interface/RegionLocalization.v) 允许关系式出口重建。局部结果可对应多个仅私有 temps 或内存表示不同的原始出口；源与候选使用相同 view 和重建关系。两个证书分别绑定实际片段，不能只给两个脱离程序的抽象操作序列。

[ClightRegionBoundary.v](../prototype/interface/ClightRegionBoundary.v) 声明 inputs、stable inputs、live-out、普通写入、私有 temps 和入口相关的字节写集。`clight_write_frame` 绑定实际语句，要求结构化 temps 写界、私有标识隔离、写集外 `Mem.unchanged_on` 及分配中性。已有引理连接实际 store、写集外 load 和连续 frame。

它不是完整读 effect 分析。实际 load／store 的访问覆盖须由语言到局部模型的桥接证明；`statement_scope` 只约束 temps。字节写集是 ghost 信息，不能用于生成凭空的运行时权限检查。

公共观察保留 trace、控制 outcome、live-out temps 及 CompCert 内存等价。`readonly_clight_runs` 对这条关系取观察饱和，避免要求私有 temps 完全相同。内存等价不是仅写集内相等，仍须保证 continuation 可以读取片段外内存。宿主必须证明选定观察关系在实际 continuation 中可运输。

[ClightPrivateCandidateExample.v](../prototype/interface/ClightPrivateCandidateExample.v) 是实际执行的局部例子：源为 `public=5`，候选为 `private=99; public=5`。只要求 `private` 不在 live-out 中，便证明两者的 trace、outcome、内存和公开出口一致；另有定理证明两个原始临时变量环境确实不同。私有值可任意变化，饱和观察不唯一，因而不能套用“公开观察唯一”。新增 `saturated_forward_bridge_equivalent` 要求原始候选结果确定、源有完成执行，并证明源／候选的观察集合可运输；`quiet_observed_forward_loop_equivalent` 在真实 Clight 中用观察关系的对称性和传递性建立这一连接。这个文件只证明局部等价；下述投影编译接口另接声明新函数 temps、freshness 和实际 continuation 的全局连接。它不允许 guard 写私有变量：当前 guard 仍须保持完整入口。

## 循环使用者如何接入

目标实例是二维数组复制／更新的循环交换，源按行访问，候选按列访问。使用者提供实际两个 Clight 片段和调度证书。局部动作保留真实地址、chunk、读取来源和机器数据运算；不能把数据加法替换成无界整数加法。控制与地址运算的非回绕前提单独登记。

证明按下列连接展开：

1. 在源语法中登记求值位置，证明源执行对应源有序的实例和真实内存动作。空路径、内层边界求值和退出增量也在对应中。
2. 从实例域推导控制／地址的入口范围条件；记录每个被快照读取的参数地址。
3. 用实际字节区间分离证明交换独立性。不同指针值不蕴含区间分离；同一 block 的不重叠切片应允许接受。
4. 证明稳定参数读取在执行前缀中保持，进而证明动作地址与入口模型一致。循环界来自内存时，不能未经证明就假定其不变，再用这项假定证明不变。
5. 用候选实例对应和合法交换链证明局部结果等价。实例双射保留重复执行的次数；可交换性只要求真正被调度反转的动作对。
6. 证明最终公共循环变量、内存及 outcome。私有迭代器有 freshness 证书；有活跃源迭代器时明确恢复值。
7. 将只读 guard、片段等价、放置和进展证明交给 Clight 宿主，再接 CompCert 的编译仿真。

候选恢复公共值的代码也属于被证明的候选。旧路线中的 control shadow replay 不能因其成本大而在新接口中省略证明。

### non-alias 动作与实际 frame

[ClightReadonlyCellSwap.v](../prototype/interface/ClightReadonlyCellSwap.v) 提交 `*p=c1; *q=c2` 和交换后的两个实际 Clight store。检查只比较指针；合法性、四字节对齐及访问不回绕从源的两个实际 `Mem.storev Mint32` 导出。域内指针不同才蕴含两个四字节区间分离；这个推导不能用于任意宽度或不对齐访问。不同 block 和同一 block 中不同的对齐单元都可接受，指针相同则回退。

这个原子在域内同时证明接受和拒绝的含义，因此 `Complement(Fact tt)` 在已知指针相等时可以接受。它与只有正向证据的保守原子，以及读取没有活动时返回 unknown 的 preload 原子不同；unknown 仍不会因否定变成接受。合成代码不查询 block 标识、权限或 ghost 足迹。

[ClightCellFrame.v](../prototype/interface/ClightCellFrame.v) 给出实际 `clight_write_frame` 实例：两个指针 temps 保持；只写入口指针所确定的两段字节；写集外内存和 `nextblock` 保持；任意声明的 live-out 不需要私有标识。它证明的是指针参数稳定，不是这些指针所指内容不变。编译器仍使用完整出口相等连接全局证明；这个 frame 也可供后续局部动作／循环证明复用。

`compile_readonly_cell_pairs_correct` 已连接 Csem→Asm。局部证书可应用于循环体内的有限片段，无须整个外围循环有完成性证明：Clight 宿主递归匹配上下文，仅被替换区域需要相应进展证书。实际插入还核对目标不引入 label；不合适的位置保留源。对选中的整个可能发散的循环进行改写，仍是另一项尚未实现的能力。

### 已接入的 2×2 实例

[ClightReadonlyMatrix.v](../prototype/interface/ClightReadonlyMatrix.v) 是上述协议的首个实际循环实例：使用者识别并核对完整源语法，提交按列执行的候选、`i=0 ∧ n=2 ∧ m=2` 的只读条件和局部等价。实际源执行被解码为四个 CompCert store，已核对的调度证书交换动作，候选执行再编码回相同内存及全部出口 temps。它不是一个脱离源程序的 schedule 示例。

这里复用了旧循环证明的单向执行运输，但没有把它直接当作等价。[DeterministicLocalReasoning.v](../prototype/interface/DeterministicLocalReasoning.v) 的精确出口版本要求源完成、源到候选运输和候选观察唯一；关系式观察版本要求原始结果确定及观察集合运输。[ClightQuietDeterminacy.v](../prototype/interface/ClightQuietDeterminacy.v) 证明实际结构化无调用片段（包括循环）的终止执行结果唯一。[ClightLoopBridge.v](../prototype/interface/ClightLoopBridge.v) 将两者接到 `conditional_equivalence`。源完成性是 ghost 证书，由实际源执行及宿主进展导出；运行时不能查询它，也不能用它跳过源可能发散的全程序证明义务。

`compile_readonly_matrix_correct` 将这个规则接到完整 Csem→Asm backward simulation。当前仍限于 2×2 的一个已核对 store 模板；一般 alias 检查、动态矩形、稳定内存边界与私有出口投影不由此实例得到。

### 动态矩形实例

[ClightReadonlyRectangle.v](../prototype/interface/ClightReadonlyRectangle.v) 将相同接口推广到运行时 `n`、`m`。使用者的识别器从实际数组类型、下标和 RHS 中提出布局；证书重新核对完整语法及变量隔离。例如 `a[120]`、下标 `i*10+j` 的检查为 `i=0 ∧ 0<n≤12 ∧ 0<m≤10`；`a[105]`、行宽 7 的上界为 15 和 7。候选按列执行相同 store，回退保持源。循环次数不由编译器枚举；范围条件是保守的，可能拒绝仍有定义的源输入。

[ClightReadonlyTreeSynthesis.v](../prototype/interface/ClightReadonlyTreeSynthesis.v) 支持原子检查本身是一棵短路树的 Boolean 公式合成，并补足所有可达测试的安全性证明。这个实例消费合成树和 `conditional_equivalence`，接到 `compile_readonly_rectangle_correct`。这个入口只改写普通 store 模板；下述组合入口另接入 read-modify-write 和行内依赖。参数 stride 的纯写模板随后通过下述实例接通，动态循环 alias 检查仍未迁移。

[ClightRectangleAssumptions.v](../prototype/interface/ClightRectangleAssumptions.v) 登记八类模型文本位置：外层头／增量、内层 reset／头／增量、下标乘法／加法及字节偏移。入口范围证书推出全部发生位置的要求；实际 guard 接受也推出该集合。另有活动域地址单射性，以及 `Int.mul`、`Int.add`、`Ptrofs.repr` 与数学地址相同的证明。实际语法绑定与执行实例覆盖由 rectangle certificate 及既有 decoder 承担；这不是任意 C 的求值位置分析器。数据 RHS 仍使用机器整数语义，不要求它不回绕。

### 读写更新与行内依赖

[ClightReadonlyLoopUpdates.v](../prototype/interface/ClightReadonlyLoopUpdates.v) 提供两个新的规则作者实例，与纯 store 共用动态范围条件。第一类是 `a[i*S+j] += value(i,j)`：局部动作包含真实 load、机器整数运算和 store，交换由分离单元的读写独立性支持。第二类是 `a[i*S+j] = a[i*S] + value(i,j)`：同一行里的读取依赖被保留，候选虽把 `j` 移到外层，仍保持每一行的 `j` 顺序；跨行独立性支持实际被反转的动作对。错误的邻居读取和对角线依赖不被该实例接受。

每个规则重新核对完整源 AST、读取来源、地址、类型和循环协议，并消费相应的实际源解码／内存动作调度／候选编码定理，保持完整内存及全部出口 temps。组合选择器是使用者 pass，依次尝试纯 store、原地更新和行内读取模板；`compile_readonly_rectangles_correct` 证明这个入口的完整 Csem→Asm backward simulation。它不能据此声称支持任意读写 body 或依赖关系。

### 规则作者可复用的循环构造器

[ClightReadonlyLoopRule.v](../prototype/interface/ClightReadonlyLoopRule.v) 暴露 `readonly_forward_loop_rule`。使用者提交实际源与候选、只读 guard、基础域 `D`／前提 `P`，以及五项证明：源和候选的 quiet 语法证书；`D` 下的检查证书；`D ∧ P` 下保留原始出口的源到候选执行运输；实际源正常执行蕴含 `D`。quiet 仅表示没有调用、goto、label 等，不意味着循环必定结束。

构造器将 `D` 加上显式 ghost 源完成性，由实际源执行获得该证书，再用候选确定性建立反方向，返回 `readonly_clight_rule source`。使用者仍提供片段选择和进展分类器；框架不能凭一个数学调度替代实际执行证明，也不能让运行时查询 ghost 完成性。上面的 update／行依赖规则使用这个构造器。这条全局路线仍要求原始出口相同；隐藏私有出口的局部构造器通过下述投影编译接口另行接入。

### 带 non-alias guard 的稳定 load 提升

[稳定 load 使用者案例](clight-stable-load-case.md) 提交源 `*out=*parameter+(unsigned)i+1U` 的计数循环、私有快照候选以及 `i=0`／源活动／non-alias 条件。检查代码不读取参数内容；它先确认源活动路径，再比较指针。第一次候选 preload 的安全性由实际源第一次读取导出，参数在每次写入后的不变性由分离的 Mint32 访问证明。参数只需可读，数据 unsigned 回绕保留；数组足迹与内存载入的循环界不能由此实例得到。

[ClightCountedLocalization.v](../prototype/interface/ClightCountedLocalization.v) 提供实际计数循环与逐次实际 body 的双向对应；次数不由编译器枚举。[ClightReadonlyProjectedLoopRule.v](../prototype/interface/ClightReadonlyProjectedLoopRule.v) 为规则作者连接只读条件、源完成、候选原始确定性和公开观察运输。[ClightStableLoadCompiler.v](../prototype/interface/ClightStableLoadCompiler.v) 核对完整源 AST，消费这些证书和新鲜 snapshot temp，通过 `compile_stable_loads_correct` 接完整 Csem→Asm。它是已经使用投影全局接口的真实循环案例。


### 内存中的循环上界与检查树读取

[ClightLoadedBoundCompiler.v](../prototype/interface/ClightLoadedBoundCompiler.v) 核对实际 `i<*bound`、`++i` 与 `*out=i+1`，接受活动且对齐单元 non-alias 的输入后，将循环头读取提升到私有 temp。实际 source header 提供上界 load 的定义性，第一次实际 store 提供输出访问依据；每次 body 的真实 store 再建立读取不变性。源码依赖入口域、guard 接受与稳定性保持各有证明，不能将稳定性放进入口域。

[ClightStrictLoopProgress.v](../prototype/interface/ClightStrictLoopProgress.v) 允许源上界随内存改变：测试接受须蕴含 signed counter 小于机器最大值，有限 body 只写内存。它用最大值到计数器的距离建立源进展，不消费 non-alias。[ClightStableLoopCondition.v](../prototype/interface/ClightStableLoopCondition.v) 则在单独给出的不变式下，逐个实际 body／增量运输循环头，形成候选 `exec_stmt`。

[ClightReadonlyLoadedTreeSynthesis.v](../prototype/interface/ClightReadonlyLoadedTreeSynthesis.v) 补上带 load 的 tree-valued 原子：validity／value 证书须给出入口域下的完成检查，实际表达式确定性将完成路径提升成所有可达节点安全，随后复用 Boolean 合成核。它不将负面结果或 unknown 自动视为可靠否定，也没有允许 guard 写私有 scratch。`make interface-loaded-bound-native` 的 514 次调用／514 行输出与 GCC 和独立模型一致，四处实际改写已确认，八组原生回归通过。完整使用者职责及反例见 [内存上界实例](clight-loaded-bound-case.md)。


### 在同一个使用者 pass 中组合规则

[ClightReadonlyRuleEmbedding.v](../prototype/interface/ClightReadonlyRuleEmbedding.v) 将已有精确出口规则提升到任意观察关系；使用者只需补充源 temps 写界。`exact_projected_replacement` 证明 guard／候选／回退代码没有改变。[ClightCommonRewriteCompiler.v](../prototype/interface/ClightCommonRewriteCompiler.v) 是组合选择器，将上述循环及标量规则放进同一 projected host，保留每次实际到达时的 guard 检查。

`make interface-common-native` 的同一函数包含多个被选择片段，576 次调用／2880 行输出与 GCC 和独立模型一致。分别确认四种交换的实际候选、两组 store 交换，以及不同位置使用同一私有 pool 的两次快照。源 payload 在后续覆盖前检查；后来分支读取先前写入后的参数值。十三组原生回归通过。源码写界的自动核对仍是 temps 语法过近似，不是内存足迹分析。详见 [组合使用者证明](clight-common-user-pass.md)。

## 与已有 CompCert 路线的连接边界

新增 [ClightReadonlyCompiler.v](../prototype/interface/ClightReadonlyCompiler.v) 提供 `readonly_clight_rule source`，绑定候选、合成条件、域／前提、只读证书、局部等价与源入口证明。使用者提供 `choose` 以及源进展分类证书；编译工具消费这些证书并复用既有区域宿主。`compile_readonly_rewrites_correct` 已证明完整 Csem→Asm 的 backward simulation。

[ClightPreloadCompiler.v](../prototype/interface/ClightPreloadCompiler.v) 是一个实际使用者：提交上述延迟读取与分支删除案例，检查源的完整语法，运输前端空语句规范化证书，实例化现有进展分类器。它有具体的 `compile_preload_rewrites_correct`。这个首个全程序连接要求完整内存及所有出口 temps 相同，尚未消费 live-out／私有 temps 的投影模式。

[ClightReadonlyProjectedCompiler.v](../prototype/interface/ClightReadonlyProjectedCompiler.v) 另暴露 `readonly_projected_clight_rule live source`。它增加源语句 temps 写界，局部等价使用边界观察；其余仍是候选、只读 guard、域／前提及实际源入口证明。`projected_readonly_rule_region_contract` 首先把源执行运输到与所有原程序 temps 一致的目标入口，再从 guarded 等价获得候选／回退执行，最后将公开出口交给既有 `PrivateRegion` 宿主。域在运输后的实际入口证明，不把私有入口相同作为隐含假设。

这个宿主使用 `program_temps` 收集所有原标识，构造并检查新鲜 pool，将其追加到目标函数 `fn_temps`，证明函数入口、外围语句、循环、goto、调用和 continuation 的运输。这里的 `live` 是所有原程序 temps 的保守集合，不是自动 liveness 分析的最小集合；当前不能据此隐藏原程序中已存在但被认为 dead 的 temp。公共观察仍保留完整内存的双向 `Mem.extends`、trace 和控制 outcome。原子 observer 的空写集声明也不是一个 frame 证书。

`transform_projected_readonly_correct` 给出完整 Clight `semantics2` 的 forward simulation；`compile_projected_readonly_correct` 接到 Csem→Asm backward simulation。没有声称完整 Clight 双向行为等价。[ClightPrivateCandidateCompiler.v](../prototype/interface/ClightPrivateCandidateCompiler.v) 是实际使用者：核对 `public=5`，候选先写新鲜 `private=99` 再执行原赋值，guard 是 `Decision true`。这是上下文与私有状态能力测试，没有性能收益主张；普通参数快照随后通过下述 load 提升实例接入；内存上界随后也使用这个投影宿主；一般私有迭代器及 affine 实例仍需各自的局部证明。

已有 affine-nest 编译器另具备真实源执行、运行时检查、调度核对和完整 C→Asm 定理，证据见 [多面体接入目标](polcert-integration-target.md)。其条件运行会写私有 temps，局部候选主要提供源到目标的执行运输。它尚未迁移到本页的只读等价接口。

`AffineNestMultiCandidateLocal` 可以提供源到候选的一个方向及 live temps／内存出口；可复用新的原始结果确定性／观察运输桥，但仍需在这个旧实例中核对源完成性、候选 quiet 性和反向观察对应。`AffineNestMemoryProjection` 可以提供实际源动作来源；还需接新模型的精确对应。既有 `ClightRegionProgress` 的协议已被新分支及 2×2 循环案例复用；投影出口已通过下面的私有候选案例接入；更一般动态前提下的有界进展及旧 affine 实例迁移仍需完成。这这些实例不能代表一般多面体功能已经迁移。

当前 `exec_stmt` 宿主只覆盖终止片段。完整 Clight 行为必须考虑源可能发散而 guard 拒绝的路径，不能将有限结果的双向对应代替进展。CompCert C→Asm 的端点维持其仿真方向，不升级为跨语言的任意行为双向等价。

## 多次替换与验证

[源前缀安全的 indexed 内存上界](clight-indexed-bound-case.md) 组合上述两类能力。入口读取值不先用作整个数组 footprint 的安全依据；每个实际 source store 给出当前比较的权限，前缀 non-alias 通过后才建立下一个源头部所需的 load 稳定性。只读运行时 tree 使用原入口，ghost source execution 只存在于证明。`strict_active_condition_transport` 分离头部不变式与自增前不变式，并把实际为真的源头部交给 body 证书；这使 alias 前提仅覆盖活动迭代。`positive_readonly_tree_primitives` 将有完成路径证书的含 load 原子接入已有前提公式，拒绝仍是 unknown。

[动态 indexed footprint](clight-indexed-load-case.md) 随后补上有界的数组写足迹消费。源实际 store 逐点给出入口权限，条件只比较活动地址，接受后才证明参数 load 的前缀稳定性；默认 cap=16，超出时回退。它允许同对象非活动参数单元、不同对象和 const 参数，独立入口／统一 pass 均通过 1095 次调用／2188 行逐单元检查。只读树生成 17 个候选出口；这项代码大小成本与最多 16 次地址比较分开记录，尚无共享候选 lowering 或性能测量。

[运行时 stride 使用者案例](clight-runtime-stride-case.md) 使用原始出口接口接入真正的 `i*stride+j` 二维交换。用户提供实际源／候选、完整语法证书和 body 不写 stride 的证明；框架条件树消费已认证的维度原子，生成 signed64 乘积界检查。源执行证明入口读取域，检查自身的乘法精确性另外证明；候选保留 runtime stride。`compile_runtime_strides_correct` 接到完整 Csem→Asm，统一 pass 也消费相同规则。345 次调用／342 行输出、九处实际 guard、未初始化参数的空路径及连续 rewrite 之间的参数修改通过；见 `make interface-runtime-stride-native`。

[RewriteComposition.v](../prototype/interface/RewriteComposition.v) 的每一步绑定真实中间程序、上下文和替换。单步程序等价按传递性组成有限序列等价。一次替换可能改变下一次的入口不变量或布局，因此后续步骤重新提交相应证书。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-clight-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-compiler-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-matrix-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-rectangle-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-cells-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-loops-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-private-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-stable-load-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-loaded-bound-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-common-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-runtime-stride-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-indexed-load-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-indexed-bound-native
```

纯接口检查编译十一个模块和三个既有依赖，审计 43 个闭合接口端点。Clight 检查编译十一个新模块及四个既有依赖，审计 57 个端点，假设包含在既有 Clight 六项全局假设中。编译器检查另审计一百九十九个端点，按片段、内存、区域与完整编译器分别比较基线；实际 store 重排的内存相等还复用 CompCert `Mem.mkmem_ext` 的 `proof_irrelevance`，投影上下文宿主的八项基线另含既有外部函数／内联汇编性质；完整编译器基线仍为 35 项。没有新增公理。报告记录源码摘要并核对旧编译器的依赖源码清单。

当前原生结果为 68 组调用通过，含四组空路径 null 指针；Clight 中确实出现检查、候选与源回退，结果与 GCC 参考及整数期望一致，输出 `172 0`。这是分支实例的运行证据，不是循环优化或性能验收。

循环原生目标提取 `ClightReadonlyMatrix.compile_readonly_matrix`，运行已有 C fixture：21 次函数调用、九组矩形输入和五处被改写的循环区域通过。输出 Clight 核对实际候选／回退的相反循环顺序；结果与 GCC 及独立期望一致，包括 goto／外围循环上下文、全局数组、全部出口变量和未读取的未初始化内层边界。不同 RHS、真实内存依赖和 volatile 模板均未被改写。报告位于 `build/interface-matrix-native/`；没有性能测量。

动态矩形目标提取 `ClightReadonlyRectangle.compile_readonly_rectangle`：225 个正尺寸 store 矩形、六处改写区域及实际短路范围检查通过；C fixture 的 842 行结果逐单元、逐出口与 GCC 和独立模型一致。空域和布局外输入回退，内层未初始化边界在外层为空时未读取。同一 fixture 中的 update／行依赖案例保持源，不能计入新接口支持的变换种类。报告位于 `build/interface-rectangle-native/`。

non-alias 原生目标提取 `ClightReadonlyCellSwap.compile_readonly_cell_pairs`。82 次 C 函数调用覆盖 20 个相同指针输入、60 个同一 block 的分离单元输入、不同对象和空循环的 null 指针；所有单元及未写 frame 与 GCC／独立期望一致，输出 `4100 0`。普通函数、计数循环和无限外围循环内的三个实际 guard／交换顺序均已核对；无限循环只编译和检查，未执行。报告位于 `build/interface-cells-native/`；这不是一般区间／循环足迹 alias 检查器。

组合循环目标提取 `ClightReadonlyLoopUpdates.compile_readonly_rectangles`：225 个 store、345 个读写更新和 225 个行依赖正矩形，十九处实际改写区域通过；842 行输出逐单元和完整 iterator 出口与 GCC／独立模型一致。每类都有接受、回退、空域、全局数组、goto／外围循环和未读取内层界案例；compound assignment 也确实被改写。邻居读取、对角线依赖、volatile 和无效布局拒绝。报告位于 `build/interface-loops-native/`。这与只处理 store 的独立矩形入口分开记录；没有性能测量。

私有候选目标提取 `ClightPrivateCandidateCompiler.compile_private_candidate`：83 次调用通过，输出 `625 0`。Clight dump 中普通函数、goto 及有限／无限外围循环的四处候选确实声明并写入隐藏 temp，公开赋值与 continuation 结果保持；无限循环只编译和检查。原始出口 temps 不完全相同，该实例实际消费投影接口。报告位于 `build/interface-private-native/`。提取缓存同时绑定证明报告摘要，避免沿用属于旧审计报告的 stamp。

稳定 load 目标提取 `ClightStableLoadCompiler.compile_stable_loads`：727 次调用、727 行输出逐单元／iterator 与 GCC 及独立期望一致。360 个别名矩阵输入、360 个同 block 分离输入、三个空循环 null 调用及四个只读参数调用通过；非零／负起点回退，unsigned 数据回绕保持。普通函数、goto、外围循环和无限外围循环中的四处 guard／快照／候选 body 已确认；无限循环未运行。`i=0,n=2,out=parameter,初值=0` 的反例保留结果 3，省略 guard 的缓存会得到 2。volatile、不同常数和变化的参数指针模板拒绝。报告位于 `build/interface-stable-load-native/`；没有性能测量。


## 固定上界的等式退出与模距离进展

[ClightEqualityCompiler.v](../prototype/interface/ClightEqualityCompiler.v) 接入一个不同的循环控制实例：固定 unsigned `n`、单位 unsigned 自增、头部 `(int)i!=(int)n`，body 满足有限普通内存语句且不改 temps。源 AST／类型／cast／增量／变量隔离均重新核对。只读 guard `i==0U && 0<(int)n` 接受后，候选保留 body 并改成 `<`，实际执行不变式保持完整内存和全部 temps。规则使用现有 `readonly_forward_loop_rule`，完整端点是 Csem→Asm backward simulation。

[ClightCounterProgress.v](../prototype/interface/ClightCounterProgress.v) 提供由计数器事实实例化的源小步协议；本例的 [circular_counter_facts](../prototype/interface/ClightCircularCounter.v) 使用 modulo `2^32` 距离，证明 unsigned 回绕后的自增仍恰减少一。实际 `unsigned_equality_progress` 与分类器消费它，独立于 guard 或 non-overflow。这里没有把检查的前提写进源进展域；body 保持固定上界来自实际 temps 写界。

独立提取入口和统一 pass 各通过 703 次调用、七处实际 guard，包含 unsigned 回绕回退、跨 signed view 边界、null 空路径、RMW 数据回绕和上下文。完整编译接口 164 个端点审计通过，无新增公理。十三种提取配置已重建回归通过，15 份既有源码／Clight 摘要保持相同。统一 pass 已加入该规则及进展分类，其原生验证记录见 [案例](clight-equality-loop-case.md)。本阶段仍不支持选中且可能无限的 step=2／改变目标循环，不满足 §4.3 的全部覆盖。


## 潜在无限外围中的有限头部变换

[ClightReadonlyExpression.v](../prototype/interface/ClightReadonlyExpression.v) 暴露实际表达式／有限分派的共用核宿主；使用者提交完整值的条件性等价、类型、只读检查和每次源求值的入口域。真实小步宿主在具体 skip/break 头部及 assignment／return 位置完成有限检查后运输相同结果和 continuation，不要求整个外围循环终止。其他 if 分支保持结构，检查没有复制任意 label。

[逐步头部实例](clight-stepwise-head-case.md) 在每次当前 `i≤n` 下将 `!=` 改为 `<`，支持改变 bound、步长 2 和 volatile body 外围。独立入口和统一入口各通过 333 次调用／284 行输出、十处实际改写；两个明确无限源也编译并确认实际头部 guard，未运行它们。十四种提取配置在 184 端点审计下回归通过，STEPWISE 使用现有八项基线，没有新增全局公理。统一入口通过 `compile_readonly_tests_after_correct` 组合 projected region pass 与逐步 pass。它不将整个可能无限的循环变成有限 polyhedral 域；[能力分类](host-capabilities.md) 说明两种宿主所需的不同证书。

## 从实际操作数生成只读比较条件

`ClightOrderedInequality.ordered_inequality_rule` 接受实际 `left`／`right` 表达式和 signed32 类型证书，生成 `left≤right`，在本次入口证明 `left!=right` 与 `left<right` 完整 `val` 相同。源比较的实际求值给出两个 word 操作数及定义性；检查及候选在同一只读入口求值。普通 load、计算表达式、常量均由同一模板处理，源 volatile 操作先降为一次 builtin 事件，后续只读其快照。详见 [737 次实际调用的实例](clight-loaded-comparison-case.md)。

该生成器直接返回共用 `readonly_condition`，与 Boolean 原子合成／带依赖的阶段合成可以共存。它不解释任意 `Prop`，也不从局部机器值关系推出数学运算树无溢出。跨迭代稳定性、整个模型域有界及调度仍有各自的证明义务。

## 内存上界与真实二维调度的组合

[2×2 memory-bound 案例](clight-loaded-matrix-case.md)把源 header 的普通 load、只读四 word 检查、私有 bound cache 和真实列优先执行接到同一 projected rule。当前行的实际 store 提供权限；只在前行 non-alias 全部通过后推进 ghost 源 tail，证明下一行安全，而实际条件始终读入口。局部不变式保证 load 稳定，源行序解码及 CompCert store 交换再建立候选执行／完整公共出口。它不是仅打印一个没有消费的 schedule。

`strict_framed_progress` 另允许 body 含其自己的 framed loop 协议，只保护 outer iterator。源最大值 rank 与 guard／load 稳定独立；这项语言设施不改变语义无关核的契约。`compile_loaded_matrices_correct` 与统一入口都连接完整 Csem→Asm。独立／统一入口各通过 668 次调用／673 行输出，当前完整审计 199 端点，十五种提取配置回归通过，21 份既有 source／Clight 摘要相同。接受域仍为 2×2；一般动态内存尺寸／stride、复杂 body 及 affine 迁移继续推进。

## 动态内存行数和列数

`ClightLoadedRectangleCompiler` 将上述组合扩展到动态矩形：当前真实源行给出完整内层 stores，不预设 non-alias；内层 scan 检查活动地址，整行接受后外层 scan 才推进 bound 稳定和真实源 tail。两层均调用通用生成器，生成宿主与实际函数宿主的语法一致性另有证明。候选采用已有 `rectangle_local`，scope／freshness 保护全部原程序 temps 和内存。

独立／统一入口各通过 6,248 次调用／6,253 行输出，242 端点审计和十六种配置回归通过，23 份已有源码／Clight 摘要相同。stride 仍静态；示例 pass 限制树展开预算，实际每处 region 有 156 份候选。完整义务、反例和后续缺口见 [动态矩形使用者](clight-loaded-rectangle-case.md)。

## 共享出口的生成适配层

原 `readonly_projected_clight_rule` 可以交给 `ClightSharedProjectedCompiler`，它另外检查 candidate quiet 和新鲜的 private Boolean slot。实际检查树先保存结果，候选／回退各一份；Boolean 写入后的分支执行由 temp scope 运输，continuation 保护全部原 temps 和完整内存。原条件合成与局部调度证明直接复用。共享矩形入口通过相同 6,248 次调用，251 端点审计和十七种配置回归通过，25 份既有源码／Clight 摘要相同。具体实现／raw 与公开 state 的边界见 [共享出口](shared-guard-lowering.md)。

只读条件的后处理接口已由 [探针简化](readonly-probe-simplification.md)接通：`ClightProbeTree.v` 把实际表达式决策树接到通用部分探针语义，`simplified_projected_rule` 保留原局部证书，仅替换 guard 及检查证书。`ClightSimplifiedRectangleCompiler.v` 再实例化已有共享编译宿主，具备完整 Csem→Asm 端点及实际 6,248 次 C 调用。简化使用语法相同表达式的路径结果，不能自动推广到不同算术表达式或非只读／非确定操作。

[参数 stride／内存上界组合](clight-loaded-stride-case.md)又提供一个模型族使用者：实际源与候选均保留参数地址；条件在源活动路径上获得 stride 定义性后分派到合法布局，局部执行经常量模型运输并复用原前缀证书。布局枚举完备性和整数乘积界／常量除法界对应由语言实例证明。独立共享编译器及统一选择器各通过 68,368 次 C 调用，完整编译审计 279 端点，无新增全局公理。当前仍为小固定数组布局枚举，不提供一般大布局或两个 memory-bound 维度。
