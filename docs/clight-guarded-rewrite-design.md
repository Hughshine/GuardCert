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

[ClightPreloadExample.v](../prototype/interface/ClightPreloadExample.v) 实现一个实际内存读取例子：先测试计数，仅在非零路径上读取指针中的整数。域要求计数有整数值；活动路径还要求实际 `Mem.loadv` 返回整数。计数为零时，指针可以完全没有定义。已证明检查安全、拒绝路径不需要指针，以及接受前提下的实际分支删除等价。[ClightPreloadSynthesis.v](../prototype/interface/ClightPreloadSynthesis.v) 将该原子接入 Boolean 公式合成，证明单原子生成的检查正是上述延迟树，并证明空路径在取否定后仍拒绝。

`preload_domain_from_source_execution` 已从这个源模板的实际终止执行导出域，供后述编译器实例消费。它不是任意循环入口的放置证明；不同源循环须提供自己的执行对应／进展证书。

[ClightAdministrative.v](../prototype/interface/ClightAdministrative.v) 处理 C 前端插入的空 sequence。它证明 skip 规范化保持实际终止执行的 trace、outcome、temps 和 memory。识别器对规范化后的完整语法作比较，再将证书运输回实际源片段；没有把打印时看起来相同当成语法相等。

## 局部 effect 与公共出口

[RegionLocalization.v](../prototype/interface/RegionLocalization.v) 允许关系式出口重建。局部结果可对应多个仅私有 temps 或内存表示不同的原始出口；源与候选使用相同 view 和重建关系。两个证书分别绑定实际片段，不能只给两个脱离程序的抽象操作序列。

[ClightRegionBoundary.v](../prototype/interface/ClightRegionBoundary.v) 声明 inputs、stable inputs、live-out、普通写入、私有 temps 和入口相关的字节写集。`clight_write_frame` 绑定实际语句，要求结构化 temps 写界、私有标识隔离、写集外 `Mem.unchanged_on` 及分配中性。已有引理连接实际 store、写集外 load 和连续 frame。

它不是完整读 effect 分析。实际 load／store 的访问覆盖须由语言到局部模型的桥接证明；`statement_scope` 只约束 temps。字节写集是 ghost 信息，不能用于生成凭空的运行时权限检查。

公共观察保留 trace、控制 outcome、live-out temps 及 CompCert 内存等价。`readonly_clight_runs` 对这条关系取观察饱和，避免要求私有 temps 完全相同。内存等价不是仅写集内相等，仍须保证 continuation 可以读取片段外内存。宿主必须证明选定观察关系在实际 continuation 中可运输。

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

### 已接入的 2×2 实例

[ClightReadonlyMatrix.v](../prototype/interface/ClightReadonlyMatrix.v) 是上述协议的首个实际循环实例：使用者识别并核对完整源语法，提交按列执行的候选、`i=0 ∧ n=2 ∧ m=2` 的只读条件和局部等价。实际源执行被解码为四个 CompCert store，已核对的调度证书交换动作，候选执行再编码回相同内存及全部出口 temps。它不是一个脱离源程序的 schedule 示例。

这里复用了旧循环证明的单向执行运输，但没有把它直接当作等价。[DeterministicLocalReasoning.v](../prototype/interface/DeterministicLocalReasoning.v) 要求源完成、源到候选运输和候选观察唯一。[ClightQuietDeterminacy.v](../prototype/interface/ClightQuietDeterminacy.v) 证明实际结构化无调用片段（包括循环）的终止执行结果唯一。[ClightLoopBridge.v](../prototype/interface/ClightLoopBridge.v) 将两者接到 `conditional_equivalence`。源完成性是 ghost 证书，由实际源执行及宿主进展导出；运行时不能查询它，也不能用它跳过源可能发散的全程序证明义务。

`compile_readonly_matrix_correct` 将这个规则接到完整 Csem→Asm backward simulation。当前仍限于 2×2 的一个已核对 store 模板；一般 alias 检查、动态矩形、稳定内存边界与私有出口投影不由此实例得到。

## 与已有 CompCert 路线的连接边界

新增 [ClightReadonlyCompiler.v](../prototype/interface/ClightReadonlyCompiler.v) 提供 `readonly_clight_rule source`，绑定候选、合成条件、域／前提、只读证书、局部等价与源入口证明。使用者提供 `choose` 以及源进展分类证书；编译工具消费这些证书并复用既有区域宿主。`compile_readonly_rewrites_correct` 已证明完整 Csem→Asm 的 backward simulation。

[ClightPreloadCompiler.v](../prototype/interface/ClightPreloadCompiler.v) 是一个实际使用者：提交上述延迟读取与分支删除案例，检查源的完整语法，运输前端空语句规范化证书，实例化现有进展分类器。它有具体的 `compile_preload_rewrites_correct`。这个首个全程序连接要求完整内存及所有出口 temps 相同，尚未消费 live-out／私有 temps 的投影模式。

已有 affine-nest 编译器另具备真实源执行、运行时检查、调度核对和完整 C→Asm 定理，证据见 [多面体接入目标](polcert-integration-target.md)。其条件运行会写私有 temps，局部候选主要提供源到目标的执行运输。它尚未迁移到本页的只读等价接口。

`AffineNestMultiCandidateLocal` 可以提供源到候选的一个方向及 live temps／内存出口；还需证明投影观察下的反向对应。`AffineNestMemoryProjection` 可以提供实际源动作来源；还需接新模型的精确对应。既有 `ClightRegionProgress` 的协议已被新分支及 2×2 循环案例复用；投影出口及更一般动态前提下的有界进展仍需接入。这两个案例不能代表一般多面体功能已经迁移。

当前 `exec_stmt` 宿主只覆盖终止片段。完整 Clight 行为必须考虑源可能发散而 guard 拒绝的路径，不能将有限结果的双向对应代替进展。CompCert C→Asm 的端点维持其仿真方向，不升级为跨语言的任意行为双向等价。

## 多次替换与验证

[RewriteComposition.v](../prototype/interface/RewriteComposition.v) 的每一步绑定真实中间程序、上下文和替换。单步程序等价按传递性组成有限序列等价。一次替换可能改变下一次的入口不变量或布局，因此后续步骤重新提交相应证书。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-clight-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-compiler-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-matrix-native
```

纯接口检查编译十个模块和三个既有依赖，审计 38 个闭合接口端点。Clight 检查编译八个新模块及四个既有依赖，审计 45 个端点，假设包含在既有 Clight 六项全局假设中。编译器检查另审计十二个端点，按片段、内存、区域与完整编译器分别比较基线；实际 store 重排的内存相等还复用 CompCert `Mem.mkmem_ext` 的 `proof_irrelevance`，完整编译器基线为 35 项。没有新增公理。报告记录源码摘要并核对旧编译器的依赖源码清单。

当前原生结果为 68 组调用通过，含四组空路径 null 指针；Clight 中确实出现检查、候选与源回退，结果与 GCC 参考及整数期望一致，输出 `172 0`。这是分支实例的运行证据，不是循环优化或性能验收。

循环原生目标提取 `ClightReadonlyMatrix.compile_readonly_matrix`，运行已有 C fixture：21 次函数调用、九组矩形输入和五处被改写的循环区域通过。输出 Clight 核对实际候选／回退的相反循环顺序；结果与 GCC 及独立期望一致，包括 goto／外围循环上下文、全局数组、全部出口变量和未读取的未初始化内层边界。不同 RHS、真实内存依赖和 volatile 模板均未被改写。报告位于 `build/interface-matrix-native/`；没有性能测量。
