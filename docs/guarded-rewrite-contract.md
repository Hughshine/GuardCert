# Guarded rewrite：使用者契约与循环证明设施

本设计面向提供循环／多面体优化、条件算术 rewrite 和内存 rewrite 的使用者。我们自己的循环实例也遵守相同契约。框架提供带只读检查的片段替换、前提表达与检查库、局部证明设施和上下文组合定理。片段选择、候选产生、搜索策略及完整程序 traversal 由使用者定义。

2026-10-05 的当前主接口是 [GuardedRewrite.v](../prototype/interface/GuardedRewrite.v)。它复用 [GuardInterface.v](../prototype/interface/GuardInterface.v) 的底层分派协议；检查改写私有状态、一般失败协议和其他正确性判断仍属于底层或后续扩展。旧的[语言无关分类](language-independent-interface.md)记录更广的入口协议，不作为当前用户前台的全部义务。

## 1. 一次 rewrite 的定义

使用者提供实际原片段 `S1`、实际候选 `S2`、可执行只读检查 `cond` 和它接受时建立的逻辑前提 `P`。前提 AST 可以由使用者直接提供，也可以由规则模板实例化。检查编译器可从 AST 构造 `cond` 及证书。

```text
guarded_rewrite(S1, S2, cond) = select(cond, S2, S1)
```

`select` 由语言实例实现为入口检查及条件分派。拒绝后执行原片段。框架不定义一个挑选哪些片段的 `Program -> Program` 算法；使用者的 pass 在选定位置调用这个构造器。

`P : State -> Prop` 是语义前提，`cond : Check` 是实际代码，二者不是同一个对象。原片段和候选的命令类型、执行语义及观察也由语言实例给出。证明须绑定实际命令，不能只绑定规则名、访问摘要或期望的循环调度。

## 2. 使用者交付什么

已有语言、性质和宿主库时，一次调用提供以下数据及证书；库函数可以自动构造部分证书。

| 输入／证书 | 它具体说明什么 | 通常如何取得 |
| --- | --- | --- |
| `S1, S2` | 实际源／目标子程序 | 用户的规则、优化器或人工候选 |
| 片段接口 `I` | 输入、live-out、允许的出口、可见内存和事件、私有临时变量 | 支持的片段形态及提取／类型检查器 |
| 合法入口域 `D` | 输入已定义、需要的访问能力、语言及宿主支持条件 | 入口不变量、源执行、类型／effect 分析 |
| 前提 AST 与 `P` | 有限可执行条件怎样足以建立语义义务 | 性质库、规则模板、编码／入口推导证书 |
| `readonly_condition` | 检查安全、可用、只读；所有接受结果建立 `P` | 检查编译器及实际条件实现的证明 |
| `conditional_equivalence` | 在 `D ∧ P` 下 `S2` 与 `S1` 的观察双向对应 | 局部规则、重排 witness 检查器或手写证明 |
| 插入点与目标可安装证书 | 源片段的 effect 已被定位；目标满足相同宿主接口 | 语言宿主及一次实际位置的实例化 |

“普通用户不重证语言”不表示新优化没有证明义务。新增规则要证明其局部定理；新增前提原子要提供含义、实际检查和正确性；新增语言或新片段形态要证明宿主组合。我们实现循环案例时承担这些实例作者的工作。

## 3. 最小的局部定理

设 `Run(S,s,o)` 为实际片段执行，`o` 包含后续程序需要的公开状态、内存及控制出口。当前前台的定理形状是：

```text
ConditionalEq_D,P(S1,S2) :=
  ∀ s,o. D(s) ∧ P(s) ⇒ (Run(S2,s,o) ↔ Run(S1,s,o))
```

这是等价，需要两个执行方向。只有“目标终止时有对应源终止”的端点定理时，还需要另一方向的执行／进展论证；不能把 backward refinement 直接叫等价。当前 `LocalScheduleEquivalence` 在对称独立性及观察运输成立时，实际补足交换链的另一方向。

片段局部模型可以只保留相关变量及内存，但必须再有表示／frame 定理，把它的结果连接到真实语言状态。库可以使用 `ExitEq_I(o1,o2)` 而非整个实现状态相等；将它转换为前台共同观察时，要证明隐藏的临时量不可被上下文读取。仅比较一个结果变量不足以处理写内存的循环。

若声明完整行为等价，`Run` 和宿主必须覆盖发散、错误、异常及事件。当前总函数示例没有这些构造，只证明其明确建模的有限正常执行及函数 continuation；现有 CompCert C→Asm 仿真也不能自动升级为 C 与 Asm 的双向行为等价。

## 4. 如何 localize effect

语言实例的片段接口应包含以下可证明信息：

```text
Inputs(I)                  入口读到的值及其定义性
Reads(I,s), Writes(I,s)     实际读／写位置及必要权限
Exit(I)                    正常出口及 live-out
PublicObservation(I)       可见内存、结果、出口、事件
Private(I)                 新鲜且上下文无法观察的临时状态
```

使用者把源程序定位为 `C[S1]` 时，要建立：每次受支持的进入都满足 `D`；没有绕过检查直接进入候选中部的入口；真实执行的读写被 effect 摘要覆盖；退出满足外围代码的要求。调用、volatile、原子操作和异常若没有对应宿主证明，应由支持范围排除。

局部证明设施应提供具体 frame 规则。例如证明一个写入只改变其声明位置，并保持其他内存、访问能力及参数；然后把若干动作的 frame 组合为整个循环的 frame。循环参数在检查与消费证据之间保持稳定，也要由这些规则或专门不变量证明。

`Writes` 可以依赖输入及迭代索引。动态不别名不是必须分离整个分配对象；只需分离所证明执行真正使用、并且会形成冲突的访问。读／读重叠通常可允许；写／读和写／写重叠需要相应依赖论证。每一项依赖“不别名”的规则仍须证明实际语言中的动作可交换，包括可见事件。

两个局部出口一致，加上相同入口和 frame，才能给外围 continuation 足够的信息。框架不能通过忽略外围会读取的内存来使局部定理成立。

前台的 `localized_conditional_equivalence` 提供可复用的提升。使用者定义 `view(s)`、局部执行 `LocalRun` 和 `restore(s,local_result)`，并分别为实际源／目标证明：

```text
Run(Si,s,o) ↔ ∃ local_result.
  LocalRun(local_Si,view(s),local_result) ∧ o=restore(s,local_result)
```

`restore` 可从原入口保留未写的 frame。两条桥接必须使用相同的 view 和公开观察还原；局部执行在该 view 上双向等价后，框架实际证明真实片段的条件性等价。语言的内存 frame／表示定理承担桥接义务，核心不把它们假设为免费成立。

## 5. condition 的支持范围

第一版固定有限 Boolean AST：

```text
Cond ::= true | false | Atom
       | Cond ∧ Cond | Cond ∨ Cond | ¬Cond
```

原子库负责类型化参数、语言含义和实际求值。`SemanticFacts.property_dimension` 区分 `Some true`、`Some false`、`None`；分别表示有正证据、有负证据、未获得证据。公式内部的 unknown 经否定仍为 unknown，最终保守拒绝。单向充分检查的拒绝应解释为 unknown。

当前 AST 组合在 `AbstractGuard` 中已有机械证明；实际语言的原子和 lowering 必须各自验证。不能从任意 Rocq `Prop` 自动生成 condition。以下是为常见优化固定的性质维度与检查要求，其中跨语言的一般实现仍须由实例提供。

[带依赖的只读检查](condition-stage-interface.md) 另提供顺序阶段组合。使用者分别提交 `D` 上建立 `P` 的检查，以及 `D and P` 上建立 `Q` 的检查；框架生成组合并证明安全、只读、可用及接受 `P and Q`。后一个检查可以使用先前阶段已接受的事实来证明读取或算术有定义。任意有限列表复用 `certified_condition_stages` 与 `synthesize_condition_stages`；具体语言只补充常量检查和检查顺序构造的分派／安全定律。实际 Clight 内存上界规则已使用此设施，局部 rewrite 与全局宿主契约保持相同。

新数学实例实际提供 `DifferentCells` 和 `NoWrapIncrement8` 两个原子，并证明其 Boolean AST 的只读检查。既有 [Presumption.v](../theories/Presumption.v) 还实现了一个受限示例语法：表达式是常量、标量、加、减，原子是大小／相等、该运算树的无溢出、界内和区间分离；其 block／offset／extent 是示例 metadata，不是可直接运行的 CompCert 权限检查。这些实例语法与通用原子扩展机制应明确区分。

| 维度 | 可表达的受限原子 | 运行时／静态依据 | 主要局部用途 |
| --- | --- | --- | --- |
| 整数与控制 | 非零、大小／区间、指定运算树的无溢出、除法／移位定义性 | 安全的宽化／checked 运算、静态界 | 算术 rewrite；循环控制与地址解释 |
| 内存与 alias | 同一位置、带访问宽度的区间分离、有限或仿射访问族的冲突分离 | 语言允许的指针操作、访问族检查、静态依赖证据 | 相同地址 load；写入／循环重排 |
| 访问能力 | 实际读／写的定义性、对齐及权限 | 源执行、静态能力或已建模 metadata | guard 和候选的安全执行 |
| 稳定性 | 参数／被读区域直到消费时不变 | frame、不变量、可信版本协议 | 将入口证据用于整个循环 |
| 布局／身份 | 可读取字段的 shape、stride、函数或实现身份 | 类型化读取及静态证据 | 后续的布局／调用特化案例 |

不存在一枚在任意语言里检查“该指针可读”的通用机器测试。抽象 `Mem` 中的权限也不是可直接读取的运行时变量。原子实现必须给出可执行依据；没有依据则使用已证明的静态事实或拒绝。

无溢出原子绑定位宽、符号、具体运算和输入时点。检查自身不能先执行可能出错的运算再看结果。硬件 flag 只有在实例建模其设置／读取／清除及关联运算后才可使用。“当前没有 overflow flag”不代表整个候选循环不会溢出。

仿射域的 `∀ instance` 或 `∀ conflicting pair` 是语义义务。它们通过区间／依赖证明化简为有限入口原子，或由有终止证明的只读有限扫描实现；不是 AST 允许任意量词的意思。扫描的内部临时计算可以由宿主隐藏，但必须证明在声明的入口状态和公开观察上只读。

编码证书的链条是：

```text
Accept(cond,s)
  ⇒ Meaning(residual_AST,s)
  ⇒ Meaning(original_AST,s)       静态事实用于消解
  ⇒ P(s)                         前提编码
  ⇒ Q(S1,S2,s)                   入口条件支持局部语义义务
```

默认只需要充分性，允许保守拒绝。最大接受域、最弱条件和最小检查成本是独立质量目标；永远拒绝虽可正确，却不是有用优化的验收结果。

只读契约在前台明确要求检查后的入口状态等于原状态；分派语义还须证明没有新增公开事件或检查发散行为。若实际 IR 状态含临时寄存器／局部变量，应证明抽象入口 view 不变及真实宿主的观察一致，不能未经证明删去它们。旧有状态扫描尚未迁移到这份契约。

## 6. 多面体实例怎样证明局部等价

循环实例的使用者应交付或通过验证器取得四类证据：

1. **实际语义与实例集合对应。** `S1` 和 `S2` 的真正控制流分别对应哪些动态语句实例；参数、域边界、索引映射及各实例的动作含义一致。分块、索引变换或分区需要源实例与目标实例的对应 witness；不能只证明两个 schedule 数组是排列。
2. **需要交换的动作可以交换。** 目标顺序颠倒了哪些源有序实例对；每一对的读写冲突／其他 effect 都由局部性质支持。保持顺序的依赖可以保留，不要求所有不同动作互相独立。
3. **入口条件足以支持执行过程。** `D ∧ P` 建立所需不变量，动作保持它，或者源／目标每个相关执行前缀分别满足证明义务。控制与地址无溢出通常需要覆盖未来迭代；数据运算可继续使用语言的正常 wrapping 语义。
4. **循环退出与外围可见状态对应。** 内存及 live-out 保持，或由宿主证明差异不可观察；目标有限执行／进展满足声称的语义范围。重排改变 `i,j` 的退出值时，必须保持它们或证明它们不在接口里。

设施应分为可复用的动作语义、性质驱动的交换、实例对应／调度验证和真实语言桥接。当前 [AbstractSchedule.v](../theories/AbstractSchedule.v) 已提供状态不变量、观察运输及合法相邻交换链；[ScheduleInterleave.v](../theories/ScheduleInterleave.v) 提供块交换和矩形行顺序证明；[LocalScheduleEquivalence.v](../prototype/interface/LocalScheduleEquivalence.v) 在独立性对称和观察兼容时提供双向执行对应。

这些定理不固定整数或内存语义，也不自动给出任意多面体候选的验证器。一般实例 bijection、非矩形域、分块及真实 Clight 循环的桥接继续由相应实例完成。框架的价值包括复用上述基础设施，减少每个实例重复证明交换、frame、检查和上下文的工作；仅要求使用者交一份任意等价定理是不够的。

本文的 `I` 是需要固定的片段接口设计；当前 Rocq 前台通过 `domain`、共同 `observation` 和宿主的位置／可安装字段承载这些义务，尚未实现一个通用类型化 footprint record 或自动 effect 分析器。两单元示例的 frame 和 continuation 证明是实际实例，不能据此声称已经得到 Clight 的一般 localization 库。

## 7. 全局相关证明怎样交付

当前 `rewrite_context` 固定语言实例提供的插入和组合规律：

```text
Placement(C,S1,D)
∧ Admissible(C,S1,R,D)
∧ LocalEq_D(R,S1)
  ⇒ ∀o. RunProgram(C[R],o) ↔ RunProgram(C[S1],o)
```

`R` 在这里是实际生成的 guarded 片段。Placement 包含实际源定位、入口域和源 effect 的宿主依据。Admissible 核对目标类型、临时变量新鲜性、入口／出口和宿主所需进展；条件代码也是目标的一部分。

新增语言／片段形态的作者证明这条组合规律一次。每个使用者的 pass 为自己选定的位置实例化 Placement 和 Admissible。支持的语言可以用语法检查、作用域和 effect 分析自动生成证书；有任意多入口 CFG 或外部调用时，需要专门宿主而非默认全部允许。

局部 proof relation 与上下文必须相容。例如以 live-out 加内存 frame 定义的观察，要能被后续 load、调用和其他 continuation 消费。把一个有限正常终止的端点定理嵌入实际小步语义时，还要覆盖目标的进展及匹配步骤。这是语言适配器的真实证明工作，不是框架自动补出的假设。

给出只读 condition 与局部条件等价后，`guarded_rewrite_equivalent` 构造整个 guarded 片段的局部等价；再消费宿主及实际位置证书，`guarded_rewrite_program_equivalent` 构造程序级等价。使用者的 traversal 只需证明实际替换绑定正确并逐次满足这些义务。

## 8. 常见模式怎样共享设施

| 模式 | 局部前提与证明设施 | 位置／effect 义务 | 当前新接口实例 |
| --- | --- | --- | --- |
| optimistic 循环重排、分配、分块 | 实例对应、冲突分离、控制／地址解释、合法交换 | 循环入口、退出游标、内存 frame、进展 | 数学实例的有限迭代重排；真实 Clight 2×2／动态矩形 store、读写更新、行内依赖及运行时 stride 的纯写交换已接完整编译；一般 affine／分块旧入口未迁移 |
| 条件算术／死分支 | 指定算术运算的定义性／无溢出、局部表达式或控制等价 | 操作数已定义，guard 插入不改变求值路径，结果／出口保持 | 8-bit modulo 增量的条件分支删除 |
| 重复 load 消除 | 相同位置、可读能力、中间写入不影响读取 | 源 load 的安全依据；普通读取的事件语义 | 新接口已有固定单元／有界 indexed 写足迹下的 payload 提升和内存循环上界提升，使用 non-alias、前缀不变性及私有快照；源进展独立于稳定性；一般 load 消除仍需各自证明 |
| 实现／布局特化 | 身份、布局、稳定性及调用等价 | 环境、调用行为、异常、版本稳定 | 后续案例，尚无新宿主 |

这些模式共享前提 AST、安全只读检查、frame 和上下文库，但局部定理的形状不同：算术重写不需要实例排列；循环重排不能只靠表达式等价。第一主线仍是 optimistic loop transformation，优先验证多面体候选的实际实例对应和依赖义务。

## 9. 已运行的实例与明确边界

[GuardedRewriteExamples.v](../prototype/interface/GuardedRewriteExamples.v) 提供一个新的数学语言实例。状态包含两个整数单元、两个输入单元标识及一个不属于片段的公开值。条件只读取入口；两个原子是单元分离和 `x+1` 的 8-bit 非回绕范围；任意 Boolean 公式复用已有检查可靠性定理。

循环实例的源顺序为每次迭代执行 `Left(v); Right(10*v)`，候选为先执行所有 Right 再执行所有 Left。值列表可以为空、有重复或任意有限长度。实例复用交换／分组证书，证明两方向的整个状态对应及外围任意纯 continuation 的程序等价。

实际编译的例子验证：

```text
分离的两个单元：guard 接受；最终为 left=2,right=20；外围值77保持。
同一个单元：未经检查的候选最终为2，源为20；guard 拒绝并得到20。
增量输入254：非回绕检查接受。
增量输入255：检查拒绝；回退保留源的回绕分支结果1。
```

这份实例明确提供了条件编码、局部等价、frame、语言分派和真实 continuation 组合的证明，演示实例作者的工作。它使用有限动作列表和总函数，不是新实现的 Clight 循环／原生多面体优化，也不包含真实指针权限、机器整数 lowering 或发散。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-proof
```

该检查编译十一个接口模块和三个既有依赖，打印 43 个接口证明端点的闭合假设报告，其中只读 rewrite 扩展占 34 个；包括关系式 localization、有限替换序列、前提入口推导、域限制及完成性／确定性下的单向证明复用，以及隐藏私有出口的观察运输。日志及源码摘要位于 `build/interface/`。`make interface-clight-proof` 另审计真实只读 Clight 适配、frame／延迟读取案例及结构化片段确定性；投影 Clight 编译接口另支持新鲜候选私有 temp 的出口差异，并消费 scope／入口／continuation 证明；保护的集合目前是所有原程序 temps。具体责任与缺口见 [Clight 接入设计](clight-guarded-rewrite-design.md)及 [Optimistic Loop Optimization 验收账本](optimistic-loop-acceptance.md)。现有 CompCert 编译器源码没有改变；旧入口协议仍保留。


## 当前的组合使用者

[ClightCommonRewriteCompiler.v](../prototype/interface/ClightCommonRewriteCompiler.v) 将已实现的分支、单元交换、循环交换、payload 快照和内存上界快照交给同一 projected host。精确出口规则经有证书的观察提升后，生成代码保持相同；使用者补充源 temps 写界。576 次调用／2880 行结果验证同一函数中的多次真实片段改写，详见 [组合使用者案例](clight-common-user-pass.md)。这项组合没有扩大各规则原有的循环形状或动态足迹覆盖。

运行时 stride 的规则随后也接入该 pass：[使用者案例](clight-runtime-stride-case.md) 展示具体的读取域、64 位检查编码、body 不变式、局部执行对应和完整程序端点。345 次调用／342 行输出通过；独立 stride 入口与统一 pass 都确认实际候选保留参数 stride、空路径延迟读取及后一次 rewrite 使用修改后的入口。框架共享检查合成和局部到全局连接；布局维度事实和实际内存交换仍由这个语言实例提供。

[有界动态 indexed 足迹](clight-indexed-load-case.md) 又证明循环写 `out[i]` 时的参数读取稳定性。实际源执行逐点建立权限，条件覆盖所有活动地址，non-alias 接受后才缓存 load；1095 次调用／2188 行结果在独立入口和统一 pass 上通过。默认上限 16、O(cap) 地址比较、17 个生成候选出口均明确记录；这不等于一般无界区间／仿射足迹分析。

[源前缀安全的内存上界](clight-indexed-bound-case.md) 进一步把 indexed 写足迹与 memory bound 组合。规则作者不能用入口上界预先假定整个 footprint 有效：写入可能改变上界并提前退出。检查证明沿实际源前缀推进，每次 non-alias 接受后才证明下一次比较安全；源完成 witness 仅用于证明，不是运行时 oracle。语言侧的 `strict_active_condition_transport` 让局部 body 证明使用实际为真的头部，分别维护头部与自增前不变式。它是本 Clight 实例提供的设施，语言无关核心仍只消费前提、只读检查、局部观察关系和宿主契约。


## 固定上界的等式退出实例

[等式退出使用者证明](clight-equality-loop-case.md) 展示另一种 source protocol：使用者将固定寄存器上界、单位 unsigned 自增、有限不改 temps 的 body 交给宿主。检查 `i==0 && 0<(int)n` 接受后，局部不变式证明实际 `!=` 头部可换成 `<`；检查不读内存、候选保留完整原始出口。原循环进展另外使用模距离证明，所以 unsigned 回绕回退不依赖 no-wrap。

`ClightCounterProgress.v` 的计数器事实由具体语言实例提供：活动谓词、自然数排名、更新、正性、递减、实际自增求值和纯性；宿主连接真实小步与局部完成执行。这是 Clight 实例的证明设施，语言无关核的四份契约没有加入整数语义。选中的源片段本身可能发散时，当前宏片段宿主仍需扩展逐步模拟接口；无限外围可以使用现有上下文证明。


## 逐步求值宿主与能力选择

[宿主能力与证明职责](host-capabilities.md) 固定宏片段和逐步求值两种用法。`ClightReadonlyExpression.v` 将有限表达式分派实例化到相同语言无关核，`readonly_expression_rule` 要求完整值／类型的局部等价、只读条件，以及从每次实际源求值建立域。它不要求外围循环先有终止执行。

[逐步头部案例](clight-stepwise-head-case.md) 在每次到达时检查当前 `(int)i≤(int)n`，将实际 `!=` 换为 `<`；body 可以改变上界或包含 volatile，step 可以为 2，两个明确无限源中的头部也已进入小步模拟和完整 Csem→Asm。无限函数只编译／检查，发散覆盖来自模拟定理。这里没有把整个无限循环当成可完成的宏片段，也不提供其有限 polyhedral 域。统一入口组合既有 projected region pass 与这个逐步 pass，前后检查各使用自己的实际入口。

[普通表达式规则](clight-loaded-comparison-case.md)进一步展示使用者如何定义有证明的 condition 生成器：提供两个实际 signed32 操作数及类型证书，模板生成 `≤` 检查、从实际源求值得到的定义域和完整比较值等价。普通 load 可重复于本次只读求值，但不自动成为稳定 preload；source volatile 事件必须在检查之前执行一次。独立／统一入口各通过 737 次调用，完整接口 184 端点审计无新增公理。

[内存上界／二维调度使用者](clight-loaded-matrix-case.md)也已交付同一个 projected rule：提供真实语法和局部 body 证书，检查安全从实际源行前缀建立，完整前提接受后才稳定 preload 并重排四个动作。独立源进展由保护 outer iterator 的嵌套协议提供，不能假定 alias 不会改变源循环次数。独立／统一入口各通过 668 次调用；199 端点审计无新增公理。当前接受域固定为 2×2，不由这一实例推广到任意 schedule 或一般 memory-bound 尺寸。
