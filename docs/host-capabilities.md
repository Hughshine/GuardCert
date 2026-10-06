# 局部证明与宿主能力的分工

2026-10-05。本页固定一项接口原则：语言无关核不要求每种语言、每种 rewrite 使用同一种片段进展证明。使用者选择实际原片段、候选、只读检查及位置；局部证书和上下文宿主的能力决定这一调用覆盖什么行为。

## 核心统一的部分

`guarded_rewrite(S1,S2,cond) = select(cond,S2,S1)` 仍是一次替换的定义。语言无关 [GuardedRewrite.v](../prototype/interface/GuardedRewrite.v) 只消费宿主的 code／check／state／observation／dispatch law。条件证明、安全判断、具体语义和效果的解释来自语言实例。

规则作者提交 `D`、`P`、`readonly_condition D P cond` 和适合宿主的局部对应证书。完成执行的宿主消费 `conditional_equivalence D P S1 S2`；可能无限的整段宿主还要求实际小步协议。`D` 说明宿主允许的进入及检查定义性，不能把希望运行时验证的稳定性／non-overflow 偷放进去。`P` 是接受后建立的前提，不是源程序执行的先验保证。局部表示与 frame 定理将源／候选模型接回真实片段；上下文定理再连接完整程序。

相同的核不意味着相同的 `Run`：表达式宿主观察实际 `val`，片段宿主观察内存／temps／trace／outcome，其他语言可声明自己的观察。只有真实语言宿主覆盖的行为才能进入全局主张。当前 Csem→Asm 端点是 backward simulation，不能称作两种语言的双向行为等价。

[公共 actual realization](clight-guard-realization.md) 将有限 guard 分派和宿主的分支执行义务分开。direct/shared 同一接口证明实际到达选中分支、私有资源和 temp frame；正常完成的宏适配器另消费 branch transport，unsigned 完整循环消费前缀后继续局部小步匹配。分派定律不要求分支完成，不代表每个消费它的宿主都已取消 source progress。具体三方责任见 [责任矩阵](framework-responsibilities.md)。

## 当前三种 Clight 宿主

| 维度 | 完成的宏片段宿主 | 有限求值的逐步宿主 |
| --- | --- | --- |
| 一次局部替换 | 整段 statement，包含整个循环 | 一个实际值表达式；可出现在具体 skip/break 头部 |
| 实际条件位置 | 片段到达时检查一次 | 每次该求值位置到达时检查 |
| 局部观察 | 完整原始出口，或保护所有原 temps 的公共边界 | 完整 `val` 和表达式类型 |
| 入口依据 | 实际源片段正常完成执行与独立源进展协议 | 当前实际源表达式求值 |
| 全局桥接 | 源 cursor 的小步进展→实际完成执行→目标片段→continuation | 有限检查分派＋同值求值→同一 continuation |
| 选中整个循环可能发散 | 当前不支持；外围可以发散 | 不选整个循环；其内部有限求值可以改写 |
| volatile／调用的外围效果 | 当前 quiet region 排除被选片段内这些动作 | 保持其他代码结构，运输实际事件／调用；没有在表达式中重复 volatile |
| 当前实例 | 矩形调度、稳定 load／bound 快照、indexed non-alias、固定上界 `!=→<` | 逐头部 `!=→<`、assignment／return 的比较值 |

第一个宿主需要源进展，原因是它将实际源小步组合成一次终止执行。第二个宿主每步都保持原控制，不需要外围的终止执行。不能给宏片段宿主提交一个只有有限正常执行的局部等价，就推断任意源循环发散路径也已覆盖。

第三个是 [整段小步宿主](conditional-progress-host-design.md)，接口为 `open_region_protocol`／`open_region_contract`。它一次选择整个 statement，只在进入时检查一次，但不收集 source completion：每个实际源步由目标正步数匹配，或由目标零／多步匹配并严格减少索引。局部后继继续匹配，或交还保护全部原 temps 与 memory 的正常出口。它可以覆盖整段原回退的无限执行；[内存上界缓存案例](clight-guarded-circular-case.md)已接到 Csem→Asm，并另有实际源／目标 `forever_silent` 定理。

这个接口不是任意控制出口的开放模块协议：当前局部源状态限定为同一函数／locals 的 `State`，两段 label-free，正常 `Sskip` 出口返回外层 continuation。初始实例是 quiet Mint32 循环；内部调用、return、跨片段 goto 和其他出口需要扩展契约。外围结构、调用和跳转仍由宿主运输。局部规则自己交付有限检查前缀、条件证书和每步对应，框架提供 scope／freshness、公开出口与完整程序组合。

新 `ClightCounterProgress` 把 Clight 计数器的 active／rank／update 及实际自增求值交给实例，不固定整数单调性。固定上界、单位 unsigned 自增用模距离实例化，原循环即使回绕也有独立源进展。step=2 的 odd target 和同时变化的 target 不满足这个证明；它们的头部可通过另一个逐步宿主改写。

## 常见模式需要什么性质

| 模式 | 主要前提 | 局部证明设施／义务 | 接入中的关键限制 |
| --- | --- | --- | --- |
| 条件值 rewrite、死分支 | 值关系、非零、范围或不可能条件 | 实际求值同值／同出口；短路条件安全 | 类型、错误和当前求值时点都要对应 |
| 乐观循环调度 | 模型控制／地址对应、动作独立或源顺序保持 | 实例／调度见证、实际内存动作交换、出口恢复与 frame | 接受条件须覆盖整个被重排执行；不能只比较 body 结果 |
| 稳定参数／bound preload | 活动路径定义性、实际写集与读取位置分离 | 源前缀安全、每次真实写入后的 load 不变性、私有快照 | 检查安全不能先假定稳定 footprint 成立 |
| 动态布局／stride | 维度界、线性化忠实、地址不回绕 | actual machine index／pointer 与数学坐标对应 | 检查自身的宽化／乘法／比较也要安全 |
| indexed alias | 活动访问族的冲突分离、访问宽度／对齐／权限 | 实际足迹与源访问对应，alias 接受后建立交换或稳定性 | 一般权限不是可直接读取的运行时布尔量；当前新接口扫描有 cap |
| 私有迭代器／cache | 新名字、scope、公开边界不变 | fresh pool、源入口与 continuation 运输、局部公共观察等价 | 目前保护所有原 temps，不把已有 temp 当作免费 dead scratch |
| 可能无限循环中的头部 rewrite | 当前两个完整值的条件关系 | 每次实际检查同值＋逐步控制运输 | 不由此得到整段有限域或一次性调度合法性 |
| 整段回退可能无限的 guarded loop | 有限前缀中的检查定义性；接受后的稳定性／候选对应 | 实际局部小步协议，零步匹配下降，拒绝回到原小步，正常出口 frame | 完成执行等价本身不够；当前实例限 quiet word／单位 unsigned 自增 |

框架提供可复用设施，不替使用者假设具体语言的性质。例如 `non_alias ⇒ 可交换` 是语言／动作实例的定理；不同宽度、volatile、异常或其他事件必须另有实际语义证明。当前 Mint32 单元和循环动作库满足自己声明的范围，不推广成任意内存代码交换。

## condition 的表达与合成

当前表示是有限 Boolean AST 加经语言实例注册的原子；动态足迹的全称义务通过有证书的有限扫描或保守入口界处理。否定不能把 unknown 变成负面证据。原子可由多步骤树实现，包含普通 load；每个可达测试的安全必须证明。专用生成器也可直接提交同一个 `readonly_condition`：`ordered_inequality_rule` 从两个 signed32 操作数及类型证书生成 `≤` 检查和局部证明，操作数的定义性来自本次源求值。它不要求表达式都先进入同一语法枚举，也不允许任意 `Prop` 无证书编码。

`ReadonlyConditionComposition` 另组合带依赖的顺序阶段：后项的域使用此前接受的性质。核证明组合安全、可用、状态不变与接受全部性质；Clight 提供实际决策树代数。它不会从任意 `Prop`、任意候选、任意量词自动找出可运行 condition，也不保证最弱条件、最小检查成本或候选收益。

[只读分支与前缀扫描](readonly-prefix-scan-interface.md) 允许提前成功和不同分支的安全域。每个结果的证据须单独提交；普通拒绝不产生否定。使用者提供当前点的活动性、性质检查和下一点的 ghost invariant，框架生成有界扫描。indexed 内存上界的实际编译入口已调用这个生成器，并用源剩余执行及权限／load 运输实例化 invariant；宏片段宿主的源进展义务没有因此省略。

前提位置可以影响接口选择。整段版本化的 `P` 要能保持到整个候选消费完成；逐步 rewrite 可以在下一次到达时重新建立当前值关系。两者不能互换检查时点而省略稳定性证明。逐步头部／值表达式实例已通过独立入口和统一入口各 333 次实际 C 调用／284 行输出，完整编译接口 209 个端点的假设审计通过；原头部 fixture 当前有十处改写，另外普通 load／计算表达式／常量 fixture 在两个入口各通过 737 次调用；见 [头部案例](clight-stepwise-head-case.md)和[普通表达式案例](clight-loaded-comparison-case.md)。

## 多次替换与 pass 组合

一次调用满足局部和插入证书后，程序等价／模拟按每次替换叠加。后一次检查使用经过此前替换仍正确的实际入口状态，不能复用过时的函数入口事实。抽象重复 rewrite 定理与真实统一 pass 共同体现这一方式。

`compile_readonly_tests_after_correct` 进一步接受一个先行 Clight pass 及其 forward simulation。当前统一入口先做直接／共享 projected regions，再做逐步表达式／头部变换，最终复用 CompCert backend；这项组合不要求先行 pass 和后来规则共享前提、候选产生算法或内部 cursor。

一般 guarded 调度／tiling 的整段发散行为、一般仿射／无界廉价 alias 条件、一般动态尺寸／stride 的 memory-bound 调度，以及旧 affine 编译器到主只读接口的迁移仍是主要缺口。新宿主和 unsigned bound 缓存实例解决了一个真实完整循环的无限回退能力，不将这些更一般需求自动纳入。先有可复核的局部证书，再由相应宿主扩展全局覆盖。

[内存上界与 2×2 调度](clight-loaded-matrix-case.md)现已在宏片段宿主中组合；它的源协议允许 body 是保护 outer iterator 的嵌套 `framed_progress`。当前 bound 可以被源写入改变，最大值 rank 不使用稳定前提；只读条件安全沿源行前缀建立，接受后才快照并调度。独立／统一入口各通过 668 次调用，该阶段完整审计 209 端点、十五种配置回归通过。这个已完成的固定尺寸模板不扩大为一般动态 memory-bound 多面体调度。

综合入口已进一步组合三槽 private pool、原直接 lowering 和双动态矩形的共享／简化 lowering，实际单／双缓存交替程序见 [多缓存案例](clight-common-multicache-case.md)。这项资源组合没有移除宏片段的独立 source progress 要求。

新的 [整段小步宿主](conditional-progress-host-design.md) 已实现上述最小发散回退：unsigned `i!=*bound` 且 alias body 每轮写 `i+2U`。有限真实源前缀提供检查安全，接受后源／cached 候选逐步对应，拒绝后完整原循环可以无限；候选另有模距离进展定理，不要求 source 的无条件 rank。接口、实际证明与提取验证分别见 [案例](clight-guarded-circular-case.md)和[当前记录](research-checkpoint-2026-10-05.md)。
