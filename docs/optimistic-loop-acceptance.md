# Optimistic Loop Optimization 验收账本

2026-10-05。主要参照 Doerfert、Grosser、Hack 的 [CGO 2017 论文](https://compilers.cs.uni-saarland.de/papers/doerfert_cgo17.pdf)（pp. 292–304）。本文将论文需求转成 GuardCert 的工程验收，不要求复现 LLVM/Polly 的代码和性能结果。下表的实现划分与测试标准是本项目设计。

## 论文能力与当前证据

| 参照 | 需求 | 新接口证据 | 尚缺 |
| --- | --- | --- | --- |
| §4.1 | 读取可作为稳定参数 | 实际参数 load 与内存循环上界提升；源前缀安全的 indexed 上界检查；non-alias 前缀不变性、私有快照、独立源进展和完整编译；延迟读取原子；[动态内存行数／列数与矩形交换](clight-loaded-rectangle-case.md)；[参数 stride 的有界布局组合](clight-loaded-stride-case.md)；[双内存上界的单次迭代消除](clight-dual-loaded-unit-case.md) | 两维动态数组调度、一般大布局 stride、多个依赖 preload |
| §4.2 | 控制／地址的机器算术与整数模型对应 | 动态矩形范围条件、登记文本位置的入口推导、实际 Int／Ptrofs 地址对应及循环消费；初始化溢出反例 | 一般初始化／非仿射条件；带 preload 的实际范围合成 |
| §4.3 | 有界实例域 | 固定寄存器上界、单位 unsigned 自增的实际 `!=→<`；接受范围不变式、模距离源进展、unsigned 回绕 fallback 与完整编译 | 一般 stride／变化目标的整段有限域或调度；与多维调度组合 |
| §4.4–4.5 | 维度界、线性化／去线性化对应 | 固定 stride 的动态 store／更新／行依赖；运行时 stride 的实际 store 地址、完整交换与只读条件；动态 memory-bound 行数和列数的实际交换；extent≤12 的全部合法正参数 stride 布局、枚举完备性与原地址运输 | 参数 stride 的更新／复杂依赖、两个内存维度、更大布局／一般指针 stride 的 memory-bound 组合 |
| §4.6 | 活动访问区间不重叠 | 实际 Mint32 单元交换及 frame；有界动态 indexed 写足迹的只读分离检查和整个参数 load 提升；旧路线的多个指针检查；嵌套活动 word 分离检查消费于动态 memory-bound 矩形交换；已验证共享候选出口和重复探针消除 | 廉价无界区间／一般仿射足迹、检查 DAG 和更复杂调度 |
| §5 | 条件简化与保守近似 | `entry_derivation`、强化条件证书；从固定数组布局导出动态范围并生成实际 guard；[保留原证书的路径探针简化](readonly-probe-simplification.md)，实际编译消费 | 外部求解器输出的可核对表示与更一般投影 |
| §6，Algorithms 1–2 | 检查自身的算术安全和 preload 安全 | 真实 Clight 树安全；普通 load 原子及公式合成；参数 stride 的 signed64 乘积检查无回绕证明；indexed 上界检查从实际源前缀建立安全，不预设完整稳定 footprint；第二行比较依赖前行 non-alias 证据；单次迭代例子沿源活动路径建立第二个 load 与两个地址比较的定义性 | 带算术检查和多个依赖 preload 的一般组合合成实例 |

论文里的维度界与 CompCert 内存权限不能互相代替。我们的实例必须分别证明“多维表示忠实”与“实际执行的 load/store 有定义”。同样，省略检查只能使用已证明的静态入口事实或源语义约束。

## 怎样判定已达到主线验收

需要一个可重复构建的实际循环实例，消费新 `readonly_condition`／局部接口，再连接完整程序定理和提取后的编译器。只打印模块名、接受一个未消费的 schedule，或运行脱离编译器的 Python 模型都不算通过。

| 验收项 | 必须观察／证明的结果 |
| --- | --- |
| 入口条件生成 | 输入是被登记的前提／模型证书；输出是实际检查语法及接受可靠性证书 |
| 文本位置覆盖 | 源中的初始化、循环头、增量和地址操作都被覆盖；不是仅检查候选 body |
| 条件活动读取 | 外层为空时不读取内层 bound 指针；检查地址不能安全计算时回退 |
| 稳定参数 | 参数地址不在实际写集内；进入执行后每个需要的读取保持同值 |
| 地址和维度 | 控制／地址非回绕；参数 stride 的多维到线性地址对应；数据运算按语言机器语义 |
| 别名与调度 | 不重叠输入接受；部分重叠及真实依赖拒绝；同一 block 的安全切片可接受 |
| 局部执行对应 | 源／候选实际实例与模型双向对应，调度确实改变了执行顺序 |
| 出口与 frame | 活跃循环变量正确；片段外数据保持；私有 temps 不影响 continuation |
| 完整程序 | 真实 region progress／上下文定理消费局部证书，接到 CompCert 编译正确性 |
| 执行证据 | 提取编译器处理 C fixtures；在接受、拒绝、空域和溢出边界输入上比较结果 |

起步实例可限制为二维、两个普通整数指针及结构化顺序循环。随后加入内存载入的边界、参数 stride、多个语句和 tiling。论文评估中的一般性与性能不能由一个模板推出；每项能力分别记录实际证据。

## 推进顺序

当前已固定 [语言接入设计](clight-guarded-rewrite-design.md) 中的职责，编译核心接口、真实只读条件和 effect 设施。延迟读取原子已接入公式合成，从实际源执行导出检查域，并通过一个分支 rewrite 实例消费新接口接到完整 Csem→Asm 定理。C 前端的空语句规范化也有执行对应证明。

`make interface-native` 已通过：实际提取的 `ClightPreloadCompiler.compile_preload_rewrites` 处理 C fixture，输出 Clight 确认 guard／候选／源回退树。68 组 C 调用含四组计数为零且指针为 null 的输入，原生结果与 GCC 参考一致，输出 `172 0`。输入覆盖零／正／最大 unsigned 计数、零／正边界值及数据加法回绕；未运行循环变换或测量性能。报告绑定编译器、源码、Clight 和汇编摘要。

`make interface-matrix-native` 的证明、提取和执行也已通过：`ClightReadonlyMatrix.compile_readonly_matrix` 用新只读 API 实现真正的 2×2 循环交换。局部证明消费实际源 store、核对的调度和候选执行，保留完整内存及全部出口变量；源完成性与候选确定性显式补足等价的反方向。21 次 C 调用、九组矩形输入和五处实际改写区域通过，包括源回退、空域、未初始化但不应读取的内层界、goto 和外围循环上下文。不同 RHS、真实内存依赖、volatile 模板不被改写；输出与 GCC 和独立期望一致。

随后 `make interface-rectangle-native` 也通过：`ClightReadonlyRectangle.compile_readonly_rectangle` 使用从布局导出的 `i=0 ∧ 0<n≤extent/stride ∧ 0<m≤stride`，处理运行时矩形尺寸。225 个正尺寸 store 矩形、六处改写区域通过；842 行 C 输出逐单元、逐出口与 GCC／独立模型一致。八类模型文本位置的条件推导、地址单射性和实际 `Int.mul`／`Int.add`／`Ptrofs.repr` 对应也已编译。源语法与执行覆盖依赖实际 rectangle certificate／decoder，尚无一般求值位置发现器。

只处理 store 的矩形入口将 update／行内依赖模板保留为源。随后组合入口已迁移这些模板，见下段；参数 stride 的纯写模板又通过本页最后一例接入，动态循环 alias 仍未迁移。新 API 的局部等价与完整编译连接已在真实循环中成立，但尚不满足上表全部主线验收。稳定内存上界随后通过下述 singleton 实例接入；下一步须将它与多维调度、动态数组足迹及参数 stride 组合。没有性能测量。

non-alias 基础原子随后接到真实 Clight、局部 store 交换、字节 frame 和完整编译定理。`make interface-cells-native` 运行 82 次 C 调用，包括相同指针回退、同一 block 的分离单元、不同对象和空循环 null 指针；输出 `4100 0` 与 GCC／独立期望一致。无限外围循环也被编译并确认内部 guard，未运行。该原子在源定义且对齐的两个 Mint32 单元上有效，并支持已知结果的否定；它尚未推广到动态循环访问区间或异宽访问，不能视为 §4.6 全部通过。

`make interface-loops-native` 接入 `ClightReadonlyLoopUpdates.compile_readonly_rectangles`：225 个 store、345 个读写更新、225 个行依赖正矩形，十九处实际改写区域通过；842 行结果与 GCC 和逐单元／完整 iterator 出口的独立期望一致。真正的 load 和机器数据运算均在局部动作中，行内顺序保持；错误邻居读取和对角线依赖拒绝。这扩展了 body／依赖覆盖，仍使用固定 stride，并未解决内存载入的稳定边界或动态循环 alias。

局部私有候选也有真实 Clight 例子：候选额外写隐藏 temp，完整原始结果不同，公开边界观察仍等价。源完成、原始候选确定性及观察集合运输形成新的通用单向证明复用接口。投影全局编译接口随后接通：新 pool 的 freshness、目标函数声明、源入口和 continuation 运输由宿主证明，保护所有原程序 temps。`make interface-private-native` 的 83 次调用输出 `625 0`，四个函数中确有新私有写入，其中无限外围循环只编译和检查。当前实例的 guard 为常真，证明私有出口与上下文能力；一般私有迭代器仍待实例化；稳定参数快照随后通过下面的循环实例接通。

`make interface-stable-load-native` 接入 `ClightStableLoadCompiler.compile_stable_loads`：源重复 load 普通参数，候选在活动且 non-alias 时将其移到新私有 temp。实际计数循环／逐次 body 的对应、每次 store 后的 load 不变性和私有出口运输已证明。727 次调用、727 行结果与 GCC 和逐单元／iterator 期望一致；360 个别名输入、360 个同 block 分离输入、三个空循环 null 调用及四个只读参数调用通过。四处实际 guard／候选使用快照已确认，无限外围循环只编译和检查。别名反例的原结果 3 被保留，无 guard 缓存会得到 2。参数只需可读，数据 unsigned 回绕保持。本例补上实际稳定读取和 singleton 循环足迹的 alias 消费，此 payload 实例本身不处理内存中的循环上界；后述实例另补上这一能力。一般数组访问区间或参数 stride 仍待接入。详见 [使用者证明](clight-stable-load-case.md)。


`ClightLoadedBoundCompiler.compile_loaded_bounds` 随后接入真正的 `i<*bound` 源循环，候选使用私有缓存上界。入口域来自实际头部／第一次 store；non-alias 后的稳定性消费每次实际 body，源进展用 signed 最大值证明且不假定上界稳定。新 tree-valued 条件证书允许普通 load，并由表达式确定性及检查完成性证明可达安全。`make interface-loaded-bound-native` 通过 514 次调用／514 行逐内存及 iterator 检查，包含 alias 改变次数、空路径 null 输出、只读 bound、signed 极值回退、goto 与外围循环；四处实际 guard／cache 循环头已确认，无限外围循环只编译和检查。别名反例保留一次迭代及输出 1，无 guard 候选则为 5。完整端点包含在 76 项编译接口审计内，未新增公理；八组原生实例已重建并回归通过。它尚未与二维调度组合。详见 [内存上界使用者证明](clight-loaded-bound-case.md)。


`make interface-common-native` 用 `ClightCommonRewriteCompiler.compile_common_rewrites` 在同一函数中消费上述精确／私有规则。新的有证书嵌入保持精确规则生成的语句相同；源写界由结构化语法过近似核对。576 次调用、2880 行输出通过，四种实际循环交换、两个 store 分支、两处共享私有 pool 的快照和后续读取当前参数值的检查都已确认。九组原生回归在 82 端点审计下重建并通过。统一选择器继承既有内存记录的 proof irrelevance，没有新增公理。详见 [一个使用者 pass](clight-common-user-pass.md)。

`make interface-runtime-stride-native` 随后消费 `ClightRuntimeStrideCompiler.compile_runtime_strides`：实际源／候选均保留 `i*stride+j`，使用有证书的 `i=0 ∧ 0<n ∧ 0<m ∧ 0<stride ∧ m≤stride ∧ (int64)n*stride≤extent`。检查自身的 signed64 乘积精确性、空轴上延迟读取参数、局部执行对应、内存重排和完整 Csem→Asm 已证明。345 次函数调用／342 行输出与 GCC 及逐单元模型一致，330 个参数网格输入中 108 个满足 guard；九处实际改写区域通过，包括两次改写间修改 stride。重叠行、零 stride 和 signed 极值的合法源输入保留回退行为；未初始化内层 bound／stride 的空路径通过。统一 pass 对相同 fixture 也通过，完整编译接口现审计 102 个端点，无新增公理。此例不含参数 stride 的 RMW、一般指针足迹或二维内存上界组合；详见 [使用者证明](clight-runtime-stride-case.md)。

`make interface-indexed-load-native` 随后将 `out[i]=*parameter+(unsigned)i+1U` 的参数 load 提升接入新只读接口。源实际执行导出每个活动 word 的入口写权限及参数读取值；guard 只比较 `parameter` 与活动的 `out+k`，接受后逐轮证明实际 load 不变。默认 cap=16，检查最多 16 个地址，超 cap 保留源；同对象非活动单元和不同对象可接受，部分重叠回退。独立入口和统一 pass 均通过 1095 次调用／2188 行逐单元及 iterator 验证；1050 次同对象网格中 528 个输入满足 guard。const 参数、null 空路径、unsigned 数据回绕和外围上下文均通过。完整编译接口现审计 119 个端点、十一组原生实例重建通过，无新增公理。这是有界活动单元分离而非廉价一般区间检查；只读树提前成功会生成 17 个候选出口，未测量性能。详见 [使用者证明](clight-indexed-load-case.md)。

已有编译器的运行证据继续有效于它自己的协议；新接口的任何一项通过都不自动升级为旧编译器已迁移。这个账本随证明和执行结果更新。

`make interface-indexed-bound-native` 又组合 indexed 写足迹与内存中的循环上界。源可能在 alias 写入后提前退出，因此检查安全沿实际源前缀建立，而不先假定完整入口 footprint；non-alias 通过后才保持下一次头部所需的 load 值。活动头部运输设施分离头部／自增前不变式，完整 Csem→Asm 端点及只读公式原子已证明。独立入口和统一 pass 各通过 1079 次调用／2154 行输出，含三元素数组中入口上界 8、第三次 store 改为 3 后合法退出的关键用例；INT_MAX 上界在 cap 前缀立即拒绝但保留相同合法源结果。139 端点审计与十二种编译器配置回归通过，无新增公理。此阶段解决一个非循环的检查安全边界，仍没有二维 memory-bound 调度或潜在发散的 `!=` 源循环；详见 [使用者证明](clight-indexed-bound-case.md)。

[带依赖的检查阶段](condition-stage-interface.md) 随后将“先建立安全事实，再执行后续检查”抽成语言无关设施。使用者提交按序的只读证书，后一项的域可以使用此前接受的性质；语言提供常量／顺序检查的实际构造与分派／安全定律。框架证明有限阶段生成器的安全、可用、状态不变及全部接受性质。实际 Clight 内存上界规则已消费该设施，生成条件保持原样；纯接口 43 个闭合端点、Clight 57 个端点、完整编译接口 141 个端点审计通过，十二种配置重建回归通过，15 份原生生成 Clight 摘要与前阶段一致。该阶段复用条件证明，不扩大循环形状或接受范围。


[固定上界的等式退出](clight-equality-loop-case.md) 随后补上 `(int)i!=(int)n` 的真实控制变换。只读条件为 `i==0U && 0<(int)n`，没有 cap；候选保留普通 memory body 并用 `<`。接受路径的范围不变式与原循环的模距离源进展独立，fallback 可以经过 unsigned 回绕。新计数器协议由语言实例提供 rank／update／active 及实际求值证明；本例已连接完整 Csem→Asm 定理与统一选择器。完整编译接口 164 个端点审计无新增公理，独立入口和统一 pass 各通过 703 次调用／703 行输出、七处实际 guard；十三种提取配置回归通过，15 份既有源码／Clight 摘要保持相同。一般 stride 或变化目标仍可能使选中片段发散，未由这个实例解决；论文全部主线验收仍未完成。


[逐步头部宿主](clight-stepwise-head-case.md) 又补上可能无限循环中有限求值的 rewrite：每次实际头部建立 `i≤n` 才用 `<`，失败保留 `!=`；允许 step=2、body 改变 bound 或 volatile body，来源于实际小步匹配而非循环完成性。源表达式的入口／完整值等价和只读检查继续消费语言无关核，赋值／return 的比较值也由同一规则处理。完整接口现审计 180 个端点，与既有 STEPWISE 八项和 COMPILER 35 项基线比较无新增公理；独立入口和统一入口各通过 333 次调用／284 行输出和九处实际改写；十四种提取配置回归通过，只有统一等式退出程序增加预期 guard，其他 16 份既有源码／Clight 摘要相同。明确无限的源只编译／检查，未执行。这个补充不建立它们的有限 polyhedral 实例域，也没有解决任意无限整段循环的 guarded 调度；能力分工见 [宿主分类](host-capabilities.md)。

[普通表达式／load 的条件比较](clight-loaded-comparison-case.md)进一步让逐步模板消费 signed32 普通 load、计算表达式和常量。检查安全从本次真实源求值导出，没有预设 bound 稳定；别名 body 改写 bound 后在下一头部重新检查。真正 volatile load 只按源执行一次，后续 guard 使用快照。独立／统一入口各通过 737 次调用和八类实际 contexts，原头部 fixture 的常量比较也被改写，原 333 次调用保持相同。完整接口 184 端点审计无新增公理，十四种配置重建回归通过；与前阶段 19 份报告比较，仅两份头部程序因常量 guard 改变 Clight，另 17 份源码／Clight 摘要相同。它补充逐次 condition 的表达／安全实例，不补足一次性稳定 preload、多维 memory-bound 调度或一般 non-overflow 合成；主线验收仍未完成。

[内存上界与二维调度](clight-loaded-matrix-case.md)随后在同一次 2×2 rewrite 中组合：从实际源当前行得到比较权限，前行全部 non-alias 后才建立下一行的 bound 稳定及访问依据，最终私有快照供真正的列优先候选消费。新的嵌套 strict 源协议只保护 outer iterator，rank 不依赖 load 稳定或接受条件。独立／统一入口各通过 668 次调用／673 行输出和七处实际 guard，包括 alias 提前退出、入口 1 变成 2 后额外源迭代、未初始化 inner bound 的空路径和两次 rewrite 之间修改 bound。199 端点审计无新增公理，十五种提取配置重建回归通过，21 份既有源码／Clight 摘要相同。该实例补上此前缺少的一项真实组合，但接受域固定为 2×2；一般 memory-bound 尺寸／stride、复杂 body、多个依赖 preload 和旧 affine 迁移仍待完成，论文主线验收仍未全部达到。

[通用只读前缀扫描](readonly-prefix-scan-interface.md)随后提炼上述检查结构。语言无关核接收活动探针的两种结果证据、当前点性质和下一点的 ghost invariant，生成可提前成功／保守拒绝的短路树并返回原有只读证书。indexed 内存上界的实际编译规则调用这个生成器，完整条件与原手写树有相等定理；权限、真实源 tail 和 load 稳定性全部由 Clight 实例提供。纯接口 49 个端点闭合，Clight 59 个端点与完整编译 209 个端点审计无新增公理；十五种提取配置全部重建回归通过，23 份既有源码／Clight 摘要相同。提取产物仅保留三个代码生成字段，没有运行时 ghost 查询。这一阶段复用证明结构，没有扩大接受范围或完成一般动态多维能力。

[动态内存上界矩形](clight-loaded-rectangle-case.md)随后在真实编译入口中嵌套使用通用扫描：先从当前实际源行解码 stores，在行内检查活动地址；整行接受后才保持 bound 并建立下一行依据。候选快照并交换真实动态行数／列数，保留完整公开出口。独立／统一入口各通过 6,248 次调用／6,253 行输出、七处真实 guard；包含后续行 alias、上界增长／缩小、同对象非活动单元、空路径、超布局但合法源回退和 sequential contexts。242 端点审计无新增公理，十六种配置重建回归通过，23 份已有源码／Clight 摘要相同。stride 仍静态，树展开有显式预算，当前每处 region 复制 156 份候选；尚无性能结果。两个内存维度、参数 stride 的组合、多个依赖 preload、廉价一般足迹、复杂 body 和旧 affine／tiling 迁移仍未完成，不能认定全部论文主线已验收。

[共享检查出口](shared-guard-lowering.md)又复用同一 condition／局部 rule：检查叶仅保存新鲜的编译器私有 Boolean，随后候选／源回退各一份。实际 Clight 私有写入由 scope、执行运输和 projected context 证明覆盖，抽象条件仍只读。共享入口通过相同 6,248 次调用／6,253 行输出；251 端点审计无新增公理，十七种配置回归通过，25 份既有源码／Clight 摘要相同。单 region 候选由 156 份减至一份，打印 body 从 332,491 字节减至 61,039 字节；不代表性能测量或完整 DAG。检查树重复展开、两个内存维度／参数 stride 组合和 affine 迁移仍是缺口。

[只读探针简化](readonly-probe-simplification.md)进一步提供语言无关的部分 Boolean 探针接口：同一入口结果确定、编译执行／安全对应、路径事实有实际测试依据。原条件的 D／P 与候选局部证明直接复用，不能将 guard 拒绝当作 ¬P。矩形共享编译实例消除重复实际表达式测试，同一 6,248 次调用／6,253 行输出通过；259 端点审计无新增全局公理，十八种配置回归通过，26 份既有源码／Clight 摘要相同。单 region 打印 body 61,039→6,584 字节，语法 if 289→45；这是静态生成结果，没有性能测量，也不是一般 DAG、算术投影或扩大优化接受域。后续仍优先完成参数 stride 与内存上界、两个内存维度及多个依赖 preload 的实际循环组合。

[运行时 stride 与内存上界](clight-loaded-stride-case.md)随后在同一次实际循环交换中组合：语言实例从真实活动 store 获得 stride 的定义性，将它等于选中布局时的源运输到常量模型，再消费原前缀证书，最后把候选恢复为参数地址。固定 extent≤12 的布局枚举完备性及数学乘积界与常量除法界的对应已证明，运行时无需可能回绕的 signed32 乘积检查。独立／统一入口各通过 68,368 次调用／68,373 行输出、八处实际 region；279 端点全量审计无新增全局公理，十九种配置回归通过，27 份已有 source／Clight 摘要相同。空外层／内层时未初始化参数、后续行 alias、bound 增长／缩小、重叠布局及两次 rewrite 间改变 stride 均覆盖。该 pass 使用有界枚举、简化和共享出口，不是一般大布局、两个 memory-bound 维度或多个依赖 preload 的完成；尚无性能结果。

[两个变化内存上界的单次迭代消除](clight-dual-loaded-unit-case.md)又接通实际双上界源协议、按活动路径延迟的两个普通读取、两项 non-alias 稳定性和完整原始出口。`i=0,*rows=*columns=1` 且输出分离时，候选消除循环；alias 引发额外行／列则原循环回退。独立／统一入口各通过 3,035 次调用、七处实际 region；297 端点审计无新增全局公理，二十种配置回归通过，29 份旧 source／Clight 摘要相同。这个受限实例解决双 preload 的实际读取时机和协议接入，但没有完成两维动态数组调度、多个依赖 preload 或复杂 body。下一步逐点源 cursor 必须同时保存真实内层 tail 和外层 tail；检查当前写入与两个 bound 分离后才推进，不能预设整行 stable。
