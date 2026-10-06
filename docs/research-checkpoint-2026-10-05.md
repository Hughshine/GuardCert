# 2026-10-05：当前框架、运行效果与下一项验收

GuardCert 当前能把使用者提供的片段变换安装成“运行时条件成立就执行候选，否则执行原片段”，并将条件正确性、局部执行对应和上下文证明连接到 CompCert 完整 Csem→Asm backward simulation。主要目标仍是 [Optimistic Loop Optimization](optimistic-loop-acceptance.md) 的条件合成与循环变换需求；尚未完成大布局／一般指针缓冲区、两个 loaded 维度与参数 stride 的一般组合、多个依赖 preload 和旧 affine／tiling 到主只读接口的迁移。

## 框架提供什么

使用者选择实际 source、candidate 和位置。语言实例提供状态、执行、公开观察、检查分派与安全定律。规则作者提交入口域 D、接受性质 P、只读条件证书和 D 且 P 下的局部观察等价。框架安装检查／候选／源回退，复用 effect／frame、前提编码、局部还原和上下文组合设施；多次正确替换可以叠加。

condition 是真实代码，P 是逻辑断言。检查必须有定义、能完成、不改变入口，并且接受蕴含 P；拒绝通常只是没有获得证据。条件生成不接受任意 Rocq `Prop`，而使用已注册的原子、Boolean 公式、带依赖的阶段和有证书的分支／前缀扫描。整数、内存和 alias 的含义在语言实例中证明，核不检查这些具体语义。

当前有三种真实 Clight 宿主：完成执行的宏片段版本化、每次值求值／具体头部的有限 rewrite，以及整段局部小步协议。前两者分别要求独立源进展或只选择有限求值；第三种可以选择完整循环并保留无限原回退，不要求整个源完成。详见 [使用者契约](guarded-rewrite-contract.md) 与 [宿主分类](host-capabilities.md)。

## 这一天补上的十三个结果

第一项是 [内存上界与 2×2 循环交换](clight-loaded-matrix-case.md)。源外层每次读取 `*rows`，候选缓存 rows 后交换 i／j 两层。条件核对活动维度和四个实际 word 地址的 non-alias；第二行的检查依据只有在第一行检查通过后才建立。

例如 `rows=&cells[0]`、入口 `cells={2,1,1,1}`、columns=2：源第一行把 bound 改成 1，随后退出，结果为 `{1,2,1,1}`。无 guard 的缓存／交换会额外写第二行，得到 `{1,2,11,12}`。已编译的版本在 alias 检查处回退，保持源内存和 `i=1,j=2`。独立与统一编译入口各通过 668 次真实 C 调用／673 行输出，覆盖 alias 改变上界、空域、公开出口及外围上下文。

第二项是 [通用只读前缀扫描](readonly-prefix-scan-interface.md)。使用者提供活动检查、当前点性质和下一点所需的 ghost invariant；框架生成有限短路检查并证明安全、可用、状态不变及接受性质。两个检查结果各自的证据显式交付，不能将 unknown 当作否定。已有 indexed memory-bound 编译规则实际调用这个生成器；完整条件与原手写树有相等定理。

这个使用者的 ghost invariant 包含真实源剩余执行、load 不变性和权限运输。提取后的 spec 只保留下一点和两个探针生成函数，不执行源循环或查询证明来运行 guard。三元素数组中入口上界 8、第三次 store 改为 3 后合法退出的关键回退行为仍保持。

第三项是 [动态内存上界矩形](clight-loaded-rectangle-case.md)：行数是实际 memory load，列数是运行时 temp，两层通用 scan 在真实源前缀上建立安全。整行 non-alias 后才推进下一行，再缓存并实际交换动态循环。独立／统一入口各通过 6,248 次 C 调用／6,253 行输出；包含后续行 alias、上界增长／缩小和安全同对象单元。静态 stride／布局保持，尚不覆盖两个 memory-bound 维度或参数 stride 的同次组合。

第四项是 [共享出口生成](shared-guard-lowering.md)：原条件和局部规则不变，条件叶保存一个新的 private Boolean，候选／回退放到分派后各一次。共享编译入口通过同一 6,248 次调用，候选份数 156→1、回退 129→1，单 region 打印 body 332,491→61,039 字节。实际 raw temps 中的私有写入由 freshness、执行运输和公开观察证明处理，抽象只读证书没有被改成任意 effectful 检查。

第五项是 [只读探针简化](readonly-probe-simplification.md)：语言提供不透明探针的部分 Boolean 语义、同一入口结果确定性和实际编译／安全对应。框架用已执行测试的路径事实消除相同探针，保持原条件证书和局部 rule。矩形共享入口消费此接口，同一批 6,248 次调用通过；单 region 打印 body 从 61,039 降至 6,584 字节，语法 if 从 289 降至 45，没有运行性能结论。

第六项是 [运行时 stride 与内存上界组合](clight-loaded-stride-case.md)：固定 extent≤12 的数组枚举全部合法正布局，确认源活动路径才读取 stride，再复用模型的 alias 前缀／交换证明。候选继续使用参数地址，两入口各通过 68,368 次调用／68,373 行输出；源改变 bound、重叠行、空内层时 stride 未初始化和顺序修改 stride 均覆盖。独立入口共享出口，统一 pass 消费同一规则；仍不覆盖一般大布局或两个内存维度。

第七项是 [双内存上界的单次迭代消除](clight-dual-loaded-unit-case.md)：实际两层循环每次读取 rows／columns，检查只在源外层活动后读取内层上界，第一笔实际 store 再建立两项指针比较的安全性。两项 non-alias 通过后，候选仅执行一次写入并设置 `j=1,i=1`，保留完整出口。源进展允许回退时任意改变两个内存上界。独立／统一入口各通过 3,035 次调用、七处实际 region；两个上界共享只读单元可接受，alias 引发第二行／列的输入保留源结果。这是受限的双 preload／rewrite 实例，尚非两维动态数组调度。

第八项是 [双内存上界的实际数组交换](clight-dual-loaded-matrix-case.md)：逐点解码当前 store 和内层 tail，保留行后的外层 tail；当前点与两个 bound 都分离后才保持两个读取并前进。跨行时消费真实退出和外层增量，不预设整行稳定。`i=0,*rows=*columns=2` 时一个新鲜 cache 供两层候选头部使用，实际写序 `[0,1,2,3]→[0,2,1,3]`。独立／统一入口各通过 22,303 次调用和七处实际 region，包含共享只读 bound、两个上界的 alias 回退和顺序替换；GCC UBSan 无诊断。一般双动态内存尺寸仍未完成。

第九项是 [双动态上界的幂等写入化简](clight-dual-repeated-store-case.md)：普通常量零写入在第一次执行后不再改变 memory，两个上界的读取由 non-alias 保持；实际两层执行与出口对应已证明。接受 `i=0`、两个任意正 signed32 上界和两项分离，候选只写一次输出并设置 `j=*columns,i=*rows`，没有维度乘积检查或运行时源模拟。两入口各通过 3,035 次 C 调用；alias 将 bound 写成零时，源 counter=1 的出口得到保留。它展示一般正尺寸的另一种 conditional loop rewrite，仍不等于一般数组调度。

第十项是 [两个动态内存上界的矩形数组交换](clight-dual-dynamic-rectangle-case.md)：两个 runtime load 可以取不同的正尺寸，实际源游标逐点保持两项读取，整行接受后消费真实退出／增量才能检查下一行；两个独立 cache 供列优先候选使用。完整 Csem→Asm 端点已消费相同 readonly projected rule。独立共享入口通过 113,330 次 C 调用／八处 region，覆盖 12／4 与 6／3 两个静态布局、全部相应正矩形、alias 回退、共享只读 bound 和顺序改写。选择器 extent≤12，局部定理无此 cap；该阶段综合入口只预留一个 cache，尚未消费双缓存规则。共享候选／回退各一次，但检查 continuation 仍重复；主函数打印体 129,224 字节、413 个语法 if，尚无性能结论。

第十一项是同一双动态矩形的 [已验证探针简化](readonly-probe-simplification.md)：复用原 D／P、候选及局部证书，消除已经取得入口结果的重复表达式测试。相同 113,330 次调用通过；主函数打印体 129,224→14,234 字节，语法 if 413→69，alias 比较位置 248→48。接受域保持，没有运行时间测量，检查仍以树展开。

第十二项是 [综合入口的单／双缓存交替改写](clight-common-multicache-case.md)：保留旧规则优先级及直接 lowering，新矩形复用简化／共享 lowering，三槽 pool 在不同 region 复用。综合入口通过相同 113,330 次矩形调用；新的四处 macro region 程序通过 120 次调用／720 行输出，每次参数改变后重新建立检查和快照，保留完整数组与 counter。

第十三项是 [整段小步宿主与实际无限回退](clight-guarded-circular-case.md)。`open_region_protocol` 只要求零步匹配时下降索引，不要求原循环无条件有限。unsigned `i!=*bound`、每轮写 `i+2U` 的源在 out／bound alias 且入口非空时实际无限；源和 guarded 目标分别有 Clight `forever_silent` 定理。只读 guard 的定义性来自有限实际头部／首次 store 前缀，non-alias 接受后才保持 bound 并与缓存候选逐步对应。源／候选 AST 匹配真实 frontend 的 body `Ssequence Sskip` 和 signed `1` 自增常量，候选进展另以 unsigned 模距离证明，完整规则接到 Csem→Asm。

提取入口 `compile_guarded_circular` 先组合原 common region pass。540 次有限 kernel 调用／540 行输出同 GCC 和独立 unsigned 源模型一致；五个函数中六处完整循环已实际改写，混合函数还检查两处旧 payload preload，先后改变 parameter／bound 后分别刷新缓存。覆盖 UINT_MAX 附近 wrap、空 alias、null out 空路径、只读 bound、跳转前驱、嵌套外围和公开 counter／word。非空 alias 不原生执行，以实际源／目标无限执行证明及完整原回退覆盖。volatile bound、步长 2 和不同 body 被精确选择器拒绝。当前每处新树有一份 candidate、两份完整 fallback，不是共享 lowering 或性能结论。

## P0 验证记录（固定阶段）

| 层次 | 结果 |
| --- | --- |
| 语言无关接口 | 54 个端点闭合证明 |
| 真实 Clight 适配层 | 59 个端点，不超过既有六项假设基线 |
| 完整编译接口 | 401 个端点、862 份证明源码摘要；FRAGMENT=6、REGION=6、PROJECTED_REGION=8、STEPWISE=8、COMPILER=35，比较既有分层基线，没有新增全局公理 |
| 提取与执行 | 二十五种编译配置全部重建／回归通过，四十份原生报告核对当前证明、全部源码、提取 stamp 与编译器 |
| 本次兼容性 | 相对 `cf4d442` 保存的 39 份既有 C／Clight 摘要全部相同；新增 whole-loop fixture 单独核对 |
| 无限行为 | 实际源和 guarded 目标的 alias `forever_silent`，加整段局部／全局小步模拟；不以原生超时实验代替证明 |

复现入口为 `make interface-proof`、`make interface-clight-proof`、`make interface-compiler-proof` 和 `make interface-native-suite`，使用锁定的 CompCert v3.18、Rocq／Stdlib 9.2 工具链。检查使用 Rocq 编译和假设报告，以及实际提取编译器产生的程序同 GCC／独立模型比较。原生测试没有执行明确发散或源未定义的输入，没有测量性能。

新规则可单独以 `make interface-guarded-circular-native` 复现。报告见 `build/interface-circular-native/report.json`，P0 整体核对见 `build/interface-compiler/open-region-validation.json`；P0 证明报告 SHA256 为 `b67f8c308c486c785b4a6b5f6275003281e565f9f3b3a3641fe391bd17282030`。862 是该阶段证明源码摘要数，不是声称本轮独立编译了 862 个新模块；新宿主和相关接口实际编译，继承源码全部核对。

## 2026-10-06：P1 实际分派与安装复用

[clight_guard_realization](clight-guard-realization.md) 证明有限、E0、memory 不变的实际 dispatch prefix，以及私有名字 freshness 和 temp frame。direct 保持原 temp map；shared 仅在全部检查完成后写新鲜 Boolean。前缀定律不要求候选／回退完成；正常完成的宏宿主额外消费 `clight_normal_realization` 的分支执行运输。抽象 readonly condition 和 kernel 没有放宽。

原 direct/shared projected 安装现在调用同一个 `projected_realized_rule_region_contract`，复用原规则与条件证明；完整 unsigned 循环的空／alias／non-alias 路径另消费相同 direct dispatch prefix 后继续原小步协议。direct 没有新增 quiet-candidate 限制，shared 保留原 quiet/freshness 核对和 private-pool 分配。新接口已被三个实际编译证明路径消费；shared whole-loop 入口尚未安装，finite 宏宿主仍要求 source progress。

完整 Rocq 编译与审计通过 **411 个端点、863 份源码摘要**；继承 FRAGMENT=6、MEMORY=1、REGION=6、PROJECTED_REGION=8、STEPWISE=8、COMPILER=35，无新增全局公理。当前证明报告 SHA256 为 `8e0bf0664f0648c2e109762fe3621ce66edb8877964c5d84b604bc2aac366c9b`。**25 种提取配置全部重建／回归通过，40 份报告绑定当前证明、全部源码、提取 stamp 与编译器；相对 `26956a4` 保存的 40 份 C／Clight 摘要全部相同。** unsigned fixture 仍为 540 次有限调用、六处新 loop 与两处混合旧 preload；无限行为由实际 Clight 证明覆盖。整体核对见 `build/interface-compiler/realization-validation.json`，回归汇总见 `build/interface-compiler/realization-regression/summary.json`。

用户要求的 topdown narrative 方向已作为活动目标补充以 `26956a4` 推送；[三方责任／难点](framework-responsibilities.md) 对应每阶段验收。P1 接口冻结时再次 fetch 三个评审分支，SHA 均未变化。源码核对还发现 P2 的证书方向义务：旧 `encoded_private_rule`／named candidate compiler 交付实际 program globalenv 上的条件性 source-to-candidate 保持，不能直接声称已填入当前双向局部等价接口。P2 会复用其候选／模型／依赖证明，并为正确的证书方向完成主接口安装。

## 接下来如何判定进展

动态行数和列数的静态 stride 路径已达到这一阶段的实际编译验收。参数 stride 与 memory-bound 调度已在固定 extent≤12 的布局分派路径组合；双内存上界的单次迭代、一般正尺寸的幂等写入化简及固定 2×2 数组交换已接通；两个动态内存维度的静态布局交换也已通过独立及综合入口；后续优先处理多个依赖 preload、更大布局／一般指针缓冲区和双 loaded 与参数 stride 的同次组合；参数的有定义依据仍须从实际源的活动路径获得，地址／控制检查须消费已证明的宽化算术或范围证书，不能先预设完整稳定 footprint。

共享出口已消除完整循环体的重复，但检查树本身仍展开重复的后续检查。选择器继续用 extent 和保守成功叶预算拒绝过大树；实际 Boolean 路径事实已用于已验证冗余测试消除；后续可推进共享检查图或廉价、有定义的区间／仿射足迹。双动态矩形共享入口已消费现有探针简化，后续仍需一般共享检查图或更廉价的足迹证书。当前仍没有性能结果。

完整 Optimistic Loop Optimization 主线还缺旧 affine／tiling 到主只读接口的迁移、复杂 body 和更一般条件合成。新 helper、未消费的 schedule 或脱离编译器的模型不能充作通过。后续仍需完整程序端点、实际提取编译器和接受／回退／空域／机器边界的原生证据；研究新颖性另随已有工作比较校准。

上述整段无限回退验收已通过 [小步宿主](conditional-progress-host-design.md) 的这个具体实例。当前限制仍是同函数 `State`、label-free、正常公开出口和初始 quiet word 模板；没有由此得到任意内部调用／return 或一般 guarded affine／tiling 的全部行为覆盖。

本轮也读取并保存了三个固定评审分支，综合与逐项采纳见 [评审记录](review-synthesis-2026-10-05.md)。当前计划转向统一 direct/shared realization、真实 affine／tiling 的主接口迁移、一个受限符号化条件／足迹路径及有同版 CompCert 对照的性能测量，详见 [工作计划](current-work-plan.md)。原性能方案仍是 planned，JSON schema 已解析并核对内部引用，当前安装的旧版 validator 不支持 Draft 2020-12；没有冒充 schema 全验证或性能结果。
