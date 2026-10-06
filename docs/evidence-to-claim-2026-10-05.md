# GuardCert evidence-to-claim matrix（2026-10-05）

证据固定于 main `cf4d44292cd1e834e79db31d0ac3a75696a7d40c`，不随后续 main 漂移。文献复核日期为 2026-10-05；这是对五个指定近邻的定向复核，不是完整文献排除检索。本文区分已实现能力、可陈述的 artifact 结果和仍待建立的研究差异；“本项目新增证据”不表示世界上首次实现。

## 证据等级与信任边界

- **已实现／已证**：固定提交中的定义、生成器和端点支持此能力；本文阅读了 checkpoint、专门实例文档以及 `ReadonlyPrefixScan.v`、`ReadonlyProbeTree.v` 的定理正文。
- **仓库报告的回归证据**：调用次数、摘要和假设审计来自固定提交的记录。本轮没有重建 Rocq、提取编译器或重跑 native suite，不把记录复核写成独立复现。
- **可写的结果主张**：限定适用域地描述实际算法、定理和运行产物。
- **候选研究差异**：需同例比较、复用量化或进一步定理；不能写“首次”“通用地解决”。
- **工程证据**：接入、资源分配、支持模板与静态代码统计，能支撑可用性，不能独立支撑 novelty 或性能。

54 个语言无关闭合端点、59 个 Clight 端点、368 个完整编译端点及 850 份源码摘要是审计覆盖计数，不是独立创新数量。Clight／完整编译层继承显式分层假设，不能因“无新增全局公理”称整个系统无公理。24 种配置、39 份原生报告也不是 39 个互相独立的算法。端到端结论是 Csem→Asm **backward simulation**，不是任意 C 输入的双向等价；源 UB 不要求保留，明确发散或源未定义测试不执行。Rocq 提取、OCaml、运行环境等沿用既有信任边界。

## 五个最近邻：先固定其已覆盖的层

| 编号／工作 | 已有覆盖及核对位置 | 与 GuardCert 应比较的实际义务 | 本轮可以／不能下的结论 |
| --- | --- | --- | --- |
| N1：[CGO 2017 Optimistic Loop Optimization](https://pollylabs.org/publications/grosser-2017-Optimistic-Loop-Optimization.pdf) | §§4–6：假设组织、投影、简化、guard 生成；§4.6 讨论 alias 与 loaded bounds 的相互依赖；§6 Algorithms 1–2 处理检查溢出、源访问域和按需递归 preload | 数学条件到真实机器检查；安全读取的先后顺序；动态上界稳定性；实际源域与检查域的对应 | 不能以动态上界、安全 preload、处理循环依赖或简化条件为首次。GuardCert 可强调指定 Clight 实例及通用检查组合的机械证明链；不能据此声称算法覆盖或性能超过 Polly |
| N2：[COVE/cSTOKE，OOPSLA 2015](https://theory.stanford.edu/~aiken/publications/papers/oopsla15a.pdf) | 条件候选验证和前提推断；§5.5 动态检查／回退，实验检查为手写 C 编译后与候选汇编拼接 | 前提如何绑定实际检查、实际候选和上下文；GuardCert 有多少推断自动化 | GuardCert 的指定生成／安装链有机械证书，可作为与论文 §5.5 实验路径的具体区别；其任意 S/T 条件发现能力反而不能从当前模板推出 |
| N3：[CoreJIT，POPL 2021](https://www.o1o.ch/about/assets/courir.pdf) | §§3.3.2、3.3.5、4：安全 Assume 插入、位置分析、优化和去优化的机械证明 | 安全域从何处取得；入口 staged checks 与 source-prefix witnesses；宏区域快路与回退行为 | 安全 guard、动态前提和位置合法性已非空白。当前 AOT 入口版本化与 CoreIR 活动执行恢复具有不同契约，不能把省去去优化写成更一般 |
| N4：[Chamois，OOPSLA 2023](https://doi.org/10.1145/3622799)；[作者海报](https://www-verimag.imag.fr/~boulme/pub/poster_OOPSLA23.pdf) | 关系不变量、oracle 目标 CFG、块符号仿真、可扩展重写和 CompCert 连接；作者材料展示循环优化／调度 | 运行时检查子程序能否由其现有块关系验证；生成器是否仍须新增定义性／源路径接口 | 只能确认上述正面覆盖。本轮全文 HAL 被访问保护阻挡，当前 oracle 文档也未取得；不把未读到的 guard generator 写成不存在 |
| N5：[Peek，PLDI 2016](https://darzu.io/files/pldi2016.pdf) | §§3–4：局部仿真、源 normalization、活跃性和全程序提升；发布接口有等长、无 call/return 等限制 | 终止／进展、控制出口、scratch／公开观察；带 guard 的较大片段如何满足其契约 | 动态循环宏区域不等同于已展示的 peephole 集；但库／插件和局部到全局均已有先例，不能断言 Peek 原理上不能接带 guard 的规则 |

这些比较是针对发表版本和本轮实际取得的材料。特别是 N4 的空白表示**未核实**，不是能力否定。N1 的 Algorithms 1–2 已直接预见依赖读取和安全访问问题，故源前缀路线的定位必须落在机械化证据结构与可复用接口上。

## 10 月 5 日的十二项能力逐项校准

每行“升级条件”是把已完成 artifact 结果升级为有说服力的研究贡献所需的证据；并不否认当前定理已成立。

| 已实现能力／证据入口 | 具体语义或工程义务 | 最近先例覆盖 | GuardCert 新增的可核对证据 | 不能单独当 novelty 的部分 | 升级所缺实验／定理 |
| --- | --- | --- | --- | --- | --- |
| 1. [loaded bound 的 2×2 交换](clight-loaded-matrix-case.md) | 源每轮 load，alias store 可改 bound；检查通过才允许缓存、重排；保留 i/j 公开出口 | N1 的 loaded 参数与 alias 联合检查；N4 的调度验证基础 | 按实际第一行证据建立第二行检查安全；alias 反例回退，668 次调用分别通过独立／综合入口 | 缓存上界和交换本身；固定四单元模板 | 同例列出 N1 生成检查所需事实与本例 discharge；扩展到多动作 body，量化规则证明负担 |
| 2. [generic readonly prefix scan](readonly-prefix-scan-interface.md) | active 的两种结果分别给证据；point 接受才推进入口上的 ghost invariant；检查有限、只读且有定义 | N1 §6 源访问域／按需读取；N3 guard 安全；N5 进展义务 | `synthesized_prefix_scan_condition` 通用证明；indexed 编译入口实际调用；生成树与原手写树相等，证明信息擦除 | fuel 展开、短路与 ghost invariant 方法本身；此次迁移未扩大 indexed 接受域 | 第二类非同构使用者；证明 fuel／枚举覆盖源访问（核自身只证有界前缀）；统计使用者专属 witness 与复用代码 |
| 3. [单 loaded 动态矩形](clight-loaded-rectangle-case.md) | 当前行 stores 取得权限，整行接受后才能推进实际 outer tail；不能预设未来行有效 | N1 非静态尺寸和安全检查；N4 循环关系 | 两层调用同一 scan，实际源 tail 与权限运输接到候选／端点；两入口各 6,248 次调用 | 增加一个维度、嵌套枚举；仍为静态布局 | 同例比较“直接假定稳定 footprint”会遗漏何义务；一般布局、读写依赖与规模测量 |
| 4. [shared-exit lowering](shared-guard-lowering.md) | 抽象只读检查变为真实 private Boolean 写入；freshness、scope、执行／continuation 运输；候选 quiet | N4 块关系／改写组合，N5 私有位置／公开观察提供近邻基础 | 原 D/P 和局部规则复用；候选 156→1、回退 129→1；单 region body 332,491→61,039 字节 | 共享分派／避免复制是常规编译工程；没有普遍体积或时间结果 | 独立的共享图／代码规模界；测编译内存、最终 Asm 字节、检查与运行成本；证明适用限制为何必要 |
| 5. [readonly probe simplification](readonly-probe-simplification.md) | 探针允许未定义；只用已执行的同入口确定结果；不能提前触及危险分支 | N1 §5 条件简化，N3 安全检查，N4 符号重写 | `simplified_probe_tree_run` 双向结果对应、`simplified_probe_tree_safe` 安全保持、同 D/P 新证书；61,039→6,584 字节，289→45 if | 重复测试消除；语法相等不等于关系推理；不是 DAG | 对定义性敏感反例作消融；测检查次数与最终机器代码；与一般 CSE／已有 validator 的接入义务比较 |
| 6. [loaded bound + 参数 stride](clight-loaded-stride-case.md) | source 活动路径才赋予 columns/stride 定义性；temp↔常量布局运输；实际地址不回绕 | N1 布局／整数／preload；N4 关系运输 | extent≤12 枚举全部合法正布局，`loaded_stride_product_bound` 对应数学乘积界；候选仍用参数地址；各 68,368 次调用 | 有限布局分派、更多模板；不是无界动态布局算法 | 双 loaded 与参数 stride 同次组合；一般 buffer、宽化算术或廉价足迹；规模及接受率损失曲线 |
| 7. [双 loaded 单次迭代消除](clight-dual-loaded-unit-case.md) | 外层活动才 load 内层；首 store 才给两个指针比较依据；回退可改变任一 bound | N1 递归 preload，N2 条件候选 | 两项分离证据、完整 counter 出口、共享只读 bound 接受；各 3,035 次调用／七 region | 受限双 preload 和 unit rewrite；不是双动态调度 | 依赖 load（如基址或地址由先前 load 决定）及依赖顺序生成；复杂 body |
| 8. [双 loaded 固定矩阵交换](clight-dual-loaded-matrix-case.md) | 每点保持两 load，内层 tail 与行后 outer tail 分开；跨行不能先假定稳定 | N1 alias 与 bounds 联合处理；N4 调度 | 实际 2×2 写序交换，两个 bound alias 回退、共享 bound 与顺序替换；各 22,303 次调用／七 region，UBSan 无诊断 | 固定矩阵和单 cache 的特例能力 | 不依赖尺寸相同的两快照与一般尺寸（第 10 项已部分补上）；仍需多动作与一般布局 |
| 9. [双动态幂等 store 化简](clight-dual-repeated-store-case.md) | 第一次零写后 memory 幂等；non-alias 保持两 load；任意正 signed32 尺寸的终止 counter 对应 | N2 条件候选；N4／N5 局部执行及出口义务 | 两入口各 3,035 次调用；局部证明覆盖任意正尺寸，无乘积 guard／源运行模拟；bound 被写零的回退出口保留 | 幂等写消除；大数值维度不等于复杂访问族 | 与调度实例分开统计复用；一般幂等动作／多语句，证明模板选取和接受完整性 |
| 10. [双动态 loaded 矩形交换](clight-dual-dynamic-rectangle-case.md) | 不同行列值；逐点两 load 稳定性和权限运输；整行完成后推进；两个 cache 独立 | N1 已处理 loaded 尺寸与 alias 互依；N4 块仿真 | 两层同 scan，真实 stores 和 tails，不预设完整稳定 footprint；完整端点，113,330 次调用／八 region | 两维和两个 cache 本身；静态布局、单 affine store、selector extent≤12 | 参数 stride 同次组合、多个依赖 preload；一般 pointer buffer／body；检查覆盖与性能，不以 local theorem 无 cap 掩盖 selector cap |
| 11. [双动态检查简化](readonly-probe-simplification.md) | 后处理复用同 D/P、原候选与局部证书，不改变接受语义 | N1 条件简化；N4 可扩展重写 | 同第 5 项通用算法第二个实际使用者；113,330 次调用，129,224→14,234 字节，413→69 if，248→48 alias 位置 | 实例上的静态体积缩小；不代表总体编译加速、运行加速或最小 guard | 多布局规模实验及 direct/shared/simplified 消融；共享 continuation DAG、成本界 |
| 12. [综合入口多 cache 组合](clight-common-multicache-case.md) | 每个 region 当前入口重新检查／preload；三 private slots 跨不重叠 region 安全复用；旧选择优先级保持 | N4 变换组合，N5 上下文提升，N3 多 pass 正确性 | `common_region_selection_sound`、`transform_common_regions_correct` 和完整端点；矩形 113,330 次及四 region 交替 120 次／720 行 | 三槽 pool、选择优先级、更多配置；多 cache 不是首个多次优化 | 资源需求自动计算、干扰／嵌套 region、更多插件组合；单次 contract 到组合的证明负担量化 |

第 1、3、8、10 项形成逐步增大的实例族；第 5、11 项是同一简化算法复用；不能把十二项计成十二个独立贡献。两个 bounds 指向同一只读单元不等同于多个**依赖** preload。第 6 项和第 10 项分别完成，不等同于二者的同次组合。

## 三个争议定位的判断

| 表述 | 当前判断 | 有效的研究差异应该如何建立 | 可安全使用的措辞 |
| --- | --- | --- | --- |
| 工作在 C／Clight 层 | 当前首先是实现与语义宿主选择，不能独立做 novelty。N1 已讨论 C 与 LLVM 的差异，Clight 也不是未经简化的全部 C | 展示该层保留了什么事实、减少何种 metadata／运输义务、增加何种控制／类型义务；同一例在低层 IR 的证据对照，不以 IR 层级替代能力比较 | “在 Clight 真实整数、指针、load/store 和控制语义下实例化，并连接 CompCert 后端” |
| generic guarded kernel 与语言 host adapter 分离 | 现为经过实例化的模块化设计结果；一般抽象／插件／宿主分工已有 N4/N5 等先例 | 给出非同构第二宿主或另一语言的实际实例，比较新增语言定律和每条规则证明量；显示 scan／simplifier 不重复证明，列 adapter 必须交付的执行、安全和观察定律 | “核不解释具体内存／算术；Clight adapter 证明实际 dispatch 和上下文对应，已有设施在多个实例复用” |
| 真实检查定义性与源路径前缀证明 | 最值得发展成研究贡献的具体证据结构，**不是已确认的文献空白**。N1 §6 已要求源域与安全 preload，N3 已证安全 guard | 用同例明确比较：仅当前源点的 witness 如何足以生成后续入口检查？局部 non-alias 如何解开权限与稳定性依赖？是否有可复用生成算法、覆盖／接受定理和更少专属证明？ | “在已支持模板中，从实际源剩余执行逐点建立检查安全，接受后运输 load 稳定性和候选执行，无须在入口先假设整个 footprint 稳定” |

第三项的逻辑关键是：入口域 D 可以携带宿主从真实源执行取得的依据，但不能偷偷包含希望检查的 P。W(c,s) 是入口 s 上关于源剩余执行的 ghost assertion；guard 始终在入口内存求值，既不执行源循环，也不动态查询权限证明。检查已证有限、只读、可用且接受可靠；拒绝不意味着 ¬P。源 permission witness 不等于可运行的通用 permission 检查。

源独立 progress 仍是当前**宏片段宿主**的义务，不能在建立 W 时省略。逐步求值宿主可以位于可能无限的外围循环中，但不能据此声称整段发散回退已经支持。仅在 P 下要求 progress 的宿主仍是待证设计。

## 论文主张应怎样分配

| 层次 | 现在可写 | 还不能写 | 升级门槛 |
| --- | --- | --- | --- |
| C1：检查构造与后处理 | 有界 source-prefix scan、部分探针语义下的结果／安全保持简化、Clight 实例的真实共享 lowering | 任意条件合成、最弱／最小 guard、首次安全检查 | 列出精确定理、域和作者义务；对 N1/N3 同例比较，并量化复用 |
| C2：语义实例 | 对指定 memory-loaded bound／alias／stride 模板，在实际源证据上建立检查安全、快照和交换正确性 | 任意 Clight 区域、一般 buffer／依赖 preload／复杂 body；所有发散行为的宏片段重写 | 补齐主要组合缺口，增加性质不同的动作；清楚区分 selector cap 与 theorem 域 |
| C3：完整安装链 | 已实例化规则进入实际 Csem→Asm 端点，综合 pass 消费单次契约，原生回归覆盖 alias、空域和公开出口 | 首次局部到全局／首次 verified compiler 接入；以端点数推断研究价值 | 与 N4/N5 接口同例尝试复用，报告仍需增加的证据及限制 |
| C4：效果 | 指定打印 Clight fixture 的体积／语法数缩小，以及报告的行为回归一致 | 运行时收益、最终二进制缩小、实际接受率；通用可扩展性 | 真实分支计数、guard 次数／时间、最终 Asm／binary、编译时间／内存，多尺寸消融与现实 kernels |

最优先的三组实验／证明不是再堆小模板：
1. **同例语义对照**：以 alias 可改变 loaded bounds 的矩形和空外层的未定义内层参数为基准，对照 N1 Algorithms 1–2 的域／preload 义务及 N3 guard 安全；尝试将生成的检查／候选交给 N4 接口，而非假定它无法验证。
2. **复用与成本消融**：direct、shared、simplified 三种路径，固定源与 D/P；统计通用／adapter／实例证明、作者手写 obligations、构建成本、最终机器代码和 runtime guard 开销。现有调用数只作为回归，不作速度分母。
3. **边界推进**：双 loaded + 参数 stride、多个依赖 preload、一般 buffer 或多动作 body，选一项给出精确支持域和拒绝策略；或者完成 conditional-progress 宿主并证明真实可能发散回退。避免同时扩展所有方向。

## 可直接替换 research-position.md 结论的修订稿

截至 2026-10-05、固定 main `cf4d442`，GuardCert 已不止是“连接条件仿真、guard 与上下文”的可行性原型：它具有实际被提取编译入口消费的只读前缀扫描、部分探针语义下保持结果与安全的条件简化、保持原规则证书的共享出口 lowering，以及单／双 memory-loaded bounds、有限参数 stride 和多 cache 的真实 Clight 使用者。最具体的证据是：检查不预先假定完整稳定 footprint，而从实际源剩余执行取得当前点的定义性与权限依据，仅在已完成 non-alias 检查后运输 load 稳定性并推进下一点；接受后才执行缓存或调度候选，拒绝时保留真实源片段及其公开出口。相同设施已经连接完整 Csem→Asm backward simulation 和原生行为回归。

这些结果支持一项限定范围的 artifact 主张：**GuardCert 在已支持的 Clight 模板内，机械连接源路径提供的检查依据、有限只读条件生成及安全后处理、条件性局部变换和真实宿主安装，并复用其检查及上下文证书。** 它们尚不自动支持文献新颖性。CGO 2017 已有假设组织、简化、检查生成与安全／依赖 preload；COVE/cSTOKE 已有条件候选验证和动态回退；CoreJIT 已机械证明安全 guard 插入与去优化；Chamois 和 Peek 已覆盖不同形式的局部验证与全程序连接。C／Clight 层、generic kernel／host adapter 分工、动态前提、安全 guard、共享出口和多次 pass 组合均不能单独作为首创依据。

当前最值得检验的研究差异是：**如何把真实源路径逐步提供的定义性、权限与稳定性证据组织为可复用的检查构造接口，并在保持部分求值安全的同时复用原条件规则证书完成生成、简化和 lowering。** 这是已有算法和机械证明边界之间的具体比较问题，而非已证实的空白。需要以同一个 alias-sensitive loaded-bound 例子对照 CGO／CoreJIT 的义务，并直接核对 Chamois／Peek 可复用的接口；后者未核实的部分必须标为未知，不能据此声称缺失。

现有边界必须同时保留：宏片段宿主仍要求源独立进展；有限求值宿主不代表一般发散宏片段已覆盖；双动态矩形选择器要求 extent≤12、静态 stride 和受限 body；loaded bound 与参数 stride 的有限组合不能推广成双 loaded 与参数 stride 的一般同次组合。一般 buffer、多个依赖 preload、复杂 body、旧 affine／tiling 到主只读接口迁移和更一般条件发现仍未完成。共享出口与探针简化已有指定 fixture 的静态 Clight 体积结果，没有运行性能或普遍代码规模结论；审计记录说明未增加全局公理，但沿用既有假设和工具链信任边界。

因此，定位应从宽泛框架愿景改为上述**已实现的证据处理算法与真实语义实例**，并把“可复用源路径证据是否降低证明负担、是否能以可接受成本扩展优化覆盖”保留为待验证的研究主张。若同例比较表明这些义务可以通过已有接口直接得到，项目仍有经过验证的工程价值，但应继续寻找具体增量，不将未验证的覆盖或首创写入论文。
