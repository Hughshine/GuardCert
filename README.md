# Guard：带前提的程序变换与组合证明

[CAV 2027 稿件](paper/README.md)已按 narrative `271f6fc` 开始并行写作：实际 LNCS
introduction／related work／framework 初稿，以及 case-study／evaluation 的证据与待验收项。
写作跟随真实源码和证明边界，不等待所有后续扩展，也不预设性能收益。

[最新单份扫描与较大域](docs/nested-stability-shared.md)已证明 initialized cache
comparisons 的 eager conjunction，备用 scan 仅生成一份；interchange 函数
762→644 bytes，原 762 次汇编调用及接受结果保持。Word=15／count≤16 的实际
C 又通过 60 次汇编调用、45 次 Clight 分派和九个真实写序 probes；两种 header
alias 下的交换／tiling 与改变 bound 的回退均得到区分。独立 23 端点／598 依赖
审计和提取通过，kernel／原候选／语言 host 保持。稳定性地址查询 2,560→0 加
两次缓存比较，但 numeric 等工作仍在；完整成本、static condition derivation、
更广源类及完整 BT／动态布局继续推进。当前工具使用独立 shared 报告目录。

[前阶段 same-word compiler](docs/nested-stability-compiler.md)已把同值 BODY 保持
接入 actual physical guard、multi adapter、typed factory 与完整 Csem→Asm。
语言证明 store／check／frame，domain 生产 canonical execution，kernel 消费证书，
原 candidate 与语言 host 证明直接复用。新条件接受时跳过 stability scan，其他
路径保留旧 scan；不同常量／未支持 BODY 保守使用原 guard。独立 19 端点／597
依赖审计、提取、762 次完整汇编调用、381 次 Clight 分派和四个真实汇编 alias
探针通过。旧／新同输入对照新增两次 fast dispatch；一组稳定性查询由 40 次地址
比较变为两次缓存比较，完整函数由 613 增至 762 bytes。完整 guard cost／计时、
更广条件及作者工作仍待验收；完整多面体目标 active。
`make -f scripts/nested_stability.mk validate`
核对独立证据。以下旧阶段保留各自当时范围，当前能力以最新 checkpoint 为准。

[完整原源 header-stability guard](docs/nested-constant-physical.md)已把 checked site、
实际 helper 准备和完整 outer scan 接起来；接受后取得 canonical Clight 与真实
Loop source 执行，并明确保留 model entry 到 actual guard exit 的 frame。
39 端点审计通过，kernel／旧 compiler 保持。安全域是原源 silent normal
completion；candidate 跨入口、dependency/alias guard、typed host 与 progress/
divergence 安装仍待完成。没有新 compiler／native，Figure 2 优化仍未安装。

[原 AST checked site 与实际 entry](docs/nested-constant-site.md)已从 proposer 数据
检查 source、scope／private names、旧 affine package、scan namespace 与 lowering。
实际 row gate 去掉额外 row=0 context 假设；接受后的域、word view、raw observers
及原 prefix 锚定到真正检查后状态。Guard AST 只依赖 observer 地址表达式。
37 端点独立审计通过；完整 physical guard 后继见上段，候选 factory 和
host 安装仍待完成，没有新 compiler／native，Figure 2 原 C 优化仍未安装。

[原嵌套源的 capture／numeric 输入生产](docs/nested-constant-numeric.md)已从实际首次
leaf 取得已用参数定义性，运行有序 capture 和两层短路 gate；numeric 接受直接
生产 outer scan 所需的逐点整数域及 word view。BODY 专用参数的 checked package、
参数未定义时的空外层／内层实际拒绝均已证明。24 端点独立审计通过，没有新增
semantic callback，kernel／旧 compiler 保持。Checked entry 后继见上段；完整
physical guard、candidate factory／host 仍待连接，没有新 compiler 或 native。

[完整三层 canonical model](docs/nested-constant-model.md)已将合法双缓存源接到
旧 affine AST，并从 checked package 取得真实 Loop 内存执行；没有新增
source/model 语义回调。12 端点审计通过，kernel／旧 compiler 保持。
Capture／numeric 后继见上段；原 AST factory／候选／host 仍待连接；
此阶段没有新提取或 native，Figure 2 适配源的优化尚未安装。

[Outer 短路扫描与双缓存源](docs/constant-joint-outer-scan.md)已消费 inner producer，
整段接受生产全部 rows／columns 的观察保持，实际取得原源与双缓存源的相同出口
temps／memory。第一行拒绝停止 outer，空 outer 不要求 child／output receipt。
14 端点／565 依赖审计通过，kernel／既有 compiler 绑定保持。完整 canonical 模型
后继见上段；原 AST factory／候选安装与新 compiler 仍未完成，没有新 native。

[Inner 短路扫描及整行接受](docs/constant-joint-inner-scan.md)已接到真实 Clight loop：
每个 column 从原源 prefix 取得 BODY 许可，接受后推进；整行接受生产所有 column
的观察保持及下一 outer prefix。首次拒绝不递增扫描游标，空 child 无需 output
receipt。该阶段没有新 native；实际 outer loop／缓存源的后继见上段，完整模型
和新 compiler 仍待连接。

[已到达常量子循环的 joint scan](docs/constant-body-joint-scan.md)现已从原 BODY 的
访问权限许可真实写地址与 `shape`、`shape+1` 的比较；接受后保持全部 raw
observations，生产 inner source-prefix 的推进证据。30 端点审计通过，具体
Figure 2 BODY 证明完整五次原 store 和检查执行，同 block 分离接受、重叠拒绝。
其 inner/outer 扫描后继见上两段；canonical model 和原 AST 安装仍待连接，没有新 native。

[常量子循环的模型／权限桥](docs/constant-bound-model.md)已把原 `<5` 子循环执行接到
canonical affine decode 和 guard-entry point capabilities；private helpers 有实际准备
和原 source public transport。该前阶段的 14 端点审计保持；joint BODY 消费者已由
上段连接，整段模型与原源 factory 仍待完成，Figure 2 的优化尚未安装。

[第二个 loaded header 的服务](docs/nested-header-services.md)已证明 conditional child capture、保持实际 memory 的层次源前缀、保护全部观察后的双缓存源运输，以及不假设 cached-source completion 的 numeric probe。48 端点审计及真实 indexed child、changing-bound 拒绝、相邻 word 接受／prefix 推进通过，旧 compiler／native 绑定保持。完整 loaded-child scan、canonical model 和 factory 尚待接入；本阶段没有新提取或汇编调用，Figure 2 仍记未支持。[交付与后续验收](docs/research-checkpoint-2026-10-06-nested-headers.md)列出证明边界。

[Loaded＋offset 根的完整接入](docs/research-checkpoint-2026-10-06-loaded-offset-affine.md)已把真实 `i<*limit+1` 的安全捕获、raw observation 保持检查、缓存源运输与旧候选验证接到新 factory／signed-expression host 和 Csem→Asm 入口，并提取运行。56 端点审计、六配置 708 次汇编调用、236 次 Clight 分支调用和 21 个机器路径通过；alias 回退保留实际提前停止，短源拒绝后不检查未来地址。任意有限层 canonical affine children 可使用此根，但 Figure 2 的 loaded child 仍未接通；扫描成本与 compact 条件仍需改进。[接口 walkthrough](docs/loaded-offset-affine.md)区分框架、语言与优化实现者的责任。

[当前 guard 简化](docs/research-checkpoint-2026-10-06-loaded-affine-reduced.md)已证明稳定性接受后运输 numeric／first-path 事实，删除 alias 阶段的重复检查；候选前提、局部证明、语言 host 和 kernel 保持。35 端点／694 依赖／1,023 源摘要审计、独立提取、624 次新 assembly 调用、208 次 Clight 路径调用及 21 个机器路径探针通过。三轴 accumulator 的完整函数 896→782 bytes，多数组 2,061→1,936；没有计时收益结论。四个机器工作量探针确认 pointer comparisons 仍分别为 46 和 6,394，逐点／逐点对成本未消除。[OLO Figure 2 适配例](docs/olo-figure2-coverage.md)另有 16 次原生调用保持原行为，但当前未安装优化：load＋1 根和 loaded child 的组合仍是具体源覆盖缺口。

前一 native 阶段的当前 `.vo` 绑定因本次 guard 简化而失配，旧报告／二进制原样保留。当前验证入口是 `make loaded-affine-multi-validate`，使用独立 reduced proof／build／native 报告；旧产物只用于已核对摘要的代码规模与工作量对照。

[Deep＋loaded multi 的可运行编译器](docs/research-checkpoint-2026-10-06-loaded-affine-multi-native.md)已闭合当前范围的真实 C→检查→候选／原源回退→完整编译链。提取入口处理两／三层参数化循环、多数组读写、真实依赖和同函数两次改写；六配置共 624 次新 assembly 调用、208 次独立 Clight 路径调用和 21 个未修改汇编的路径探针通过。循环交换／2×3 tiling 确实改变访问顺序，同 block 分离切片接受、部分重叠和改变 bound 的别名保留原回退；短数组例确认 guard 不比较未来未获许可地址。真实运行发现并修复了 cache 与候选 counter pool 的冲突；独立 32 端点／692 依赖／1,021 源摘要审计及旧 42 项假设回归通过，最小 kernel 不变。检查成本与收益尚未测量，下一阶段推进紧凑 entry 条件及 CGO 2017 同例对照。

[前一递归 body domain 证明](docs/research-checkpoint-2026-10-06-loaded-affine-body-domain.md)从原 loaded source 生产参数 word view，并从当前完整 body 生产递归模型执行、各点物理许可和 private cursor 的实际地址比较域；写 trace 对应证明将点写分离推成 body 的 bound 保持，允许 reads alias bound。25 端点／674 依赖／1,001 源摘要审计通过，既有 body／numeric／compiler 对象保持。本段保留前阶段验证范围；完整检查与缓存源连接见上段。

[Deep＋loaded 的 numeric guard 接入](docs/research-checkpoint-2026-10-06-loaded-affine-numeric.md)已从真正原 loaded 源生产 first-path receipt 和安全 private capture，复用既有递归 affine numeric guard 及当前证书接口；不以完整缓存源执行或未来稳定性许可检查。五个新 `.v`、25 端点／660 依赖／987 源摘要审计通过，零次迭代时未定义 child 参数及 body pointer 的实际 Clight 检查也有具体 memory 见证。此阶段接受只证明 numeric math domain；深层 physical stability scan、候选和全程序安装仍需继续接入，没有新增 compiler／native 能力。

[最近可运行的 deep affine compiler](docs/research-checkpoint-2026-10-06-materialized-affine.md)把已有递归 affine 源、真实单／多指针 body 和候选 checker 接到当前 kernel：Clight 提供正常返回的私有 Boolean check、安全／分派／状态运输及程序安装；domain 复用源／模型与候选证明。新的 Csem→Asm 入口、26 端点审计、提取和十二配置共 5,118 次 assembly 调用通过；四组实际 Clight 插桩另核对接受／fallback、物理 alias 和条件读取。最小 kernel 没有改动，[接口说明](docs/clight-materialized-check.md)列明使用者责任和限制。

当前主入口组合 canonical 递归 affine children 与单个 repeated-load `*bound` 根；另一两层 dependent cursor 路线处理 `**root` header／多观察稳定性。任意深度 dependent loaded headers、typed pointer-store body、独立计时及同例 proof-burden 比较仍未完成。共享 `.vo` 重编后旧冻结 cursor 对象摘要失配，当前消费者独立重编／535 依赖审计通过，42 项假设保持；旧编译器和 native 报告保持历史记录。以下阶段各按其保存时的验证范围阅读。

[循环化 dependent guard compiler](docs/research-checkpoint-2026-10-06-cursor-dependent-compiler.md)已把完整双观察扫描降低为两个实际私有 cursor 循环，连接真实 source package、mapped／tiling／schedule factory、完整 Csem→Asm 定理和提取。八个新模块、43 端点／537 依赖／976 source 摘要审计通过；完整 compiler 保持原 42 项假设，kernel 没有改动。两个真实 affine C 域共 444 次新入口调用、28 个 store-order 探针（含两个旧入口对照）及 18 个新 guard comparison 探针通过。默认 64×64 cap 的完整 Clight 函数从 20,710／20,711 个 if 降为 111／112，打印体约 13 MB→25 KB；linked 函数 72,083／105,857→879／916 字节。计时和性能收益仍未测量。

[上一依赖 header 编译器](docs/research-checkpoint-2026-10-06-dependent-compiler.md)从真实 C 的 `i<**root` 识别原源，安全捕获 private pointer／bound，再接实际候选和原 compound-load fallback。其 40 端点、提取及两个域 444 调用保留为独立历史证据。本阶段复用其 source／model、全部 footprint coverage、观察保持、候选 certificate 和语言 host；实际 guard cursors 与 candidate counters 分开，新的 typed private pool 为 21 槽。旧 compiler／native 摘要绑定复核通过，未重跑或累计旧矩阵。

这次接入沿 topdown `7d94d81` 的澄清：最小 kernel 止于局部 guarded correctness，条件处理／prefix scan 是上层库，完整程序安装属于语言 host。语言证明安全 captures、短路循环与私有状态运输，domain 填入实际 header／body 解码、reached-write receipts、全部 point／row 覆盖，并证明新 lowering 对应原 condition。guard 不预置未来稳定性，拒绝后保留原 `**root` 源的提前停止与公开 marker=123。仍要求源已有 body-pointer receipts；合法 pointer-store body、一般深层 affine 源、不同 body base 的 alias 接受、P4 和同例证明负担比较继续作为未完成项。

[上一 private bound snapshot 编译器](docs/research-checkpoint-2026-10-06-affine-private-loaded.md)保留为独立历史证据：单个 `*bound`、无公开 bound 快照，两种 affine 域共 444 调用／28 机器探针。新 dependent 入口复用其底层条件、candidate checker 和 preparation 库；本轮旧矩阵未重新验收，不计作 dependent 运行结果。

[更早的顺序 plan 阶段](docs/research-checkpoint-2026-10-06-affine-planned-loaded.md)保留为独立证据：已有 public snapshot 的三角源六配置共 222 调用、十三个机器探针，含默认 64×64 caps。其 private snapshot 后继委托整个 factory；最新 dependent 入口扩展 capture／typed pool／progress 安装，共用底层 plan 与候选 checker。各阶段的旧矩阵分别保留，不累计为最新运行证据。

此前[参数化 loaded-bound compiler](docs/research-checkpoint-2026-10-06-affine-loaded-compiler.md) 已从真实 C 识别源 snapshot、不同变量名的三角域和 `j<2*i+1`，将 mapped、schedule、2×3／4×1 tiling 接到 staged guard、真实原 loaded fallback 和 Csem→Asm。其 47 端点审计、十一配置共 1,650 调用和七个机器探针保留为独立历史证据，bound 是写缓冲区单元 0；本次没有重跑该矩阵。[context 评审](docs/clight-boundary-contract-review.md)和[三方验证责任](docs/framework-responsibilities.md)继续约束实现与主张，完整 goal 保持 active。

早期 [loaded source placement](docs/research-checkpoint-2026-10-06-loaded-placement.md) 证明不假设 bound 稳定的 nested progress，组合原候选 checker、保留 prefix/suffix 的 contract、完整 Clight 安装与 Csem→Asm。语言协议允许 body 改变 memory bound；缓存合法性由独立 domain 证明。当时的固定 optimizer 标识符、真实 frontend、提取及原生缺口已由后续阶段关闭；该记录保留其历史验证范围。

研究问题：如何把片段变换所需的语义前提处理为可靠证据或安全的检查代码，并复用条件正确性证明接入完整程序？首条实现主线是以 PolCert 为功能参照，在顺序 CompCert 中实现有动态前提的多面体变换，采用入口检查与原片段回退，并获得完整程序的行为保持证明。允许按 CompCert 机器语义重实现表示、算法和证明；验收要求是基本功能与证明能力对齐。通用框架通过语言接口实例化。旧 affine／tiling 路线的统一 C→Asm 入口支持动态矩形、`j<i+M` 的非矩形源、多个实际数组对象及跨数组读取／复制；消费实际依赖证书的仿射候选、组合坐标映射和二维 tiling 已接通源执行、运行时检查、候选执行及完整程序定理。一般仿射 Loop 的提取执行对应也已证明。单个稳定指针缓冲区及指针／固定数组中的稳定 RHS 标量参数也已接入。正、负及混合系数的仿射源地址随后也已接通，见 [signed 仿射地址](docs/memory-signed-affine-access.md)。[多个不同指针的活动访问分离检查](docs/memory-multiple-pointer-guards.md)也已接通源与候选的真实执行及完整程序定理，支持同一 block 中的切片。这些旧路线能力尚未全部迁移到主只读接口；更一般的深层仿射域、参数化访问及更宽的别名前提继续推进。具体缺口与验收要求见 [多面体接入目标](docs/polcert-integration-target.md)。

当前语言无关前台见 [guarded rewrite 使用者契约](docs/guarded-rewrite-contract.md)：用户选择片段、候选及位置，框架提供只读条件、条件性局部等价、effect／frame 证明设施和上下文等价组合。循环与多面体变换是主要实例。新的[独立接口原型](prototype/interface/README.md)已编译验证，包含别名下的有限循环重排、前提入口推导和多次替换组合。[Clight 接入设计](docs/clight-guarded-rewrite-design.md)已有真实只读检查、延迟读取原子的公式合成及写 frame 接口；分支 rewrite、2×2／动态矩形 store、读写更新、保留行内依赖的循环交换和 non-alias 单元写入交换均已消费新 API 接到完整 Csem→Asm 定理，并提取编译器运行真实 C 程序。动态矩形范围已连接模型文本位置义务和实际机器地址表示；候选私有出口的投影已通过 freshness／scope 宿主接到完整编译，并有实际 C 例子；[普通参数 load 的循环提升](docs/clight-stable-load-case.md)也已消费单元 non-alias、前缀不变性和私有快照，运行 727 次实际 C 调用。[内存循环上界](docs/clight-loaded-bound-case.md)也已接到完整定理并通过 514 次 C 调用，源进展独立于稳定性；普通 load 可进入带证书的 Boolean 检查树。[运行时 stride](docs/clight-runtime-stride-case.md) 的实际二维纯写交换也已接通，345 次调用／九处 guard 通过；源和候选保留参数地址，64 位乘积检查自身的精确性已证明。[有界 indexed 写足迹](docs/clight-indexed-load-case.md) 下的参数 load 提升又通过 1095 次调用，支持同对象安全单元和部分重叠回退，默认检查上限 16。[源前缀安全的 indexed 内存上界](docs/clight-indexed-bound-case.md) 又组合这两类能力，1079 次调用／2154 行输出通过；检查安全不预设完整稳定 footprint，三元素数组中上界从 8 变成 3 的合法源行为得到保持。[内存上界与二维 2×2 调度](docs/clight-loaded-matrix-case.md)已在同一次只读 rewrite 中组合，独立／统一入口各通过 668 次调用／673 行输出；四单元检查安全沿实际源前缀建立，候选快照 bound 后确实重排。[动态内存上界矩形](docs/clight-loaded-rectangle-case.md)进一步支持运行时行数／列数与静态 stride，独立／统一入口各通过 6,248 次调用／6,253 行输出；两层实际检查由通用前缀扫描生成。[共享出口适配层](docs/shared-guard-lowering.md)又复用原只读证书和局部规则，将每处候选／回退各生成一份，相同 C 调用通过；编译器私有 Boolean 的实际写入由 frame／scope 和上下文证明保护。[参数 stride 与内存上界的同次交换](docs/clight-loaded-stride-case.md)又覆盖 extent≤12 的全部合法正布局，实际候选继续使用参数地址；独立／统一入口各通过 68,368 次调用／68,373 行输出。[双内存上界的单次迭代消除](docs/clight-dual-loaded-unit-case.md)又接通延迟双重读取、两项稳定性和独立嵌套源进展，独立／统一入口各通过 3,035 次调用。[双内存上界的实际数组交换](docs/clight-dual-loaded-matrix-case.md)进一步接通逐点两层 tail、两个读取的稳定性和真实四次写入重排；固定 2×2 接受域中两入口各通过 22,303 次调用。[双动态上界的幂等写入化简](docs/clight-dual-repeated-store-case.md)又支持任意正 signed32 尺寸，候选写零一次并恢复两个 counter；两入口各通过 3,035 次调用。[两个 runtime 内存尺寸的矩形交换](docs/clight-dual-dynamic-rectangle-case.md)进一步通过独立共享入口和完整 Csem→Asm 端点，113,330 次调用／八处 region 覆盖不同尺寸、两个静态布局及 alias 回退；selector extent≤12，双缓存规则已进入综合入口并与旧单缓存规则交替运行；已验证探针简化将主函数打印体 129,224→14,234 字节、语法 if 413→69，检查仍以树展开。更大布局／一般指针、参数 stride 的双 loaded 组合、无界／仿射足迹和旧 affine 编译器迁移仍待完成。[组合使用者 pass](docs/clight-common-user-pass.md)已在同一函数中接入原有单缓存和精确出口规则，以及双缓存动态矩形：原混合 fixture 的 576 次调用／2880 行输出通过，新增交替多缓存 fixture 的 120 次调用／720 行输出通过；二十五种配置回归和 401 个编译接口端点审计通过。[固定寄存器上界的等式退出](docs/clight-equality-loop-case.md) 又将 `!=→<` 接到新接口；源进展用模距离证明，unsigned 回绕 fallback 不依赖 guard。独立入口和统一 pass 各通过 703 次 C 调用／七处实际 guard。[逐步头部宿主](docs/clight-stepwise-head-case.md) 又支持可能无限循环中的有限判断 rewrite，独立入口／统一 pass 各通过 333 次调用；当前值条件、改变上界、步长 2 和 volatile body 都由实际小步模拟连接完整编译，仍不提供这些循环的整段有限域。[普通 load／计算表达式比较](docs/clight-loaded-comparison-case.md)进一步从每次实际源求值建立检查安全，独立／统一入口各通过 737 次调用，包括改变 bound 的 alias 和只执行一次的源 volatile 快照。以 [Optimistic Loop Optimization 验收账本](docs/optimistic-loop-acceptance.md)记录当前缺口。底层扩展分类见 [四份核心契约](docs/language-independent-interface.md)。

以 Doerfert、Grosser、Hack 的 [Optimistic Loop Optimization（CGO 2017）](https://dl.acm.org/doi/10.5555/3049832.3049864) 为主线，现有原型覆盖 presumption 编码、condition 合成和 conditional rewrite。真实 Clight 分支、表达式、有限区域与严格计数循环 passes 已接入 C 到汇编正确性，并提取成编译器运行了 C 示例。当前工具链锁定 CompCert v3.18、Rocq 9.2.0 与 Stdlib 9.2.0。

[宿主能力与证明职责](docs/host-capabilities.md) 区分完成执行的整段版本化、每次求值位置检查和允许完整回退无限执行的整段小步协议；语言实例通过相应上下文证明连接完整程序。

[带依赖的只读检查接口](docs/condition-stage-interface.md) 支持将前一阶段接受的事实用于后续检查安全。框架只依赖语言提供的常量／顺序检查代数，证明任意有限阶段的状态不变、安全与接受含义；实际内存上界规则已消费该组合，条件语法保持相同。[分支与前缀扫描](docs/readonly-prefix-scan-interface.md)进一步支持活动结束后的提前接受和逐点 ghost 依据运输；indexed 上界规则实际调用通用生成器。[只读探针简化](docs/readonly-probe-simplification.md)进一步保留原条件证书地消除重复实际测试，已接到单 loaded 和双动态 loaded 矩形共享编译入口。当前 54 个纯接口端点闭合，Clight 59 个和主完整编译 415 个端点、864 份证明源码摘要审计通过；二十五种配置回归通过，40 份原生报告绑定当前证明与编译器。相对 `cf4d442`，39 份既有 C／Clight 摘要全部相同。新整段小步宿主无需原循环独立进展，真实 unsigned memory-bound 缓存通过 540 次有限调用／六处完整 loop，且有源／目标实际无限 alias 回退定理；当前新树仍有两份原回退。

研究对象还包括人工或工具给出候选后，由优化／domain library 推导可检查条件，再由框架消费证书、生成检查与回退。COVE/cSTOKE、Peek、Chamois、Icing 和 CoreJIT 已覆盖这条链的不同部分；当前原型是可行性基线，候选增量是可运行的、已验证的前提处理与检查代码生成。有限外层次数条件搜索已在实际多面体候选上实现；任意关系式条件推断和新颖性仍需进一步支持。

[实际分派与安装复用](docs/clight-guard-realization.md)已通过本轮验收：direct/shared 使用同一 readonly 规则证书和公共安装定理，完整 unsigned 循环消费同一有限 dispatch prefix。相对 `26956a4`，25 配置全部重建／回归、40 份 C／Clight 摘要不变；finite host 的 source progress 与 shared whole-loop 的未实现边界分别保留。

- [三方验证责任与最难验收](docs/framework-responsibilities.md)：框架、语言实例和优化／domain 方的责任；持续沿 topdown paper narrative 推进。
- [公共实际 guard 分派](docs/clight-guard-realization.md)：direct/shared 的私有资源、有限小步前缀和宿主安装复用。
- [当前交付与研究边界（2026-10-06）](docs/research-checkpoint-2026-10-06.md)：真实 affine／tiling 的主接口迁移、三方证明责任和后续难点。
- [10 月 5 日阶段记录](docs/research-checkpoint-2026-10-05.md)：只读框架、内存上界与调度、通用前缀扫描及 P0／P1 历史验证。
- [当前工作计划](docs/current-work-plan.md)：吸收评审后的优先级和验收，保留完整多面体主目标。
- [三个分支的综合评审](docs/review-synthesis-2026-10-05.md)：固定提交、逐项采纳、实际实现变化与研究主张校准。
- [完整 unsigned 循环与无限 alias 回退](docs/clight-guarded-circular-case.md)：有限前缀的检查安全、真实小步局部契约和 Csem→Asm 接入。
- [2026-10-04 交付记录](docs/research-checkpoint-2026-10-04.md)：前阶段可运行产物、成本问题与未完成项。
- [文献与需求](docs/survey.md)：已有工作解决了哪些部分，以及候选研究空隙。
- [统一完整程序编译器](docs/unified-guardcert-compiler.md)：同一 Csem→Asm 入口连接深层仿射循环、矩形循环和条件标量 rewrite。
- [接口与使用](docs/api-usage.md)：候选使用者、规则作者和语言实例各提供什么，以及框架给出什么证明。
- [深层片段使用通用有状态核心](docs/deep-affine-core-interface.md)：真实 Clight 条件实例、状态运输和完整程序宿主的证明边界。
- [保持相同前提的扫描精简](docs/deep-affine-scan-cost.md)：访问去重和单向比较的证明，以及实际检查成本。
- [深层检查与候选成本](docs/deep-affine-cost.md)：实际计时揭示平方扫描与空点枚举的成本，区分行为证明和性能结果。
- [深层多指针变换](docs/deep-affine-multiple-pointers.md)：实际源域地址扫描、前提编码、候选和回退，以及完整程序证明。
- [外部候选接口](docs/external-affine-candidates.md)：导出实际源，导入人工或工具生成的 Loop IR，自动生成守卫并独立验证候选。
- [深层多语句与分裂](docs/deep-affine-fission.md)：静态站点排列、本轮及未来迭代依赖、原片段回退。
- [深层候选条件搜索](docs/deep-affine-condition-search.md)：为同一外部候选尝试有限源范围，独立验证并生成完整程序中的守卫。
- [Skew 与 reflection](docs/deep-affine-coordinate-maps.md)：真实循环、负坐标、依赖拒绝及机器范围／守卫验证。
- [多个运行时版本](docs/deep-affine-runtime-versions.md)：逐轮检查当前程序、分配新私有名字，并在已有源回退位置安装后续 guard。
- [变量乘除条件 rewrite](docs/variable-cancel-rewrite.md)：非零与溢出范围性质编码、短路检查、表达式上下文及两个完整编译入口。
- [深层域切分](docs/deep-affine-domain-split.md)：完整切面覆盖、候选分组与执行顺序验证，共用原片段回退和完整程序定理。
- [候选变换组合](docs/deep-affine-composition.md)：逐段检查中间片段，连接索引平移、完整分区与分块。
- [深层矩阵累加](docs/deep-affine-accumulation.md)：实际读改写依赖、内层交换、数据回绕和重叠指针回退。
- [跨领域 survey](docs/survey-general.md)：重构、修复、合约、更新、enforcement、近似和超性质等场景的区别。
- [已有覆盖与研究定位](docs/research-position.md)：CompCert 主线、verified peephole 和最接近工作的对比；值得检验的具体问题。
- [从候选到带检查的程序](docs/candidate-conditioning.md)：人工/机器候选、COVE、条件等价，以及与 CoreJIT、Alive2 和 Peek 的区别。
- [具体贡献与推进计划](docs/contribution-plan.md)：建议主线、算法与定理、第一批实例和验收标准；补充可执行前提及最优 guard 合成的先例。
- [本轮研究结论与实际边界](docs/research-checkpoint-2026-10-02.md)：性质接口的分工、真实循环调度接入、条件读取安全性与后续一般域路线。
- [框架扩展设计](docs/framework-extension.md)：证据、状态关系、失败协议与不同证明目标；区分设计和已实现能力。
- [性质运输与状态关系的补充文献](docs/composition-literature.md)：CompCert／Verasco defensive form、开放模块组合及安全插桩的已有覆盖。
- [CompCert-loop 新增比较](docs/compcert-loop-comparison.md)：2026 年抽象行为接口与结构循环变换接入的直接先例。
- [研究动机草稿](docs/intro.md)：先描述变换类与研究对象。
- [Presumption 分类与合成](docs/presumptions.md)：表达能力、编码定理、overflow flag 和死分支 rewrite。
- [问题定义与证明接口](docs/framework.md)：插件义务、局部到全程序的桥接、CompCert 接入路线。
- [性质接口与抽象核心](docs/abstract-kernel.md)：语言实例、可组合的语义维度、三种检查结果、残余化，以及新条件树的实际 C→Asm 接入。
- [验证记录与边界](docs/validation.md)：实际编译、实例和反例检查。
- [真实 CompCert 接入](docs/compcert-integration.md)：插件证书、C 到 Asm 定理、提取与原生执行。
- [常见 rewrite 接口与实例](docs/common-rewrites.md)：除法、取模、条件算术取消、Truth identity；真实内存的局部接口。

## 原型

当前主线是 `AbstractGuard.v` / `SemanticFacts.v`：通用核不内置整数或内存语义，语言实例提供性质、检查原语与条件选择。`ClightCondition.v` 将生成的条件树降低成实际 Clight 控制流，表达式与语句宿主接到完整程序模拟，`AdaptiveRegionCompiler.v` 接到 C→Asm。overflow 取消规则已使用这个路径。`StatefulGuard.v` 进一步允许检查改变私有状态，由语言实例提供公共状态关系、源观察运输和条件构造证明；一般仿射地址扫描已实际通过它接入统一完整程序入口。`ResidualGuard.v` 提供有证书的静态消去，尚未进入原生驱动；`AbstractSchedule.v` 的性质驱动交换链及可执行检查器已进入实际矩阵优化的原生证明链。详细接口与 PolCert 尚需的桥接见 [abstract-kernel.md](docs/abstract-kernel.md)。

下面记录各实现阶段及独立适配路线，边界与验证数量属于各自的保存版本。当前能力与证据以顶部的两个实例及最新阶段记录为准；旧 deep 路线使用有状态核心，新接入消费当前 `GuardInterface`。

[同地址读取实例](docs/clight-same-address.md) 在这一端到端路径上增加内存性质维度：源 load 建立检查有效性，运行时 `p == q` 允许后端消除重复读取。原生检查覆盖快路、回退、unsigned 边界及 signed／volatile 排除。

[树形原子检查与 signed 取消](docs/clight-signed-cancellation.md) 让一个性质原子由多步骤条件树实现，继续复用同一完整程序宿主。signed32 的 `(x*2)/2 → x` 已进入实际 C→Asm 驱动，使用 signed64 检查而在溢出时保留源式回绕行为。

[有限语句区域宿主](docs/clight-statement-regions.md) 将局部条件正确性证书提升到完整 Clight 小步模拟，证明源区域内部每一步的工作量度量严格下降。`encoded_region_rule` 复用同一性质与条件合成接口；冗余赋值实例已进入实际提取驱动，原生例子验证普通、循环和 goto 外围中的快路／回退。出口 memory 已支持双向 `Mem.extends`；它的旧有限宿主保留为独立基线，当前提取入口使用下述进展协议宿主。

[片段内部进展协议](docs/region-protocol.md) 将小步覆盖、下降度量和完成执行的重建交给语言实例。通用核心不解释语言语义；有限片段与严格 signed32 计数循环共用显式模拟索引和整程序宿主。零次迭代时跳过整个循环的规则复用性质合成与 C→Asm 定理。真实 C 前端的循环包装已直接证明；原生例子验证整个循环命中、signed 边界和零次迭代的空指针 barrier。

[直接 Clight 的嵌套区域](docs/clight-nested-regions.md) 将片段进展与 temporary frame 合成，允许内层计数器变化并保护外层控制值。默认编译器替换真实 C 的整个两层循环；七组输入、五处 guard、公共 liveout、数组写入与 frame 违例经原生检查。

[原生矩阵循环交换](docs/native-matrix-interchange.md) 已进一步接入完整 Csem→Asm：动态检查 `i == 0 && n == 2 && m == 2` 后，将行顺序改成列顺序，否则执行原循环。实际 CompCert 内存重排证书保留完整内存和所有退出 temporaries；条件的读取安全性从源执行推导。五个实际 guard、九组输入、局部／全局数组、外围 goto／循环、未初始化但不被读取的内层边界及拒绝例子均通过原生验证。该入口只支持一个 2×2 仿射 store 模板，未调用 PolOpt，未声称性能改善。

[动态矩形循环交换](docs/dynamic-rectangles.md) 将源对应和循环重建推广到任意运行时行列数，编译器从数组长度与跨度导出短路 guard；通用核在语言提供可交换性质后证明符号化域的重排，无需枚举运行时点。独立 `RectangularCompiler.compile_rectangular_regions` 接入完整 Csem→Asm 定理，`make native-rectangular` 验证纯写、同格子读改写、保留行内依赖的行首读取及外围上下文。此实例仍使用内置循环交换，未实现一般调度。

[真实内存的多面体路径](adapters/compcert-memory/README.md) 已把上述三类完整源循环接到实际 Loop 与 PolyLang，并由一般依赖验证器的结果建立候选进展及完整 Csem→Asm 定理。`make native-memory-compiler` 提取 `GuardMemoryCompiler.compile_memory_regions`，验证 795 个正矩形、19 个 guarded 函数及错误证书／资源耗尽时的源循环保留。`make native-memory-validator` 单独执行一般仿射与实际二维 tiling 检查器。[二维分块的完整 C 路径](docs/memory-two-dimensional-tiling.md) 另通过 `GuardMemoryTiledCompiler.compile_memory_tiled_regions` 接入完整定理，生成四层候选、尾块 guard 与公开 iterator 出口修复；`make native-memory-tiling` 提取并运行这个入口。[仿射条件域](docs/memory-affine-conditional-domains.md) 另接通三角形、斜切等静态叶子条件的完整 C 分块入口，`make native-memory-cuts` 已验证 4800 个正动态条件域与实际快路。[多语句完整 C 分块](docs/memory-multiple-statement-tiling.md) 已支持同布局数组纯写列表和重复语句的位置区分；`make native-memory-sequences` 提取这个入口。[混合读写列表](docs/memory-mixed-statement-tiling.md) 已接通纯写、原地更新、行首读取在同一个数组上的任意非空组合；`make native-memory-operations` 提取完整入口。[一般 Loop 与外部候选](docs/memory-general-loop-candidates.md) 已提供真实提取的双向执行对应，以及接受不受信任结构候选的 Csem→Asm 入口。[点坐标对应](docs/memory-point-coordinate-correspondence.md) 支持外部候选携带 iterator 排列；[语义域等价与统一候选](docs/memory-semantic-domain-alignment.md) 已将外部仿射候选和二维分块提案接到同一完整程序入口；`make native-memory-unified` 构建并运行它。[多个实际数组对象](docs/memory-multiple-array-objects.md)已进入同一完整程序定理，并提供实际 block 非别名和安全基址检查；`make native-memory-multiarray` 验证它。跨数组同单元读取、只读输入及[直接数组复制](docs/memory-direct-array-copy.md)也已接通；[仿射 iterator 对应](docs/memory-affine-iterator-maps.md)进一步接入平移、剪切及组合映射。[非矩形 C 源边界](docs/memory-nonrectangular-source.md)进一步接通 `j < i + M` 的真实执行、宽度检查、仿射候选、实际二维分块与公开计数器出口；`make native-memory-ragged` 验证完整程序接受和回退。[仿射调度生成路径](docs/memory-schedule-generation.md)已从真实源提取、外部调度到实际 CodeGen，再经独立检查接入相同完整程序定理；`make native-memory-schedules` 验证它。[参数化仿射内层上界](docs/memory-parametric-affine-bounds.md)已接入有符号常量、参数、加减和常量乘法构成的边界，支持递增及递减的行宽、多个参数、真实数组复制和相同完整程序端点；`make native-memory-parametric` 验证调度、分块及外围上下文。[不同数组长度和步长的一条复制](docs/memory-different-array-layouts.md)也已接入相同完整程序入口，读写地址按各自布局编码；`make native-memory-layout-copy` 验证它；[同一数组的布局重映射](docs/memory-same-array-layouts.md)也使用相同入口及实际依赖检查。[不同布局混合列表](docs/memory-layout-operation-lists.md)及[真实仿射下标](docs/memory-affine-source-accesses.md)也已接入。[具有源证据的邻居偏移](docs/memory-anchored-offset-accesses.md)也已接入。[多个仿射读取与整数计算](docs/memory-affine-computations.md)也已接入并通过完整汇编验证。[三重 C 循环与矩阵乘法](docs/memory-three-level-loops.md)已接入调度、外层二维分块与完整汇编验证。[任意有限层规范 C 循环](docs/memory-recursive-source-loops.md)随后接入同一完整程序入口，验证四、五、六、八层源以及外层二维分块。[真实指针缓冲区](docs/memory-pointer-buffers.md)随后接入单个稳定 signed32 指针、任意基址、同一域／依赖检查及条件范围搜索；15 组完整汇编配置和 10 组／390 次调用的分支诊断通过，`make native-memory-pointer` 可重现。[稳定 RHS 标量参数](docs/memory-stable-scalar-parameters.md)随后接入指针与固定数组，保留 signed-32 数据运算及短路求值安全；两类各 16 组完整汇编配置和 10 组分支诊断通过，分别覆盖 2626／2602 次调用。`make native-memory-scalar` 与 `make native-memory-scalar-array` 可复现；这些阶段的报告保留各自的编译器 hash；当前全量审计及功能边界见下面的 signed 地址和多指针记录。

[辅助变量与循环分块](docs/private-stripmine.md) 让局部变换引入 private temporaries，并证明完整程序只需在源标识符上保留 temporary 值。`StripmineCompiler.compile_stripmine_regions` 实现任意核对后的正块大小的 strip-mining，包含动态尾块；循环体允许普通数组读写、多条语句、分支、真实依赖与指针别名。辅助边界无溢出前提经同一检查合成器产生，检查失败保留原循环。`make native-stripmine` 提取实际 C→Asm 入口并验证不同块大小、源 counter 出口、完整数组及调用／goto／switch 上下文。该阶段只提供保持顺序的分块；后续一般候选和调度生成见上述真实内存路径。矩形纯写／原地更新／行前缀读取二维 tiling 已由上述真实多面体路径实现。

[通用有限调度核对器](docs/schedule-checker.md) 从不受信任的候选顺序生成重排证书，只消费指令相等性与可交换性质的检查。实际矩阵规则已消费它，CompCert 数组元素性质库提供真实内存解释。Rocq 提取的 OCaml 检查器已运行全部 120 个五指令排列、依赖拒绝及重复／缺失指令案例；这还不是一般 affine schedule validator。

[不受信任的点顺序入口](docs/untrusted-point-schedules.md) 进一步允许外部提供有限调度，由核对器接受后生成实际 Clight 展开代码并精确恢复循环变量。参数化 C→Asm 定理覆盖任意提案，包括被拒绝的提案；源域仍限于固定 2×2 模板。`make native-schedules` 提取该入口，并验证全部 24 个合法点排列与七个错误提案。

该入口使用[共享回退 lowering](docs/shared-fallback.md)，所有检查失败汇合到同一份原循环，不增加临时变量或标签，并复用原局部证书。五个实际函数的代码体积均减少，例如 `matrix_dynamic` 从 353 降至 221 字节；这是 fixture 的函数字节数，没有速度结论。

[内存与宿主运输性质](docs/compcert-memory-transport.md) 从不依赖具体语义的双向模拟引理，实例化真实 CompCert 内存、运算、Clight 表达式和完整小步执行。代码及 temps 相同而 memory 双向扩展时，语言实例提供相同观察及后继关系的证书。PolCert 的具体 load/store 桥接已复用这个接口；区域替换宿主已借此连接等价内存出口与完整 C→Asm 定理。

[PolCert 适配](adapters/polcert/README.md) 已在同一工具链上完整重编译真实 `Loop` 的 57 个证明依赖，直接接入 `INSTR` 的 Bernstein 交换性质和 `Loop` 条件片段。`make polcert-proof` 从锁定源码与补丁复现；实际 PolCert 优化器到完整 Clight 循环程序的桥接仍在推进。

[实际优化器适配](adapters/polcert-optimizer/README.md) 进一步移植 92 个证明依赖。`PolCertOptimizer.optimize_version` 调用真正的 `Opt_prepared`，检查 metadata 并生成 guarded `Loop.t`，其正确性直接消费上游端点；复现目标为 `make polcert-optimizer-proof`。[优化器区域证书](docs/polcert-optimizer-regions.md) 已将这个端点接到参数化的 Csem→Asm 定理。完整循环的具体证书与原生优化器调用尚未实现。

[signed32 仿射桥接](docs/polcert-affine-clight.md) 已证明实际 Loop 表达式和布尔测试到 Clight 的 lowering，并通过通用性质接口生成输入区间 guard。接受的 guard 建立静态区间证书需要的运行时前提；缺失布局或无效区间保留 unknown。复现目标为 `make polcert-affine-proof`。完整循环与区域 lowering 仍在推进。

[计数循环桥接](docs/polcert-clight-loop.md) 进一步提供基本指令插件、`Instr/Seq/Guard` 的 body 编译、一个外层 Loop 的 Clight lowering，以及任意 continuation 中的实际小步执行证书。复现目标为 `make polcert-loop-proof`。当前 body 要求保留 temporaries，内部循环尚未支持；多面体优化的完整程序 simulation 仍未闭合。

[嵌套循环桥接](docs/polcert-nested-clight.md) 扩展到指定 scratch 深度的多层 Loop，允许内层 scratch 改变并保护参数、外层计数器及声明的 live frame。编译器检查整个 scratch pool 的新鲜性；复现目标为 `make polcert-nested-proof`。翻译另有纯语法接口，正确性证书由语言实例提供。

[具体数组实例](docs/polcert-array-clight.md) 重编译真实 `CInstr/CState/Loop` 的 60 个依赖，将一维 signed32 数组指令和嵌套循环接到 Clight 的真实 load/store 与小步执行。最终端点没有抽象指令执行假设；真实分配／初始化例子证明 `B[0]=7` 时生成代码产生 `A[0]=8`。复现目标为 `make polcert-memory-proof`。标量参数入口、候选进展、tiling 边界运算及完整程序区域模拟仍在推进。

[CInstr 入口审计](docs/polcert-context-audit.md) 证明锁定的旧非空声明 wrapped 语义不可执行，并提供新的显式只读参数实例。真实分配内存上的循环执行见证已通过；旧模型与既有 raw 指令／原生双写实例的边界分别记录。该问题约束复用旧模型的路线；自建语言实例可以直接使用 CompCert 内存与机器算术，但仍须证明真实入口、源解码与候选重建。

[真实 CInstr 调度区域接口](docs/polcert-schedule-regions.md) 已将入口检查域、接受后的源解码、条件调度证书和候选生成组合为完整 Csem→Asm 定理，采用与 PolCert 相同的等价内存出口。`PolCertStorePackage.v` 已实例化动态数组双写的具体包族，并进入实际提取入口；这些局部义务均连接真实执行。

[具体 CInstr 双写重排](docs/polcert-store-swap.md) 已用真实 Bernstein 定理证明同一数组的两个不同常量元素写入可以交换，并接到完整 Csem→Asm 定理。检查器验证静态参数和源 AST，真实分配例子构造两端执行。`make polcert-store-native` 还提取独立编译器，检查普通、循环体和 goto 上下文中的三个实际交换及五个排除例子。该阶段只处理常量元素写入；后续内部循环区域及调度接入见上述真实内存路径。

[动态数组下标实例](docs/polcert-dynamic-stores.md) 从范围及不同下标前提合成实际检查；条件接受后调用真实 CInstr 重排性质，拒绝时保留两条源写入。源执行提供下标定义性，条件正确性与检查编码分别证明，继续复用完整程序区域宿主。

[无人工区间的仿射 guard 合成](docs/affine-dynamic-synthesis.md) 直接从“不溢出”前提与 layout 生成依赖顺序的 signed64 检查树，证明检查精确对应所选 signed32 前提，并经性质接口支持复合公式和 unknown。复现目标为 `make polcert-dynamic-proof`；这一合成器尚未进入原生驱动。

`GuardedRegion.v` 把片段表示为一次返回事件、控制出口和状态的转移。新的插件路径先证明语义义务与 presumption AST 的编码对应，经 `Synthesis.v` 合成为显式短路条件程序，再由通用定理提升到任意外围 CFG 的有限与无限执行。

| 文件 | 内容 |
| --- | --- |
| [GuardedRegion.v](theories/GuardedRegion.v) | 版本选择、证书与原片段的绑定、多位置替换、上下文替换定理 |
| [CheckedGuard.v](theories/CheckedGuard.v) | 8 位无符号加法检查；接受的表达式与数学整数求值一致 |
| [Examples.v](theories/Examples.v) | 无回绕假设下的比较消除、无别名假设下的写操作交换、完整示例程序 |
| [Presumption.v](theories/Presumption.v) | 有限表达子集：算术、NoOverflow、边界、不相交及布尔组合 |
| [Synthesis.v](theories/Synthesis.v) | 编码契约、带 flag 的求值、condition 合成与真/假对应 |
| [ConditionalRewrite.v](theories/ConditionalRewrite.v) | 恒假分支、前提下的死分支、矛盾前提；共享完整程序定理 |
| [CompCertArithmetic.v](theories/CompCertArithmetic.v) | 实际 CompCert Int 运算与 checked-add 原语的对应证明 |
| [ClightGuard.v](theories/ClightGuard.v) / [ClightGuardProof.v](theories/ClightGuardProof.v) | 真实分支版本化 pass；Clight 两种入口语义的完整程序仿真 |
| [ClightEncodedRule.v](theories/ClightEncodedRule.v) / [ClightNoWrap.v](theories/ClightNoWrap.v) | 编码、condition lowering 与局部正确性证书；unsigned32 分支实例 |
| [ClightExprRewrite.v](theories/ClightExprRewrite.v) / [ClightExprRewriteProof.v](theories/ClightExprRewriteProof.v) | 表达式版本化与完整 Clight 程序的仿真 |
| [ClightExprRule.v](theories/ClightExprRule.v) / [CommonRewrites.v](theories/CommonRewrites.v) | 完整快照上的表达式证书；严格表达式上下文提升；四个 rewrite 实例 |
| [CompCertMemoryRule.v](theories/CompCertMemoryRule.v) | Disjoint 编码与实际 Mem.load/store 的局部稳定性、load hoisting 端点证明 |
| [GuardCompiler.v](theories/GuardCompiler.v) | 扩展编译驱动、Csem 到 Asm backward simulation 与规格保持 |
| [ClightIntegrationExamples.v](theories/ClightIntegrationExamples.v) | 真实 Clight 快路／回退；恒假分支与矛盾前提的编译器实例 |
| [CommonRewriteExamples.v](theories/CommonRewriteExamples.v) | 实际 AST 命中、类型拒绝、嵌套上下文和无条件取消的溢出反例 |
| [demo.py](prototype/demo.py) | 独立 Python 执行模型、边界枚举和错误变体反例 |
| [synthesis_demo.py](prototype/synthesis_demo.py) | 从 presumption 合成 condition AST，运行新增 rewrite |

真实 passes 在 `SimplLocals` 后运行：分支版本化允许 guard 接受时进入原 else；表达式版本化允许 guard 接受时运行保持类型和值的候选。后者支持赋值右侧和 return，可提升到二元／单目运算及 cast。四个新实例是 `x/y→x>>1`、`x%y→x&1`（检查 y=2）、`(x+x)/2→x`（检查不回绕）和 `x-x→0`（Truth）。完整程序证明覆盖调用、外部事件、可能发散的循环、switch 和 goto。

实际源足迹的跨指针分离检查已接入受支持的矩形和深层仿射循环，并与候选及回退连接到完整程序定理。它仍采用保守的跨指针分离前提与平方扫描，不支持任意内存片段的别名检查。任意候选 region 的关系式条件发现、preload 和完整 DSL lowering 仍未覆盖；真实 Mem 的 load-hoisting 局部证明尚未接入 Clight。独立 `GuardedRegion.v` 模型采用总的有限宏转移，与实际 Clight 宿主的边界分别记录。

## 运行

需要 opam、Python 3.10 或更新版本和通常的 OCaml 构建依赖。工具链在项目的 `.toolchain/` 中隔离，不需要系统安装。详细版本与构建记录见 [toolchain.md](docs/toolchain.md)。

```sh
sh scripts/bootstrap.sh
opam exec --root="$PWD/.toolchain/opam" --switch=guard -- make check-integration
```

只验证独立语义核和 Python 模型：

```sh
opam exec --root="$PWD/.toolchain/opam" --switch=guard -- make clean
opam exec --root="$PWD/.toolchain/opam" --switch=guard -- make check
```

`make proof` 编译独立语义核；`make demo` 运行两个独立执行模型及实际 Rocq 提取的调度检查器。`make check-compcert` 还完成 CompCert proof 构建与接入文件编译。`make check-integration` 进一步审计实际驱动定理的假设，提取默认、有限点调度、动态矩形及分块入口，构建四个编译器并运行八组默认 C 原生套件、点调度、动态矩形及分块套件，没有全局安装。已有 Python 模型不是 Rocq 提取产物；原生示例使用的编译器来自实际提取。版本、条件 AST 与原生结果在 `build/compiler.txt`、`build/synthesized-conditions.json` 和各个 `build/native-*/` 目录，包括 `build/native-nested-regions/`、`build/native-matrix-interchange/`、`build/native-scheduled-matrix/` 、`build/native-rectangular/` 与 `build/native-stripmine/`。

[实际多面体候选的条件搜索](docs/memory-candidate-conditioning.md)在默认域失败后提出更小的外层次数区间，逐个重新核对域、依赖、机器代码与 guard，接入相同完整 C→Asm 入口；运行诊断同时核对快分支可达和依赖反例回退。

[不同布局读写列表](docs/memory-layout-operation-lists.md)保留各条赋值的实际步长与对象，组合整段列表的真实内存执行，并进入同一个完整程序定理。复制链、更新和同数组重映射继续消费候选依赖检查及已验证条件搜索。

[内层宽度条件搜索](docs/memory-inner-width-conditioning.md)在原域及外层次数搜索失败后，用范围包含证明限制内层宽度并重新验证候选。`m-p` 复制链的循环分裂已经进入完整 C→Asm 入口，实际快路允许多个外层迭代，依赖反例回退。

[三重 C 循环与矩阵乘法](docs/memory-three-level-loops.md)已进入统一完整 C→Asm 入口，实际依赖检查接受 `i-k-j` 和外层两维分块，拒绝破坏复制链顺序的反转与分裂。`make native-memory-triple` 验证完整汇编、机器回绕、公开出口和短路回退。

[递归 C 源循环](docs/memory-recursive-source-loops.md)已通过 17 组完整汇编配置和 11 组实际分支诊断。`make native-memory-recursive` 构建并验证该路径；当前原生驱动的八对辅助计数器允许八层普通候选或六层源的外层二维分块，资源不足安全回退。

[signed 仿射源地址](docs/memory-signed-affine-access.md) 通过 241 个适配模块及七个 lowering 模块的完整编译与假设审计，完整程序端点仍继承 42 项原有假设。13 组实际汇编配置和 10 组分支诊断（5463 次调用）通过；检查覆盖反向依赖链的正确回退、中间回绕和最终合法地址。

[多指针活动访问检查](docs/memory-multiple-pointer-guards.md)通过 269 个适配模块及七个 lowering 模块的完整编译与假设审计，完整程序端点仍继承 42 项原有假设。11 组完整汇编配置和九组分支诊断（5256 次调用）通过；`make native-memory-multi-pointer` 可复现。检查支持同一 block 中的不重叠切片和交错访问，依赖或地址条件失败时回退。当前枚举最多 64 个潜在访问条目，只读别名仍保守拒绝。

[显式源元数据的候选接口](docs/memory-source-metadata.md)消除访问式未使用某些循环维度、或遗漏稳定参数时的调度维数猜测。完整程序定理对任意候选提议器继续成立；269 个适配模块和七个 lowering 模块全量审计通过，九组完整汇编配置和六组分支诊断通过，`make native-memory-source-metadata` 可复现。

[循环式 alias guard](docs/memory-loop-alias-guards.md)允许检查修改私有计数器和标志，并证明检查后的状态满足候选前提。一个计数轴、两个指针及逐元素访问已接入完整 C→Asm 入口，检查代码不按循环上界展开。当前扫描为 O(n²)，逻辑窗口为 1024。[坐标反射](docs/memory-coordinate-reflection.md)随后接入一维反向执行及反射和平移的组合：280 个适配模块和七个 lowering 模块全量审计、1200 次完整汇编调用及 600 次分支诊断通过，`make native-memory-loop-alias` 可复现。

[一般一维仿射地址扫描](docs/memory-affine-alias-scans.md)随后接入非单位步长、递减／常量下标和多个指针，并实际实例化有状态的语言无关核心。293 个适配模块、七个 lowering 模块和两个抽象核心模块的全量审计通过，完整编译器仍为原有 42 项假设；2696 次完整汇编调用和 1366 次分支诊断通过。新路径至多构造 32 条原始访问之间的 O(A²n²) 检查，资源超限继续尝试旧路径；检查接受也必须有独立的调度依赖证书。`make native-memory-affine-alias` 可复现。

[仿射端点扫描](docs/memory-affine-endpoint-scans.md)随后为相同步长或常量访问选择单层检查，将这些访问对的检查次数从平方降为线性，其他访问对保留双层扫描。297 个适配模块、七个 lowering 模块及两个核心模块的全量审计通过，数学充分性与算法选择没有全局公理，完整编译器仍为原有 42 项假设。新例子通过 1687 次完整汇编调用及 964 次分支／精确比较计数诊断；一般仿射和逐元素循环的完整回归也在同一编译器上通过。`make native-memory-affine-endpoints` 可复现。多轴动态扫描及地址参数仍待实现。

[多轴动态 alias 扫描](docs/memory-multi-axis-alias-scans.md)随后将源实际活动足迹的检查推广到任意有限层规范矩形循环，并接入 mapped、调度生成和二维分块的统一 Csem→Asm 端点。310 个适配模块、七个 lowering 模块及两个核心模块全量审计通过，没有新增全局公理；14 组配置共 4270 次完整汇编调用、2135 次分支及精确比较计数诊断通过。新源序候选的共同上界在例子中扩大至二维 61、三维 15、四维 7；同一源码的检查代码体积减少，运行时仍采用平方扫描。`make native-memory-axis-alias` 可复现。共同次数上界、更一般深层仿射域及地址参数仍待扩展。


[多轴边界扫描](docs/memory-axis-boundary-scans.md)随后替换同系数访问对的平方检查，并证明在源地址能力成立时保持原 guard 的布尔结果。320 个适配模块的全量审计和统一 Csem→Asm 端点通过，没有新增全局公理；五套完整汇编及分支回归通过。相同 2135 次多轴诊断保持 618 次快路、1517 次回退，查询总数 `35,537,690 → 854,960`。四维小输入可能增加查询，生成代码也变大；不同系数保留完整扫描。共同 cap、地址外部参数及更广深层源域继续推进。

[逐轴范围条件](docs/memory-per-axis-bounds.md)随后让源访问、guard、依赖验证和候选机器 lowering 共用独立的轴 cap。`(per-axis …)` 候选入口已接入统一 Csem→Asm 定理；340 个适配模块的全量审计、489 个证明源码哈希检查通过，完整编译器保持既有 42 项假设。新入口完成 6230 次完整汇编调用及 3115 次分支诊断，同一源码逐调用比较新增快路 502 次、新增回退 128 次；单个 box 的接受范围没有包含关系，查询总数也增加，不能视作性能提升。`make native-memory-axis-bounds` 可复现当前入口。该阶段没有接入地址外部参数及更一般的深层指针域。

[仿射地址参数](docs/memory-affine-address-parameters.md)随后将片段内稳定的地址 temporary 与普通 RHS 标量分开，连接源定义性、短路范围条件、真实足迹扫描、依赖验证和机器 lowering。20 个新模块已进入统一 Csem→Asm 定理；360 个适配模块及 509 个证明源码哈希的全量审计通过，完整编译器保持原有 42 项假设。新入口完成 7384 次完整汇编调用和 4219 次分支诊断；3819 次片段入口实际接受，完整缓冲区和公共游标一致。编译器还可将外层游标视为内层片段的地址参数；`make native-memory-address-parameters` 提供复现入口。

[固定地址参数的边界扫描](docs/memory-parameter-boundary-scans.md)随后将边界策略推广到参数化片段：只比较循环坐标的系数前缀，固定实际参数值，不把参数作为扫描轴。367 个适配模块及 516 个证明源码哈希的全量审计通过，完整程序保持既有 42 项假设。同一八核源的前后编译器各完成 8281 次完整汇编调用；4288 次分支诊断保持片段、范围和逐入口接受结果，实际地址查询 `1,128,338 → 231,952`。不同坐标系数保留完整扫描，小矩形可能增加查询；这些结果不宣称运行时间加速。原有逐轴入口和五套普通入口也在同一编译器上完成回归。

[多个运行时条件方案](docs/memory-version-families.md)已接入语义无关的抽象核心、实际 Clight 检查／候选组件及统一 Csem→Asm 端点。不同方案可使用不同的定义域、前提和状态关系，检查失败通过源观察保持证明衔接到下一方案。当前实例在五个地址参数 cap 组中各取首个验证通过方案；372 个适配模块、三个核心模块和 522 个证明源码哈希全量审计通过，完整程序仍为原有 42 项假设。相同源码的前后版本各完成 8281 次完整汇编调用，4288 次分支诊断的候选调用 `1336 → 1810`，新增 474 次且没有丢失既有接受；查询 `231952 → 735722`，代码也增大。普通和单方案入口已完成同一新编译器回归。`make native-memory-parameter-versions` 可复现；该阶段不提供最弱条件或运行时间加速保证。

[检查前缀与提前回退](docs/memory-prefiltered-versions.md)随后也进入实际编译器：已认证完整检查的廉价前缀拒绝时尝试下一方案，前缀接受而地址检查拒绝时回到源片段。376 个适配模块、三个抽象核心和 526 个证明源码哈希全量审计通过，完整程序仍为原有 42 项假设。同源前后版本各通过 8281 次完整汇编调用；4288 次分支诊断保留相同 1810 次候选调用和 4330 个候选片段入口，查询 `735722 → 653276`，减少约 11.2%，但代码文本增大。普通和单方案完整回归及旧多方案定向回归通过。`make native-memory-prefilter-versions` 可复现；通用证明保证源观察保持，不保证任意异质方案的接受范围保持或运行时间加速。

[带实际入口起点的片段](docs/memory-started-fragments.md)随后将所选指针循环的根下界接到真实公共游标，并证明只检查实际 `[start, upper)` 足迹。直接候选、自动仿射调度、分裂和二维分块共用统一 Csem→Asm 定理；私有计数器保护入口快照，退出时恢复源公共游标。407 个适配模块和 557 个证明源码哈希全量审计通过，完整编译器保持既有 42 项假设。13 种配置通过 10283 次完整汇编调用；另有 5340 次实际分支诊断，观察到 369 个非零起点候选入口。负根和负地址参数快路仍在推进，不能将该阶段等同于任意片段或全部多面体能力。`make native-memory-started-regions` 可复现。

[有符号循环和地址窗口](docs/memory-signed-windows.md)进一步把负数根起点、稳定地址参数及逻辑下标接到实际源对应、短路条件编码和统一 Csem→Asm 证明。单指针路线静态证明窗口内的单元分离，依赖合法性仍由候选检查器验证。该阶段 440 个适配模块及 590 个证明源码哈希的完整编译与审计已通过，完整程序保持既有 42 项假设。13 种配置完成 7982 次完整汇编调用；3238 次分支诊断观察到 566 个负根、2072 个负参数和 1672 个负下标快路入口。34 个未定义参数入口实际执行零次参数测试。`make native-memory-signed-windows` 是该入口的复现目标。

[有符号片段根的二维分块](docs/memory-signed-tiling.md)随后将负数根入口、跨零的行块和源公开出口接到统一候选及完整程序证明。442 个适配模块与 592 个证明源码的全量编译和假设审计通过，仍为原有 42 项完整程序假设；17 种配置通过 10438 次完整汇编调用，11 组分支诊断通过 4010 次调用。旧 signed 配置及三组非负起点入口的定向回归逐行报告完全相同。原生提案器筛选正 signed32 块大小，已验证检查器再检查候选。该阶段的 signed 快路使用单指针静态分离；后续多指针路线见下文，更一般深层仿射域及版本族组合继续推进。

[有符号窗口中的多指针](docs/memory-signed-multiple-pointers.md)进一步把多个实际稳定指针、负根和负地址参数接到同一完整程序端点。单指针使用已有静态分离，多个指针扫描本次源实际访问的跨指针单元；接受后还须通过独立依赖验证。461 个适配模块、七个 lowering 模块、三个核心模块和 611 个证明源码的干净全量审计通过，完整程序仍精确保持原有 42 项假设。14 种配置通过 9660 次汇编调用，11 组分支诊断完成 5644 次调用、6682 个实际候选入口。检查至多处理 32 条原始访问，完整扫描仍为 O(A²P²)，只读别名保守拒绝。`make native-memory-signed-multiple-pointers` 可复现。更一般深层仿射域、动态步长和 signed 版本族组合继续推进。

[深层仿射原型](prototype/affine-nest/README.md)的初期单指针阶段记录如下；当前多指针与统一入口见上方链接。逐层上界可读取外层游标和稳定参数，
从实际源执行推导安全 guard，检查候选域与真实依赖，恢复全部源控制出口，并接到 Csem→Asm。
65 个独立模块与既有 611 个证明源码共同支撑提取入口，完整程序保持既有 42 项假设。
二十四种配置完成 6,792 次实际汇编调用，另有 2,771 次实际 Clight 分支诊断；合法三层交换和前两轴分块被安装，
真实依赖、错误域／映射／分块见证及验证器失败保留源片段。`make affine-nest-compiler native-affine-nest` 可复现。
该初期阶段尚未实现深层多指针或合并统一驱动；前两项已在后续阶段完成，成本改善仍待验证。
子范围和地址窗口还可由实际源语法推导；较大 fixture 另完成 300 次汇编调用和 180 次分支诊断，
观察到 70 次超过旧 cap 8 的快路调用。`make native-affine-nest-ranges` 可复现。
