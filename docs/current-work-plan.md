# 当前工作计划：评审吸收后的验收顺序

2026-10-07 当前：[原 Horner tensor 源](tensor-original-source.md)已从真实原 Clight
execution 生产模型，连接 affine／tiling candidate 并恢复公开 iterator exits；
source-derived readonly layout condition 以原 silent normal completion 许可读取。
111 端点＝旧 66＋新 45／291 依赖审计、12 项提取检查通过；无新 kernel／整程序
compiler。数学 BOX 覆盖每个 read/write 的全部活动坐标，但尚未编码为机器 guard。
当前为 positive rectangular temp-bound nest、单 leaf operation、一个 tensor；
literal `<5` transport、region factory／private resources／progress／placement 与
Csem→Asm 继续沿 [checkpoint](research-checkpoint-2026-10-07-tensor-source.md)验收。
Narrative 远端重新 fetch 仍为 `271f6fc`，main 正文相同。三方责任／四条链保持；
不把源模型假设、guard-only certificate 或可运行 checker 当成完整安装。完整目标 active。

2026-10-07 当前：[动态 tensor candidate backend](dynamic-tensor-backend.md)已完成
vector affine read／RMW lowering、runtime layout 参数保护、实际 guard 到 registry
nonalias，以及原 affine／tiling checker 到实际 Clight candidate execution 的连接。
66 端点（33 旧＋33 新）／238 依赖审计、七项提取运行通过；无新完整 C compiler。
重新 fetch 并读完 narrative `271f6fc` 和 context-lifting 说明，main 正文一致。
[新 checkpoint](research-checkpoint-2026-10-07-tensor-backend.md)将澄清具体纳入
目标：保持最小 kernel；下一项是原源 Horner 地址／活动路径／完整坐标覆盖的
producer，然后 public exits、typed factory／progress／placement 和 Csem→Asm。
按约定三层子集先闭合证明链，再同例验收条件成本、接受域、bytes、完整运行和
三方作者负担；不等所有扩展做完才比较。C_opt 已接模型，C_derive 尚缺实际源，
不把接口字段、observer 或 checker 可运行当作全程序证明。完整目标 active。
以下阶段记录保留原范围，其后继顺序以本段和新 checkpoint 为准。

2026-10-07 最新：[动态 tensor 服务](dynamic-tensor-layout.md)补齐逻辑坐标向量到
modular pointer 地址的局部连接与安全 volume guard。33 端点／160 依赖审计通过，
13 闭合端点，零新增公理。已有二维 runtime-stride compiler 已保留变量 stride；
本轮不重复声称新增这种能力。最小 kernel 与原 instruction／dependence contract
保持，尚无新完整 compiler／native。Narrative 远端 `271f6fc` 已再次 fetch，main
正文一致。[新 checkpoint](research-checkpoint-2026-10-07-dynamic-tensor.md)固定后续
顺序：vector affine accesses／真实 reads/value backend → 原源维度读取许可与
保护／坐标覆盖 → candidate lowering／公开出口 → selector／语言 host／Csem→Asm
→ 提取和完整 C 接受／回退。数学 span 不代替实际权限，单 tensor nonalias 不
代替 header 稳定性或跨 array 分离。完整 BT、成本和作者负担继续独立验收。
完整目标 active。以下保留先前阶段当时范围。

2026-10-07 最新后继：[入口参数同值条件](nested-invariant-word.md)已将 literal
shortcut 扩展到 loop-invariant affine int32 store values，实际 physical guard、
模型生产、data-only factory 和新 Csem→Asm entry 全部连接。新值定义性由原源
prepared/domain receipt 生产，没有新增 caller callback；原 literal lowering、
candidate validator、五赋值出口和 language host 复用。35 端点／591 依赖审计、
提取、120 assembly／60 Clight calls 通过，包含 wrap 后 word-one 的 header alias
接受与动态域变化回退。没有新的 GDB probes、成本或最新入口的 source-only rebuild。
本轮确认 narrative 远端仍为 `271f6fc`、main 正文一致。
下一项按 [本轮 checkpoint](research-checkpoint-2026-10-07-nested-invariant.md)
验收实际成本／作者责任比较、进一步非同值与多数组 footprint 条件，继续更广
source/domain 与动态布局／BT。Kernel 仍止于 local correctness；四条逻辑链不
变成四份用户手填证明。完整目标 active，以下保留各阶段当时边界。

2026-10-07 最新后继：[紧凑公开出口](nested-compact-exit.md)已将当前 accepted
uniform nested 模型的 shadow traversal 替换为五个 temp 赋值，完整源出口、
检查后实际入口、candidate memory 和 Csem→Asm 均已证明。42 端点／606 依赖
审计、提取、762 assembly／381 Clight calls、较大域 60 assembly／45 Clight
calls／九个真实汇编 probes 通过。Guard、validator、kernel、语言 host 保持；
candidate 的出口对应由新 producer 交付，不新增使用者语义 callback。
Identity/interchange/tiling bytes 为 587/626/719。[配对完整计时](nested-compact-cost.md)
已通过 30 轮／1,200 batches：同值独立输入的 interchange 从相同 guard 的
shadow 版 1,521.1ns 降至 1,229.8ns，仍为 source 的约 1.35×；identity 为
约 0.88×。非同值 interchange／tile 仍为 source 的约 5.73×／7.65×。
新／旧 guard 的分派、prefix decisions/loads 在八个输入上完全相同；结果包含
backend/layout 效应，不把差值当作纯 shadow 成本。
下一项继续非同值 stability／多数组 alias 的 compact footprint 条件，并整理
语言库、domain 和 site 作者各自的证据及复用。更广 affine source、动态布局、
完整 BT 和新入口的 source-only fresh rebuild 仍待验收。Narrative 分支重新
fetch，仍为 `271f6fc`，两份正文与 main 一致。以下段落保留各阶段当时边界。

2026-10-07 当前：[单份扫描与较大域](nested-stability-shared.md)已关闭备用 scan
重复：interchange 762→644 bytes，原矩阵的 762 assembly／381 Clight calls 与
接受结果保持。新增 actual word=15／count≤16 profile 的 60 assembly calls、
45 Clight calls、九个未修改汇编 probes，区分两种 header alias 下的交换与 tiling，
并核对改变 header 后域增长的原源回退，见
[本轮 checkpoint](research-checkpoint-2026-10-07-nested-stability-shared.md)。
独立 23 端点／598 依赖审计、提取通过，
kernel／候选／语言 host 保持。较大同值输入的 stability queries 2,560→0，加两次
cache equality；numeric 等检查仍在，不能声称完整 guard 常数成本。

成本核对更正：numeric 是 first-path／参数区间检查，不是逐点扫描。单数组
same-word 接受路径的 stability scan 被跳过，alias-only code 为 `skip`，完整
guard 工作已不随域大小增长；其他路径及多数组 alias scan 仍有迭代工作。
当前 [完整成本](nested-stability-cost.md)已验收 30 轮／1,200 batches，完整数组与
公开状态前后核对，包含逐 call header reset。新同值 interchange 比旧版快，
但仍约为 source 的 1.65×；非同值独立输入约 5.91×。Guard-prefix 同值 decisions
4,673→17，说明紧凑 guard 不保证净收益。另 [numeric word facts](nested-numeric-word-facts.md)
生产真实 numeric/domain 充分事实，34 端点审计中四个新定理闭合；未替换 runtime。
当时下一项 **对已接受的固定矩形 nested 源生产紧凑 exit-domain/frame，替代
候选后的 shadow traversal，再验收完整计时**，现已由上述五赋值 producer
连接；本实例没有直接采用一般 last-path `affine_exit_statement`。不以成本
相减代替归因。非同值 stability／多数组 alias 的 footprint 条件继续推进。
Actual capture 许可、helper frame、模型入口及 host/candidate 责任必须保持。
作者数据／语言库／实例证明比较，以及更广 affine source、动态布局与完整 BT
仍按完整目标推进。以下记录保留前阶段范围，不能把旧 `.vo` 绑定称为当前验收。

2026-10-07 最新后继：[独立源码树复现](nested-frontend-reproduction.md)已从修复版
`1d3acc0` 的新空树通过 proof／extraction／全部既有 C matrix 和 probes。没有
历史 report／objects 输入，复用已安装 pinned toolchain；585 dependencies／20
queries，compiler 42-global 集合保持、kernel 闭合，未扩展 source class。
另 [constant-word observation](constant-word-observation.md)的 actual Clight BODY
checker／memory-effect producer 7 端点通过，6 项既有基线、零新增 global axiom。
它提供 fixed-cell observation 保持，不保证 pointer bindings／progress。
后继 [same-word producer](nested-word-model.md)已将实际循环的
observation 保持接到 cached source／canonical model，并证明两次缓存比较的
真实执行、接受义务和 actual check-exit ports frame；22 端点／508 依赖审计通过。
[same-word compiler](nested-stability-compiler.md)现已完成 actual physical guard、
multi adapter、typed factory 和新 Csem→Asm entry；新条件成立时跳过 stability scan，
其他路径保留旧 scan，原 candidate／host 证明直接复用。独立 19 端点／597 依赖
审计、提取、762 assembly calls、381 Clight dispatch calls 和四个未修改汇编
probes 通过。同输入旧 binary 对照新增两个 alias fast calls，局部地址查询下降，
但完整函数代码增长；详见
[新 checkpoint](research-checkpoint-2026-10-07-nested-stability.md)。
Narrative `271f6fc` 最新澄清继续约束验收。

下一项 **在相同 source／candidate 上降低备用 scan 的代码重复，并拓展 compact
condition 的有效范围；分别验收完整检查／program timing、代码大小及接受域，
建立三方作者需要提供的数据、库证明和实例证明对照**。Constant-word shortcut
不等于整份 guard 常数成本；一般 projection、动态布局、更多 affine source
classes 和完整 BT 适配仍继续按下列计划推进。完整目标 active，阶段完成不关闭目标。

以下为先前阶段；其中 fresh-build 待办已由上述后继关闭。

2026-10-07 后继：[nested frontend BODY／contexts](nested-frontend-coverage.md)已沿
同一实际 Csem→Asm compiler 验证多数组读写、真实 dependence、same-allocation
slices、alias 回退、BODY value wrap、重复 sites 与前后副作用／return。七类函数
的 default profile 为 714 assembly calls；提出 child-count∈[1,2) 的更强前提后，
同一 checker 接受原来被拒绝的 chain，另有 238 assembly calls 验证条件内 fast、
条件外回退。Clight 分支与 GDB machine probes 分列，不能用调用数推断通用性。

本轮重新 fetch narrative `271f6fc`，main 正文一致。吸收后的验收顺序为：

1. **可复现性**：建立 fresh-checkout、empty-build 路径，确认完整证明、提取与
   实际输入编译不依赖本工作树的旧 objects／reports。
2. **紧凑条件**：在同一 source/candidate 上用经认证的充分条件替换逐点扫描。
   语言证明 primitive 的安全／partiality 与状态运输，domain 证明新入口条件
   覆盖实际模型义务；复用候选和 host 证明，不要求新旧接受集合相同。
3. **OLO usability**：分别测量 guard work／完整运行成本、接受域、代码大小及
   编译成本；统计 kernel／语言库／domain／site 作者各自仍要提供的证据。
   Cursor loop 缩小代码不等于消除逐点检查，代码 bytes 也不等于优化收益。
4. **功能扩展**：推进更广 affine/polyhedral source、参数化域变换及原 BT 的
   动态布局／delinearization；按 source coverage、condition algorithm、未闭合
   证明或语义差别归因，不能用 verified 标签解释功能缺口。
5. **宿主接口复核**：从现有 finite／shared／open hosts 核对重复 clauses 和
   真正的 progress／control 差异，再决定是否抽取契约库。最小核保持局部
   correctness 边界，不先按文档建议增加抽象；每阶段同步实际 manuscript。

完整目标 active；本阶段没有修改 kernel／Rocq／compiler，也没有成本或作者
工作量测量。更详细的运行和证据边界见新 coverage 文档。

以下为先前固定阶段；其后继待办以本段及最新 checkpoint 为准。

2026-10-07：[actual nested frontend／native](nested-frontend-native.md)现已运行既有
Figure 2 适配 C，保留源文件和旧 coverage report。语言证明覆盖 `shape[0]` 零偏移
及 CompCert reset 前的 skips，原 AST 为 fallback key。新入口实际提取，identity／
interchange／2×3 tiling 安装；20-endpoint proof audit 及 48＋27 full assembly calls、
16 Clight branch calls、6 GDB machine probes 通过。真实 independent-array 写序
区分 source、interchange、tiling；两个 header regions 的 alias 均回退，完整数组
和公开 exits 对照一致。Kernel 不变，compiler baseline 42 项保持。
下一项 **在这个 frontend 上运行多数组 read/write、真实 dependence 静态拒绝、
same-allocation slices、非零 row、undefined BODY inputs、重复 rewrites 和 control
contexts，并提供 fresh-build 路径**；随后关闭 compact 条件、guard work／完整
运行成本、接受域、code growth／compile time和同例作者比较。不能借旧 root-only
矩阵替代新 frontend 验证，也不能把 code bytes 当成优化收益。完整目标 active。

以下为先前阶段固定记录，其后继待办以本段及最新 checkpoint 为准。

2026-10-07：[nested guarded candidate／compiler](nested-constant-multi.md)已接通：
canonical source 沿 ports frame 运到实际 physical guard exit，许可现有多数组
alias-only 检查；接受生产 private model anchor 和到 checked entry 的关系，供
候选 validator／实际 Clight lowering 和 public exit restoration 使用。既有 kernel
消费 guard／preservation certificates，实例交付 projected region contract；新 typed
factory 和 compiler 通过原 signed-expression region host 合成 Csem→Asm backward
simulation。三层原 AST 的 host progress 检查及三层 identity candidate 的实际 backend
代码有 fixture。最小 kernel 未改；dispatch 与整程序 installation 分别证明。
下一项 **提取新入口、实现实际 C descriptor／非 identity candidate、确认原 AST key
和真实候选安装，再运行完整非空数组接受／回退 matrix**。没有新 nested native 或
计时，不能改写 Figure 2 原 `not-supported` 报告；最终 compact 条件、成本／有用
接受域和同例作者工作仍分别验收。完整目标 active。

以下为先前阶段的固定记录；其中的后继待办以本段及最新 checkpoint 为准。

2026-10-07：[完整 header-stability guard](nested-constant-physical.md)已从 checked
原 site 生产 helper 后新入口，填入全部 outer scan 输入，合成真实代码；接受
取得 canonical Clight 与 Loop source 执行，model entry 明确 framed 到 actual
guard exit。39 端点（36 domain／3 fixture）、590 依赖／1,089 源摘要审计通过，
kernel／旧 compiler 保持。安全域仍是原 source silent normal completion。
下一项 **沿 frame 完成实际 candidate 的跨入口 context／pointer-cell 对应**，
接既有多数组 dependency/alias guard、candidate validator/lowering/public exits；
优先复用旧 loaded-offset multi 的模式：由数据 checker 取得 canonical source
scope，以 `structured_execution_temp_transport` 沿 ports frame 把已生产的 model
execution 运到实际 guard exit，再许可 alias guard／候选；不强求任意 location
map 完全相等。由 data-only factory 组装 guarded rule。随后接 typed pool、原源 key／fallback
及 language host 的合法 placement 和 **progress／divergence** 合同，完成新
Csem→Asm、extraction 和 active accepting／refusing native matrix。不能把 normal
completion 下的 guard theorem 等同于任意上下文的程序正确性。最终 compact
condition／成本／实用接受域／作者工作量仍各自验收。Figure 2 优化未安装，目标 active。

2026-10-07：[原 AST checked site／actual entry](nested-constant-site.md)现已绑定
实际 source、scope／fresh names、旧 package、scan namespace 与 lowering；observer
syntax 只依赖编译时地址表达式，runtime raw receipts 另从真实读取生产。
ROW0 profile 有实际 gate，入口 theorem 只消费原 source completion；接受后的
DOMAIN／SOURCE_WORDS／observers／initial prefix 均锚定实际检查后入口。37 端点
（4 language／23 domain／10 fixture）、584 依赖／1,083 源摘要审计通过。
Kernel 不变、旧 compiler 基线保持。Helper／outer／完整 guard 后继见上段；
candidate factory、typed pool 与 host 仍待完成。
没有新 compiler／extraction／native／timing，Figure 2 原 C 的优化仍未安装；
完整目标 active，最终 compact 条件／成本／接受域及作者工作要求保持。

2026-10-07：[原源 capture／numeric 输入生产](nested-constant-numeric.md)已从实际
first leaf 和旧参数使用 checker 生产参数定义性，执行有序 capture／双 gate，
numeric 接受后生产完整整数域及 outer scan 的逐点 `DOMAIN`／`SOURCE_WORDS`。
24 端点（6 language／11 domain／7 fixture）、565 依赖／1,076 源摘要审计通过；
kernel 闭合，旧 compiler 保持 42 项 assumptions。BODY 专用参数的 data-only
package 接受，空外层／内层在其余参数未定义时的实际拒绝均已证明。
其 checked-site 后继已由上段绑定 observer receipts、scope／namespace；helper
准备及完整 physical scan 消费者、guard／candidate factory 和 typed host 仍待组装。
没有新 compiler／extraction／native／timing。Figure 2 适配源仍未安装优化，
完整目标 active。紧凑条件、成本／接受域及同例作者工作继续按 narrative 验收。

2026-10-07：[完整三层 canonical 模型连接](nested-constant-model.md)已将合法的
双缓存源运输到旧 affine AST，并消费 checked package 取得真实 Loop 内存执行。
12 端点／557 依赖／1,071 源摘要审计通过；kernel 不变，旧 compiler 保持 42 项
assumptions。静态 leaf quiet/write 和本实例循环 frame 由证明生产，没有新增
source/model 语义回调。私有 helper 初始化与原 source freshness 仍须实际组装。
Capture／numeric 后继见上段；scope／namespace 及完整 guard 组装、真正原 AST
factory／typed pool／候选／host 尚待连接，随后提取和运行 Figure 2 适配源。
Empty／negative／unknown 的有序 gate 与原源回退一起验收。本阶段没有新
compiler／native，完整目标 active；compact 条件、成本／接受域与作者工作仍是
后续最终要求。

2026-10-07：[实际 outer scan／双缓存源](constant-joint-outer-scan.md)已从现有
inner producer 生产全部 rows 的 preservation，填入旧 two-cache transport，取得
原／缓存源的相同出口 temps 和 final memory。第一行拒绝、独立 empty outer guard
和无需 child cache 的语言 empty transport 有实际端点；kernel 不变，没有新增
BODY／PRESERVE 语义回调。14 端点／565 依赖／1,069 源摘要审计通过，旧 compiler
保持 42 项 assumptions。完整 canonical model 的后继见上段；原 capture／numeric
到 typed inputs 的实际 producer，以及原 AST factory／typed pool／候选／host 待连接。
没有新数组 fixture、提取、native 或计时；完整目标 active。

2026-10-07：[实际 inner 短路 loop／整行接受](constant-joint-inner-scan.md)已消费
原 BODY 的检查 producer，整行接受直接取得所有 column 的观察保持和 outer-prefix
advance。固定入口的 header 适配复用旧语言 prefix，guard 私有游标与逻辑 source
temps 分开；first refusal 和 empty child 的真实执行端点已证明。
14 端点／563 required dependencies／1,067 源摘要审计及旧 compiler／native 绑定核对
通过；kernel 无改动、无新增公理。
该阶段之后的实际 outer scan／完整 rows 及 cached source 已由上段连接；
canonical model 后继见首段，原 AST／typed pool／候选／host 和 compiler 尚未完成。

本轮重新 fetch／完整读取 narrative `271f6fc` 及 context-lifting，main 正文无差异；
[责任／实现核对](narrative-implementation-check-2026-10-06.md)已按 `ea55a6f` 更新到
实际 inner 消费者，消除把已接通 inner scan 列为待办的旧状态。
三方证明归属与四个逻辑证书环节分开；实际 guarded-choice 分派不代替整程序安装。
这一要求已由最新 outer 阶段落实：inner producer 生产全部 rows 的 preservation，
填入现有 cached-source transport，没有新增一个要求使用者假定它的 `PRESERVE` 回调。
原 source memory／guard-entry memory、private cursor 对应、empty outer／child
读门控和负 computed count 的实际回退策略分别验收。
继续把 kernel、条件库、language host 和具体 optimizer/site 的责任分开；
不把 `ENCODE`／coverage／`PRESERVE` 参数计作已实现 producer。
Reached constant body 许可的双观察 joint scan 和接受后的 inner-prefix preservation
已连接；实际 inner／outer 后继见上段。下一实现组装原 capture／numeric 的实际
输入 producer 与原 AST 安装；canonical model 后继见首段。
功能链闭合后验收 compact 条件、成本／接受域和
同例作者责任；相关里程碑同时更新实际稿件，不等待全部未来扩展。

前一 [实际 BODY joint scan](constant-body-joint-scan.md)消费 reached source permissions，
使用有实际求值／load receipts 的 observer expressions，保护两个 raw header words。
接受推出全部 point writes 分离及任意同 view 实际 BODY 的 preservation，填入 inner
prefix advance；具体 Figure 2 leaf 的五次原 store 和完整检查执行均有 fixture。
30 端点／569 required dependencies／1,064 源摘要审计及既有 compiler／native 绑定核对
通过，没有新 compiler、extraction、native 或 timing。完整 inner/outer scan 尚未
安装；下一项保持拒绝后不探测下一 BODY、empty outer 不读取 child，以及实际
source memory／guard-entry permission anchor 的区分。完整 goal active。

前一 [常量子循环模型／权限桥](constant-bound-model.md)：private helper 初始化有实际
Clight 执行和原 source public transport；原 literal-bound 子循环完成导出 affine 模型
及全部点在 guard entry 的 permissions，不预设 enclosing loaded headers 稳定。
14 端点／565 required dependencies／1,060 源摘要审计通过，旧 compiler 与 prior
对象绑定保持。其 reached inner BODY 权限已由上段消费；整段 cached model 和
original AST factory 仍未完成。该阶段没有新完整 compiler 或 native。

前一服务阶段是 [ordered child capture／层次源前缀](research-checkpoint-2026-10-06-nested-headers.md)：
外层实际进入才捕获 child；inner prefix 保留实际 source memory 和 global observation／permission
anchor；这一 row 的全部观察保持成立后才推进 outer。缓存源是接受后的结果，numeric probe
另从 captured words 许可。48 端点／571 依赖／1,057 摘要审计和原 Csem→Asm／native 绑定保持。
没有新 factory、提取或 native；完整 goal active。下一项连接实际 joint scan、canonical
cached model 和原源安装，同时保留紧凑条件与真实 guard 成本验收。

最近可运行阶段是 [loaded＋offset 根的完整程序接入](research-checkpoint-2026-10-06-loaded-offset-affine.md)：
真实 `i<*limit+1` 的 raw observation 保持扫描、接受后缓存源执行、候选验证、entry transport、
checked factory 和 signed-expression host 已连接到新 Csem→Asm 入口并提取运行。
56 端点／567 依赖／1,047 源摘要审计、六配置 708 次完整汇编调用、236 次 Clight 路径调用和
21 个未修改汇编探针通过。旧 expression-header／reduced 绑定保持。
[Figure 2 源覆盖探针](olo-figure2-coverage.md)仍未支持 loaded child；根加一接入没有关闭这个缺口。
下一项继续 dependent loaded child 的 reached capture／层次前缀，同时推进紧凑稳定性充分条件。
当前条件仍扫描访问点及跨数组点对；功能链闭合不等于 guard 成本已解决。

2026-10-06 更新。主目标仍是顺序 CompCert 中可运行的 verified guarded polyhedral transformation，PolCert 是功能与证明能力参照；片段选择和候选由用户提供，框架核心组合条件证据和局部 reasoning，语言 host 负责完整程序安装。完整目标没有因阶段结果而完成。

前一可运行接入是 [deep＋loaded multi native](research-checkpoint-2026-10-06-loaded-affine-multi-native.md)：
cache entry transport、稳定性之后的 alias 安全、旧 candidate validator／backend、原 loaded fallback、
语言 host、新 Csem→Asm、真实 frontend 和提取已连接。六配置 624 次 assembly 调用、208 次 Clight
路径调用和 21 个未修改汇编的路径探针通过，包含非空三层、多数组和同函数两次改写。
真实 C 暴露的 cache／counter 资源冲突已修复；独立 32 端点／692 依赖／1,021 源摘要审计通过，
compiler 保持旧 42 项假设，scan／旧 deep／当前 cursor 绑定保持。前一 factory 报告保留为历史，
不声称它仍绑定当前 factory。下一验收转为已声明范围的紧凑条件、成本及 CGO 2017 同例对照。

前一可运行交付是 [循环化 dependent guard compiler](research-checkpoint-2026-10-06-cursor-dependent-compiler.md)：真实 `**root` 源的两个 private captures、双观察稳定性、mapped／tiling／schedule 候选和 original fallback 已完整安装；实际 guard 改为两个短路私有 cursor 循环。43 个新证明端点、提取、两类 affine 域共 444 调用，以及 store-order／guard comparison-order 探针均通过。默认 cap 的完整函数从约 13 MB 的 Clight 打印体降到约 25 KB，机器函数大小也已单独核对；没有性能收益结论。以下阶段保留各自历史范围，当前未完成项以文末最新接入阶段的验收为准。

最新可运行交付是 [deep affine 接入当前证书接口](research-checkpoint-2026-10-06-materialized-affine.md)：复用已有递归 canonical 源／模型和候选 checker，Clight 新增正常返回的 private Boolean host；单／多指针使用者消费当前 kernel，并接实际 Csem→Asm、提取、十二配置共 5,118 次新 assembly 调用及四组独立 Clight 插桩。26 端点／462 依赖／982 源摘要审计通过，kernel 不变。旧 source IR 和多指针物理 scan 不是本次新增算法；stable-temp 深层域与两层 loaded/dependent 路线尚未组合。共享 `.vo` 重编导致旧冻结 cursor 对象绑定失配，当前消费者独立重编／535 依赖审计通过，原 42 项假设保持；152 个对象摘要已不同，不把旧 validator 称为通过。

本计划吸收 [三个分支的评审](review-synthesis-2026-10-05.md)。既有研究路线保留在 [contribution-plan.md](contribution-plan.md)，当前执行优先级以下表为准。

活动目标补充（用户 2026-10-06）：持续按 `topdown/research-positioning` 的 [paper narrative](topdown/paper-narrative.md) 改进整体定位；以“小的语言无关框架＋实质 CompCert 循环实例”组织研究，明确框架、语言实例、优化／domain 实现者的验证责任。具体约束与最难验收见 [责任矩阵](framework-responsibilities.md)。这项补充与原完整实现目标同时有效，每个阶段检查，不将方向文档算作功能完成。

最新 fetch 取得 `271f6fc`：新增 **CAV 2027 并行写作**。已建立
[实际 LNCS 稿件](../paper/README.md)，introduction／related work／framework 为正文，
case study／evaluation 写既有架构与待验收结果，逐节绑定源码、定理与一手文献。
每个相关实现里程碑同步改对应稿件和 evidence map；不等全部功能／测量完成才写，
也不把未完成结果写成贡献。写作与原 proof-first 功能目标并行，完整 goal active。
[首轮构建记录](manuscript-checkpoint-2026-10-06.md)保存 10 页 PDF／offline 构建、
渲染检查、一手文献范围和本轮 constant-body 证明同步；没有新运行测量。

上轮重新 fetch 并核对 narrative 澄清，分支仍为 `7d94d81`，主线正文一致。[实现责任与下一项验收](narrative-implementation-check-2026-10-06.md) 将 deep＋loaded 接入细化为：原源 first-path receipt → 安全物理扫描与覆盖 → 观察保持后的缓存运输 → 原 AST／fallback／host 安装。检查安全不能以完整缓存源执行或未来稳定性为前提。该核对阶段尚未交付新的 producer／compiler；下段记录实际后继结果。

[后继 numeric guard 阶段](research-checkpoint-2026-10-06-loaded-affine-numeric.md)已关闭上述 first-path producer：从原 loaded header／首次 body 取得递归 headers 和已用参数，安全 private capture 生产 prepared domain，再消费旧 numeric/profile 编码和现行 guard certificate。实际 source key、freshness 和检查体有静态 site checker；25 端点／660 依赖／987 源摘要审计通过，无新增公理，旧两条 Csem→Asm 回归和当前对象摘要保持。此接受仅证明 numeric math domain；下一项按原源前缀连接递归 physical scan、完整 coverage／fuel 和观察保持，之后才接缓存源／candidate／typed pool／whole-program host。本轮没有新增 compiler、提取或 native 调用，完整目标 active。

[后继 body prefix 阶段](research-checkpoint-2026-10-06-loaded-affine-body.md)已证明不固定维数的完整 body receipt、结构化 store 权限运输、接受后前缀推进与完整缓存源运输，并接到 checked recursive affine package。34 端点／665 依赖／992 源摘要审计通过，numeric 和两个当前 compiler 对象保持；具体 alias 源先改 bound 后退出，实际检查首次拒绝。下一项实现 recursive physical body probe：一个实际完成的 body 已许可其内部全部 child points，只有整个 body 检查接受后才推进下一 loaded root header。`BODY_CHECK` 的安全、完整覆盖和 byte separation→观察保持仍须由 domain library 实现；本阶段不称已交付深层 loaded optimizer／compiler。

10 月 6 日阶段同步吸收 `f793629` 的 cross-IR 补充：保持核心不依赖 Clight 语法；SSA／汇编使用者须实例化自己的控制、live-out／phi、scratch／flags 定律。它们是接口讨论和同例 related-work 比较的方向，第二 IR 实现是可选证据，当前主实现／验收继续是 CompCert/Clight。

[前一 body domain 阶段](research-checkpoint-2026-10-06-loaded-affine-body-domain.md)已实现前项中参数定义性、实际递归 child 模型、当前 body 的各点权限→guard entry 运输、private cursor 地址比较 domain，以及写 trace coverage／点写分离→实际观察保持。25 端点／674 依赖／1,001 源摘要审计通过，先前 body／numeric／compiler 绑定保持。它提供单点许可与 coverage；完整检查的后继验证范围单独列在下段。

[最新完整 scan 阶段](research-checkpoint-2026-10-06-loaded-affine-scan.md)已接合带包围 root coordinate 的递归 child scan、root 拒绝 break／前缀推进、实际 capture＋numeric＋runtime gate，并导出 cached-source receipt。静态 site checker 不暴露逐 body 安全性回调；当前 guard certificate 的 D 只有原 source completion。自别名 bound=2→1 的实际源／整段拒绝、同 block 相邻字的真实接受／缓存源执行，以及未定义 child 参数的零次迭代都已通过；38 端点／682 依赖／1,012 源摘要审计通过，kernel／既有对象绑定保持。下一项先连接旧多指针 alias guard 与 candidate checker，再接 typed pool、原 source key／fallback 和 whole-program host、Csem→Asm、提取与真实 C。新三层非空完整执行 fixture、多观察 dependent header、typed pointer-store body、P4 和同例证明负担仍未完成。本轮没有新增 compiler／native 能力，完整目标 active。

最新同步到 `8c098ed` 的 [context lifting](topdown/context-lifting.md)：kernel 的局部正确性与语言的程序安装分开陈述；host 提供可复用 region/boundary 契约，优化与具体位置提供 guarantee／placement 证据。已完成 [源码核对](clight-boundary-contract-review.md)，已有 temp/memory／scope／private 运输继续复用；finite 与 open 的 progress 是实质差异，不按自由 clause 组合重新设计 kernel。guarantee/requirement API 仍待实际受阻案例支持，不称已经实现。

最新 `7d94d81` 的 kernel 截止澄清已同步：只读前台、条件组合、prefix scan、simplification 和 assumption derivation 属于上层库；语言 host 承担完整程序安装。沿此边界继续实现和记录责任，不做无实例依据的文件重排或新 kernel 接口。

| 顺序 | 工作与状态 | 必须交付的验收 |
| --- | --- | --- |
| P0：本次交付 | 实现、实际 frontend 对应、提取与回归已通过；提交／push 以阶段记录为准 | 一个真正完整的 unsigned memory-bound 循环；guard 域来自有限源前缀；源／目标实际 alias 发散；540 次有限调用、六处新 loop 与两处混合旧 preload；401 端点／862 摘要、25 配置／40 报告绑定当前产物，39 份旧 C／Clight 摘要保持；准确文档并 push |
| P1：统一实际 realization | [公共设施](clight-guard-realization.md)与三个实际路径已接入；411 端点／863 摘要、25 配置／40 报告验证通过，相对 `26956a4` 的 40 份 C／Clight 摘要保持 | direct/shared 复用同一个 readonly condition 与 local rule，公共证书说明实际代码、私有资源／freshness、状态／观察运输、defined dispatch 和相应宿主模拟；两个 finite 安装路径和完整 unsigned 循环消费同一设施。分派前缀不要求分支完成；shared whole-loop 尚未安装，finite host 仍要求 source progress |
| P2：主多面体路线迁移 | [named rectangle 使用者](clight-polyhedral-preservation.md) 的证明、提取、40＋8 原生配置已通过；第二项 [参数化 affine 内层源／多类数组 body](clight-parametric-preservation.md) 通过 12 个证明端点、六份完整 C fixture／134 个原生配置，以及四个实际接受／回退顺序探针；主接口 415 端点／864 摘要保持；第三项实际参数化 pointer scan 已接入一般公共证书、kernel 保持、Csem→Asm 和提取，38 端点／15 个原生配置／四个执行顺序探针通过，另有 222 组完整上下文输入／三配置通过 | 不受信任的实际候选、源／候选对应、机器范围／alias 检查、private 观察、Csem→Asm 与提取接受／拒绝均通过公共接口；记录旧证书复用和专属义务。此次第二项仍不包含一般深度 affine polyhedron、指针切片或 stateful 足迹；单个新 helper 或脱离编译器的模型不计完成 |
| P3：一个符号化条件／足迹算法 | [盒状 affine 包络](affine-box-condition-derivation.md) 与实际宽度使用者通过 29 端点、完整证明／提取、134 配置和十个顺序探针，[证据](research-checkpoint-2026-10-06-envelope.md)。后继 [源观察 alias 编译入口](clight-observed-pointer-compiler.md) 已接实际 source matcher、三类候选、序列 placement、Csem→Asm 与提取；67 端点审计、十五原生配置各 376 调用和十个机器路径探针全部通过，[本阶段](research-checkpoint-2026-10-06-observed-compiler.md)保留分块首轮超时及八份绑定产物重执行的事实 | 固定受限 affine 表达／域和允许观察；输出条件和可核对证书；证明实际源实例覆盖、Boolean／机器表示、安全与接受蕴含语义前提；实际编译一个候选，给出拒绝策略和非空接受域。不把逻辑 projection 定理描述成已有 QE 实现 |
| P4：机制性能与复用量化 | [测量方案](native-performance-plan.md)和[schema](native-performance-report.schema.json)已采纳，尚未测量 | 同版原 CompCert 对照，实际接受／回退／静态拒绝分开；tree/simplified 的同源对照；最终 kernel bytes、guard／完整运行成本、编译成本、原始批次和环境。测量期间没有并发证明／构建；负收益照实报告 |
| 持续：已有工作／主张校准 | 保留 [cf4d442 证据矩阵](evidence-to-claim-2026-10-05.md)；新增 [Chamois／Peek 一手接口补核](related-work-interface-check-2026-10-06.md)，阶段性读取新评审 | Chamois oracle 签名和 CFG 扩展证明已取得，不再保留这两个访问未知项；动态条件推导能力和同例作者负担仍需核对。比较 OLO、Chamois、Peek 的安全、覆盖、freshness 和宿主义务；不以端点数、C 层或 abstract if 单独主张 novelty |
| 持续：论文方向与验证责任 | 目标的组成部分，沿 topdown narrative 更新 | 每个阶段区分框架证明、语言定律和 optimizer／domain 证书；分别落实 `C_opt`、`C_derive`、`C_guard`、`C_host`。重点验收 B 覆盖全部 A、guard 自身安全、实际模型对应、有限／无限宿主行为及证明复用，不以责任表代替这些证明 |

P0 关闭的是一个明确语义缺口。P1 服务于 P2 的真正接入；P2 是主功能目标的一次迁移验收，之后仍需一般 affine 域、复杂读写 body、依赖 preload 和布局组合。P3 是 optimizer/domain library 的受限推导算法，核心不承担 universal assumption extraction。P2 的首个使用者已实际消费候选／依赖核对和条件正确性；新的保持接口沿用旧证书在实际 globalenv 上的方向，与双向规则共享安装证明，没有改称等价或只重做 guard 包装。后续优先迁移参数化源／访问及真实 pointer footprint；区分可直接复用的 readonly 证书和需要私有检查状态的路线。P3 必须说明 `B⇒A` 的入口推导，再交给 `guard accepts⇒B` 的编码与 host。P3 与 P4 用来检验算法和实际价值，不将测量结果预设为收益。新增 [paper narrative](topdown/paper-narrative.md) 已在 P0 后同步读取并吸收。

P2 第二项已经复用 `encoded_private_rule`，接入参数化 readonly 使用者、实际 schedule generation／rechecking 与不同数组 body。第三项 [private-scan compiler](clight-private-check-migration.md) 将真实参数化 pointer footprint 接入一般公共 host 和 guard／preservation 证书：覆盖归纳检查安全、实际检查后状态、result 初始化、原入口 P、全部完成检查 sound、任意完成分支的 exact dispatch、分支运输及 kernel 消费。scope、private pool、source progress 和完整 CompCert 安装均沿用已证明的语言设施。38 端点、465 项实际依赖、812 份摘要；15 个原生配置各覆盖同一组 637 次调用，另有四个实际 disjoint 接受／alias 回退的汇编顺序探针。完整研究目标仍未完成。

参数化 readonly 结果见 [阶段记录](research-checkpoint-2026-10-06-parametric.md)，private-scan 的前一事实阶段见 [历史记录](research-checkpoint-2026-10-06-private-scan.md)，公共 pointer compiler 的证据见 [新阶段记录](research-checkpoint-2026-10-06-private-scan-compiler.md)。当前 pointer 源是稳定寄存器矩形 bounds 下的参数化仿射访问，不与 `j<U(i,parameters)` 非矩形源混称；source-derived D、footprint coverage 与范围理论仍复用既有 domain 证明，没有新增一般 projection 算法。

P3 已实现受限 affine 范围／足迹的符号化条件推导，明确允许观察和保守拒绝策略，输出可核对条件证书，并让实际候选消费。其范围仍是盒状源／受限 pointer package；一般 projection 不在已实现能力中。P4 仍需同版原 CompCert 对照、实际 guard／运行成本，以及与已有接口的同例证明负担比较。一般深度 affine pointer 域和多个依赖 preload 继续作为功能差距维护。

P3 的 pointer 快捷检查计划已据实际语义修正：`p+k` 是合法源访问，不蕴含原始 `p` 是 weak-valid pointer。CompCert 对指针比较的定义性要求因此不能仅由当前访问足迹推出；“先比较 base，再按 offset 包络判分离”不能直接插入普通循环。只有源前缀或合法 placement 证书提供比较所需的实际地址有效性时才可接入，不将它偷偷加进 source-derived D。首次实现切口是通用盒状 affine 包络及有符号参数范围编码，替换参数化 readonly 源的宽度检查，让真实候选消费所有迭代点的覆盖证明；该 compiler 的 pointer scan 保留。后继新入口在 source receipt 足够时支持 alias 快捷接受，拒绝继续原 scan。旧宽度检查本来也是一轴符号化 endpoint 检查，替换它不等于已消除 footprint 枚举或实现一般 projection。

P3 后继的 [源观察与 alias 包络](source-observed-affine-separation.md) 实现真实 prefix receipt、实际 Boolean 编码、modular 四字节分离、全部源 footprint coverage 及 readonly shortcut／原 scan 的局部组合。[完整 compiler](clight-observed-pointer-compiler.md) 进一步绑定 normalized source AST，复用原 mapped／tiling／schedule checker，并通过已证明的 sequence progress 接到程序。真实 prefix load 与后缀 store 均保留；机器路径探针确认快捷接受跳过扫描、拒绝继续扫描，随后选择候选或源循环。缺失／破坏观察许可时只能使用原 scan。

共享 fallback 的实际 lowering 已接入 [共用 compiler factory](clight-shared-pointer-shortcut.md)：同一入口按 Boolean 选择 direct／shared，同一 source matcher、三类 candidate checker、D／P 和条件推导只有一份。语言层新增真实正常执行运输，核心未变，优化方不重证 C_opt／coverage。79 端点审计、提取、两个完整十五配置矩阵及二十个机器路径探针通过；本轮三十个配置全部新编译，共 11,280 次配置内调用，十五份 direct Clight 摘要与冻结基线一致，见 [阶段记录](research-checkpoint-2026-10-06-shared-pointer.md)。已通过的二维 interchange 配置将 scan AST 13→1、linked 函数 11,750→1,566 字节；候选仍可重复，两个对称 base 比较保留，尚无运行成本测量。后续优先扩展非盒状 affine pointer 域和依赖 preload，并按 P4 在无并发构建时测量同版 CompCert 对照。优化作者的 obligations／证明负担继续单独统计，与 related work 做同例对照。

下一阶段的具体非矩形 pointer 切口、三方义务、包络与安全扫描的区别及验收见 [affine pointer 域计划](affine-pointer-domain-next.md)。先关闭真实域／候选对应和非空符号接受，再扩依赖 preload；不把 bounding box 当作源权限覆盖的扫描域。

非矩形 pointer 接入的前一阶段交付局部证明支持：语言的 framed source decode／实际 first-body frame；domain 的 `[i;j]++entry_context` Loop、实际 pointer 源对应、ragged footprint／capability／包络覆盖；原 candidate checker 的显式源模型接口，以及候选 Clight lowering 与公开 affine 出口恢复。核心未改，原矩形包络实例复用同一 pair compiler／物理分离服务。

该支持阶段通过 36 端点／515 项实际依赖审计；原 compiler 经当前 81 端点审计、重新提取与两模式各一配置的 376 次调用回归，见 [新记录](research-checkpoint-2026-10-06-affine-pointer-support.md)。候选运输与条件支持已有具体三角域实例，尚未由新 package 组装。全十五配置没有重跑，新 pass 没有原生运行；此前 `f144d45` 的完整矩阵继续是冻结历史证据。计划与 goal 保持未完成。

后继 [源 package 与条件阶段](research-checkpoint-2026-10-06-affine-pointer-source.md) 已实现 normalized AST／元数据 checker，并从真实源有限正常执行取得 header／body 参数读取证据；按 row／N、header range、width、body range 组织 readonly condition，消费 kernel 的组合服务。其实际接受已经接到同一 package 的 pointer 源 Loop 执行和精确公开出口；旧一维 affine-access API 保留。Clight fixture 证明接受，以及破坏增量、窗口、pointer 覆盖、未使用几何的拒绝；n=0 的实际 decision_run 不读取未定义 body 参数。

后继 [完整 source guard](research-checkpoint-2026-10-06-affine-pointer-alias.md) 已将保留 prefix 的真实 pointer receipt、实际域包络／物理 non-alias 接到同一 source package 和入口，继续消费 kernel sequencing。静态 column cap 先在 domain 层代入 endpoint，语言层复用 modular 求值和 signed 范围编码；不需要虚构源 count 寄存器。79 端点／526 项依赖／871 份源码摘要审计通过，没有新增全局公理。完整条件接受已绑定实际源 Loop／精确公开出口，尚未绑定新的候选或完整程序。

后继 [非矩形 pointer compiler](clight-affine-inner-pointer-compiler.md) 已关闭上述同一入口连接：两套 candidate ranges、独立 mapped-domain／dependence certificate、实际 lowering／公开出口 restore 和 local rule；normalized source/prefix/suffix 运输接入已有 progress／placement host，得到新 `compile_affine_inner_pointer_correct`。原进展 checker 在具体新源 fixture 上通过，没有重复发明宿主定律。103 端点／533 项依赖／878 份摘要审计和提取通过；六个新原生配置每个 81 次调用、共 486 次，五个机器路径探针区分真正候选／源执行。实际 `j<i+1`、`j<2*i+1` 的不受信任候选和 schedule generation 均已选中；错误域、直接除法边界、资源耗尽与缺失 source receipt 保留源。该结果独立于旧 compiler/native 矩阵。

本次也明确了 optimizer/domain 的一项表示责任：generated 参数检查含 `2147483648` 或 `-a` 时不能直接降到 signed32，除法边界也不能直接通过 affine extractor。不受信任的候选整理器提出参数 guard 删除与粗范围／affine 条件替换，整个结果再经原 checker；不把整理器当作 `C_guard` 的证明或可信 residualizer。两个实际域消费同一证书和 host，kernel 未改，性能和作者负担尚未测量。

后继 [nonrectangular pointer tiling](research-checkpoint-2026-10-06-affine-pointer-tiling.md) 已把实际 candidate Loop 和 quotient witness 接到同一 package、候选证书与完整编译器；2×3／4×1 在两个源域实际安装，错误 link、缺失源点和非正 tile 大小拒绝。mapped／tiling 共用条件、restore 和 local contract，kernel／语言 host 未改。109 端点／535 依赖／879 摘要、十一原生配置共 891 调用和七个机器路径通过。tile 控制数来自 metadata caps 的编译时除法，不宣称已有通用运行时 floor/ceil lowering。前阶段的 103 端点／六配置记录保留为历史证据。

后续按难点排序：优先实现多个依赖 preload 的安全读序、原入口事实和参数稳定性，再推广一般深层 affine 域。当前完整 guard 的 D 仍使用有限正常源完成和 retained source receipt，不能替代依赖加载／无限源的有限前缀协议。保守不同-base 拒绝与真实 ragged scan 的组合也需独立 capability／private-state 证明。P4 和同例 near-neighbor／作者 obligations 比较继续有效，完整 goal 保持 active。

OLO 的需求验收仍以义务区分：当前已安装实例提供机器范围／no-wrap、真实 nonrectangular footprint、物理 alias 条件、mapped／tiling 候选依赖保持和全程序安装；该 compiler 尚未覆盖每次循环测试重新读取的 memory bound。不能把“源已 preload 到稳定寄存器”作为这一困难情形已解决的证据。

后继 [loaded pointer 局部规则](research-checkpoint-2026-10-06-affine-loaded-pointer.md) 已证明一个真实三角源的 bound 反复读取／缓存运输，并接到原候选证书与保留 prefix 的 contract。语言提供 preload 值观察和 active-loop 运输；domain 提供 byte 级观察保持、保守 affine cell exclusion，以及 source 活动支持的 first-body words。kernel 未改，实际 full condition 消费依赖顺序组合，D 不预设未来稳定性。31 端点／540 依赖／884 摘要审计通过，无新增全局公理；原 42 假设 compiler 独立回归通过，原 891 调用报告重新核对绑定、未重执行。

该局部阶段当时没有新 loaded 选择器、完整程序端点、提取或原生结果。其安装验收要求 source progress 不假设 bound 稳定，并实际连接 frontend／matcher、原候选工厂、完整程序端点和运行证据；各项不能互相替代。

后继 [loaded placement 阶段](research-checkpoint-2026-10-06-loaded-placement.md) 已关闭语言 progress 和程序证明连接。strict signed nested 协议按机器最大值计算距离，不依赖 memory bound；真实 AST checker 允许 body 改写 bound 单元，拒绝改写外层 iterator。table host 复用 private-pool、scope 与原程序安装定理。固定 source profile 的 mapped／tiling／schedule checker 已消费原 loaded 局部 contract，支持 sequence association 和保留 quiet suffix，得到新的 Csem→Asm endpoint；kernel 未修改。55 端点／546 依赖／890 摘要审计通过，无新增全局公理；新 compiler 与独立旧 regression 均继承 42 项假设。旧 891 调用报告再次核对绑定，没有重执行。

下一项优先推广这个 source adapter 到真实 frontend names／AST，并在完整 C 上给出非空候选接受、提取、回退／alias／公开出口／外围上下文的原生证据。当前 profile 的固定标识符和 proof endpoint 不构成这项功能验收。随后推广任意 bound pointer 与多个依赖 preload；后项读取的许可、original-entry 条件和 private snapshot 稳定性继续独立验收。本例使用源已有公开 preload，仍使用有限正常源完成域，不宣称解决全部依赖读取或一般无限源。更一般深层域、P4 和同例作者负担保持在目标内。

## 每个阶段固定记录什么

1. 输入／候选／condition 的实际定义和选择器支持域；selector cap 与局部定理范围分别列出。
2. D 从哪里获得，P 在哪里建立，哪些后续访问需要已接受事实；不得在 D 偷放 P。
3. 局部有限等价或小步协议、公开出口／frame、宿主覆盖的发散和控制出口。
4. 完整程序端点、继承假设、源码／报告／编译器 stamp；native 回归与形式证明各自的边界。
5. 同一 source／D／P／candidate 下复用了什么，专属 obligations 和 proof code 有多少；新增模板不自动计作独立贡献。
6. 未完成项、评审意见处理状态、commit 与远端 push。原评审保存固定 SHA，新状态另记，不把历史判断默默改成当前事实。
7. 三方责任与难点：框架新增服务、语言实例新定律、优化方专属 proof／checker 各是什么；最难义务实际如何关闭，哪些仍由调用者承担。更新 [责任矩阵](framework-responsibilities.md) 和研究定位。

接口原则保持不变：最小 kernel 的 `select_exact`／局部证书组合保持；只读前台是上层库；语言实例解释语义、观察、安全和控制，使用者决定寻找片段、rewrite 提案、遍历、优先级与资源预算。框架不能只要求一份任意等价定理，而要通过实际复用的检查、frame、表示和上下文设施降低规则作者工作。

## 阶段性读取评审

完成 P0、冻结 P1 接口、完成 P2 迁移，以及取得第一批 P4 样本时，重新同步评审分支，记录新增 SHA 和相对上次读取的变化。每条新增意见更新“采纳／已解决／仍待证／未采纳理由”及对应验收，不仅追加阅读链接。正文中历史能力按其固定提交解释，当前主张依最新实际产物更新；不因评审分支比 main 旧就整体忽略意见，也不把已被后续证明关闭的缺口继续列为当前缺口。


## 参数化 memory-loaded 源的完整运行验收

[本阶段](research-checkpoint-2026-10-06-affine-loaded-compiler.md) 已关闭固定标识符、真实 frontend 接受、提取和原生验收缺口。源 snapshot 可处在直接 load prefix 的任意位置，输出须唯一且不覆盖 pointer；checked source/metadata 来自实际 AST。新 source evidence 接口以真实 loaded header/body 提供机器值读取证据，再执行 range/width 检查、全部实际 write exclusion、loaded→cached 运输和原候选 checker。框架原 sequencing、语言 progress/host/backend 继续被实际入口消费。47 端点／549 依赖／893 源摘要审计和新 Csem→Asm、提取通过；十一新编译配置各 150 次调用，七个机器探针确认候选和原 loaded fallback。

下一必交付调整为独立 bound pointer 的动态 write-footprint 分离：source 保留的 bound load 要能进入当前 source package，alias/bound stability 条件共同覆盖所有 stores，guard 失败仍用不预置稳定性的语言 host。之后实现依赖 preload 的安全读序和 private snapshot，扩展一般深层 affine 源。当前同 write-buffer cell 0 的静态 exclusion 不称动态任意 pointer 支持；新版 preparation 接口先由 loaded 入口消费，旧 cached 入口仍保留原证明，尚未证明总 proof burden 降低。P4 和同例 related-work/作者负担验收继续独立，完整目标 active。

## 独立 bound pointer：源顺序稳定性证明服务

[本阶段](research-checkpoint-2026-10-06-affine-loaded-stability.md)完成实际 stores 到原 guard entry 的权限运输、实际完整 row 的 write receipts、坐标替换后的 Clight 地址求值、支持不同 blocks 的 pointer equality／物理分离，以及实际当前行 guard 的安全／完成／接受保持。语言的 loaded-prefix invariant 保存剩余真实源执行，正结果才允许续行；没有在 D 中放未来 bound 稳定性。上层 prefix library 被实际消费，kernel 不变。

下一必交付保持独立 bound pointer 的完整安装，顺序固定为：

1. checked source package 消费现有 range／word／row-decode 定理，证明每次到达的 `memory_affine_row_domain`；完成初始 loaded-prefix witness 和足够 fuel 的覆盖证明。不得把界限稳定性或完整未来 footprint 当作安全域。
2. 让实际逐行 guard 消费上述实例证书，推出全部实际源 writes 的观察保持，并接到新的 external loaded→cached 运输与原 mapped／tiling candidate 证书。
3. matcher 接受独立 bound pointer，核对它受 frame 保护并来自 retained source read；保留真正 loaded fallback，复用语言 progress／placement，取得 Csem→Asm、提取和完整 C 运行证据。
4. 验收独立 blocks、同 block 不同 offsets、写中 bound 后提前停的源、当前行 alias 拒绝而后续危险地址不被检查。记录 guard AST／shared lowering 成本，性能独立测量。

本阶段是证明服务，不称已经完成这个安装。当前行 domain／decoder 仍由实例证明；编译器能力仍以此前 loaded compiler 为准。之后才推进依赖 preload 和 private snapshot。


## 独立 bound pointer：实例和 compiler proof 已连接

[本阶段](research-checkpoint-2026-10-06-affine-dynamic-loaded.md)已完成上一列表的前两项，以及第三项的 matcher／候选／Csem→Asm 证明：实际 checked package 填完所有 scan callbacks，range 与 count/width 证书证明足够 fuel 覆盖；完整分离 guard 接到 exact loaded→cached 运输及原 mapped／tiling／schedule checker。新 normalized AST fixtures 核对独立 pointer 接受、缺 receipt／pointer 覆盖／控制变量冲突拒绝。最小 kernel 不变，原上层 prefix/sequencing 库和语言 host 被实际消费。

提取／真实 C frontend／原生验收仍未完成。新的优先顺序为：

1. 保留 sequential/branching 结构的检查 plan 或 nested scan lowering，避免在每个 row 的接受出口复制后续扫描。实际 syntax fixture 已显示此增长；单独共享 candidate/fallback 不解决它。
2. 证明新 lowering 与已认证 guard 的求值／短路顺序对应，公开 temp/memory frame、private result/cursor、checked-entry 与 defined dispatch；复用既有安装 host。
3. 提取新 compiler、绑定真实 C，运行独立 blocks／同 block 不同 offsets／bound 被写后提前停／alias 后危险后续地址未求值；机器探针验证候选与 repeated-load fallback。
4. 完成这一运行验收后，推进依赖 preload／private snapshot 和一般深层 affine 源。性能与同例作者负担仍独立验收，不把编译定理或 AST 计数当作这些结果。

原 1,650／891 次调用的 native 报告仅重新核对产物绑定，本阶段没有重执行旧矩阵，也不把旧结果算作独立 pointer 新运行证据。完整 goal 保持 active。

## 独立 bound pointer：顺序 plan 与完整运行已验收

[后继阶段](research-checkpoint-2026-10-06-affine-planned-loaded.md)已关闭上述顺序 plan、private frame／defined dispatch、提取、真实 C 和机器路径缺口。plan 直接降低为顺序 Clight，旧 tree 只作为证明规格，提取不包含其展开函数；原完整条件、源 package、三类候选 certificate 和语言安装 host 被实际复用。119 端点／587 依赖／931 摘要审计，六个新编译配置各 37 调用、十三个机器探针通过。不同 blocks 的 bound 和同 block 的非写 offset 确实接受；第一／第二行写中 bound 确实保留提前停止；小数组探针确认拒绝后不执行未来 row 的地址比较。默认 64×64 caps 也有实际安装和候选运行证据。

这一进展没有改变 kernel 截止位置。语言 plan/code 对应、scratch 初始化、frame 和实际分派是上层库；优化实例证明 plan 等于原条件，host 继续负责 source progress 和 Csem→Asm。当前保持有限正常源完成域；不将正常 branch 运输定理扩大成一般 divergence／任意控制出口支持。body alias 的同-base 快捷条件仍保守拒绝不同 body base。

新的优先验收：

1. 原源没有 public bound snapshot 时，插入 fresh private snapshot。由实际到达的原 header 证明读安全，保留 original-entry 谓词并证明 private/public 运输；源 fallback 保持 repeated-load 语义。单独记录新增 matcher、私有资源和 placement 证据，不用一条假设或预置稳定性替代这些证明。
2. 扩展多个依赖读取的合法顺序、定义性、stores 稳定性；body pointer 观察不能因被命名为 preload 就自动合法。复用当前 prefix／private-state 库，真实案例受阻才讨论 kernel 接口。
3. 将按 cap 展开的 scan 循环化或进一步符号化。当前默认 cap 的完整 Clight 函数有 12,518 个 if，虽然消除了旧 tree 的 continuation 复制，代码成本仍需处理；与 P4 的完整成本、同版 CompCert 对照及同例作者负担比较分别验收。
4. 扩展一般深层 affine 源／复杂 body 和不同 body base 的物理 alias 条件；当前新运行矩阵是独立 bound 的三角源，不与旧两域矩阵混称。

旧两个 native validator 的绑定复核通过，矩阵未重执行。narrative 仍为 `7d94d81`，本地正文与再次 fetched 分支一致，另两个评审分支也无新增。完整 goal active。

## Private snapshot：原 source scope 与两类 affine 源已验收

[新阶段](research-checkpoint-2026-10-06-affine-private-loaded.md)关闭上一列表的第一项：语言 preparation 桥由原 source 的实际首次 header 取得 typed read，在原入口安全插入一个 fresh private cache；只用 public agreement 运输执行，消费 prepared source 的扩展 scope 契约后收回原 scope。真正原 source 仍为安装 key，原 host 的 source progress 保持，不要求使用者另证中间源 progress。新的 domain adapter 委托整个既有 planned-loaded factory，没有重证条件／候选或修改 kernel。

审计 140 端点／43 语言端点／592 依赖／936 source 摘要，提取和三角域、`j<2*i+1` 各六配置共 444 次新入口调用通过。74 次旧入口同源对照确认其静态不安装；28 个机器探针含两个旧入口对照。新增实际 bound cache 私有，公开 marker 始终为 123；写中 bound 的源提前停止和只有第一行合法的短数组得到保持。旧三套矩阵只绑定复核，不计入新验收。仍需源已有 body-pointer receipts，当前功能不包括依赖 dereference。

当前后继优先顺序：

1. **多个依赖 header 读取。** 以 `i<**pp` 这类真实源为切口，语言从实际 header 分别提供 pointer-cell 和 bound-cell receipt；domain 证明两种 chunk 的 byte footprint 排除、正结果之后才安全推进的源前缀，以及接受后两次观察的保持。原复合 header fallback 必须保留。private capture 的运输桥继续复用，不能把已有单个 `Mint32` 不等比较推广为 `Mint64`／`Mint32` 不重叠。
2. **guard 大小与成本。** 按 cap 展开仍产生约 12,500 个 if；实现 scan 循环化或经证书的符号足迹，继续独立 P4 测量。公开 AST 文本、最终机器大小、编译成本和执行成本分开报告；当前没有性能收益结论。
3. **主 domain 表达力。** 一般深层 affine 源、复杂 body、多参数／布局组合及不同 body base 的物理 alias 接受。两个实际 affine 域是本次表达力证据，但不代表任意多面体已迁移完成。
4. **同例责任与已有工作比较。** 用当前私有读取／前缀安全例检查 OLO、Chamois、Peek／COVE、CoreJIT 的条件、语言、安装义务；记录真正复用的 certificate 链，尚不主张 total proof burden 或 novelty 收益。

沿 narrative `7d94d81`，上述读取／条件推导留在语言和 domain 库，kernel 仍只组合局部证书；host 负责 progress／context 安装。guarantee/requirement clause API、第二 IR 或新 kernel 能力只有实际接入受阻时才推进。完整 goal active。

## 依赖 header：服务已证明，完整实例继续接入

[最新阶段](research-checkpoint-2026-10-06-dependent-header.md)落实上述第一项中的语言与逐点 domain 服务：实际 `**pp` header 的两个 typed reads、安全 ordered captures／public-scope preparation、不同 chunk 的 byte separation、实际 affine write sequence 保持两项观察、全部观察保持后才推进的 prefix，以及 source→cached 实际执行运输。另有 signed-expression progress selector，不把未来稳定性写进 source progress。九个新增模块、51 端点审计通过；没有新 native 或 compiler 入口。

下一验收按依赖顺序推进：

1. 从真实 checked affine package 生产 joint row／outer scan 的所有证据：实际 header、row decode、全部坐标范围、write receipts 与足够 fuel。使用现有 concrete HEADER 和逐点双观察 condition；不以 generic scan 的参数或 exhaustion 冒充源覆盖。
2. 接完整 guard 到原三类 candidate certificate，保留原 `**pp` fallback；actual host 消费新 progress selector，并落实 pointer／bound／Boolean／counter private pool 的不同类型、freshness 和真正 original source key。
3. 提取新入口，运行完整 C 接受／回退／上下文。当前 memory 后半单元重叠 fixture 不是 defined C loop benchmark；先用合法 bound 改写拒绝和稳定依赖读取接受。需要 typed pointer-store body 才能覆盖合法改变 pointer cell 的更一般源，不能将 progress fixture 计作 optimizer body 支持。

guard 循环化、一般深层域、不同 body base 的 alias 接受、P4 和同例 proof obligations 比较保留后继优先级。该接入不要求新 kernel 能力，完整 goal active。

## Dependent compiler 接入：完整局部链已证明

[后继阶段](research-checkpoint-2026-10-06-dependent-joint.md)关闭上一节第一项并连接第二项的候选证明：真正 checked affine package 填入所有 header／body decode／word ranges／write receipts，内外两层 scan caps 覆盖全部活动写入；接受后运输实际 `**pp` 到 cached source，原 candidate certificate 给出实际 candidate execution。首次真实 header/body 生产 preparation evidence；完整局部链接受／拒绝都保持最终 memory 和公开 temps。七模块、29 端点审计通过，原 kernel 和 checker 保持。

仍未关闭 factory 和完整入口。当前优先：原 compound AST matcher／source key；在真实 prefix 后捕获两项 private observation 并生产上述入口域；pointer／integer／Boolean／counter 的 typed fresh pool；保留顺序 continuation 的 plan lowering；实际 host 消费新 progress selector 并接 Csem→Asm。完成后单独提取、运行合法完整 C 接受／回退／上下文；不将本轮局部 theorem 或 inherited private compiler 回归算作 dependent native 结果。

已证明的 generic callbacks 不再列为该 checked package 的未知项；capture domain producer、语言安装和实际运行仍明确保留。一般 pointer-store body、循环化 guard、主 domain 扩展、P4 与同例已有工作比较继续后继验收。完整 goal active。

## Dependent compiler：原源安装、提取和完整 C 已验收

[最新阶段](research-checkpoint-2026-10-06-dependent-compiler.md)关闭上一节的实际接入义务。matcher 对真正 `**root` normalized AST 核对类型和增量，内部 cached model 消费同一 checked affine package；原源保留为安装 key。safe captures 后的入口 producer 从实际 prefix／首次 header 取得 pointer、bound 和 body receipts。19-slot private pool 区分 pointer cache、integer bound、Boolean 和 counters；顺序 plan 与原完整 condition 精确对应，实际 host 消费不预置稳定性的 source progress，并接到新的 Csem→Asm 定理。

九个新模块、40 端点／531 依赖／961 源摘要审计和提取通过，完整 compiler 沿原 42 项假设基线。三角域和 `j<2*i+1` 各六配置共 444 次新入口调用、28 个 store-order 机器探针通过；74 次旧入口同源对照另记，不安装变换。实际 guard 接受进入 reordered candidate；bound 改写、body alias、cap 拒绝保留原 compound-load 源与公开出口。小数组检查输出和 store order；本轮没有独立机器 comparison-order 观测，不扩大为此项证据。

当前后继优先级：

1. **Guard 扫描成本。** 默认 64×64 cap 的实际完整 Clight 函数已增长为 20,710／20,711 个 if，打印体约 13 MB。优先实现循环化或经证书的符号足迹；复用当前安全／观察保持／candidate 链，再核对私有 cursor、进展、短路、frame 和实际分派。语言与 domain 库承担这些义务，除非出现真正无法表达的语义责任，不改 kernel。
2. **主 domain 表达力。** 推广一般深层 affine 源、复杂 body、多参数／布局和不同 body base 的物理 alias 接受。当前 body 仍是 Mint32 操作，保留源 body-pointer receipts；两级 header 不代表任意 dependent preload 或 typed pointer stores 都已支持。
3. **合法 pointer-cell 变化。** 设计实际 pointer-store body／source correspondence 和双观察拒绝例；不能把 Mint32 覆盖 Mptr 后半的 memory fixture 当作合法 C benchmark。
4. **实证与比较。** 继续 P4 的 guard／代码／编译／执行成本和同版 CompCert 对照；用同一 source／condition／candidate 比较 OLO、Chamois、Peek／COVE、CoreJIT 的责任与作者负担，不将 444 次调用当作 generality／novelty 或 profitability 证据。

本阶段再次 fetch 后 narrative 仍为 `7d94d81`，本地正文与远端一致；其最小 kernel 截止继续是局部 guarded correctness。condition processing／prefix 是库，language host 提供完整程序安装，domain 提供模型义务及条件推导。没有按文档边界重排文件或新增 kernel API。完整 goal active。

## Cursor scan：逐行实际 lowering 已证明，完整成本接入继续

[新服务阶段](research-checkpoint-2026-10-06-cursor-scan.md)落实上一节 guard 成本的第一步：语言库提供先初始化、inactive／拒绝即退出、仅接受时 increment 的真实私有 cursor 循环；domain 的符号列地址模板精确对应原逐点双观察 probe，整行逻辑规格等于原 row condition。原 reached-row 域生产检查可用性，实际有限执行取得 primitive safety；任意实际完成且返回 true 的行扫描复用原 physical-write 观察保持定理。七模块／34 端点／531 依赖／968 source 摘要审计通过，全部新端点在原 CompCert 基线内，旧 dependent compiler 保持 42 项假设。

当前未连接 outer scan、实际 resource checker／factory、whole-program 安装、提取或新 native。上述约 20,700 个 if 的完整函数仍是当前 compiler 的真实成本，不用一份循环体的服务定理代替成本验收。后继顺序：

1. 从 checked package 和 typed pool 生产 cursor／result freshness、public read scope；把 outer prefix 推进和全部 rows 覆盖接到实际循环，不提前求值失去许可的后续地址。
2. 保留同一原 source key、实际 preparation／候选／fallback，连接新 lowering 的 dispatch／frame／progress 到现有语言 host；取得新的完整 compiler endpoint。
3. 提取和真实 C 验收接受／拒绝／bound 早停／上下文，单独测量 Clight 和机器代码大小、编译成本和 guard 执行成本。

本阶段再次 fetch 仍为 narrative `7d94d81`，本地正文和 context note 与远端一致；最小 kernel 截止继续约束以上责任。旧两套 native validators 只复核冻结绑定，没有重跑矩阵。一般 domain／physical alias／pointer stores、P4 和同例作者负担比较保持后继任务，完整 goal active。

## 循环化 Guard：实际 Compiler 与成本规模已接入

[最新阶段](research-checkpoint-2026-10-06-cursor-dependent-compiler.md)关闭上一列表的 outer scan、有限 resource checker、实际 factory、whole-program endpoint、提取和两域完整 C 验收。新嵌套 scan 精确对应旧完整 stability condition，原 checked package 填入扫描 callbacks，原 coverage／两项观察保持／candidate certificate 和语言 host 被复用；kernel 不变。typed pool 增为 21 槽，guard cursors 与 candidate counters 分开，保留真正 original compound source key 与 fallback。

43 端点／537 依赖／976 source 摘要审计和提取通过，完整 compiler 保持原 42 项假设。两个域六配置共 444 次新入口调用、28 store-order 探针（含两个旧入口对照）、18 个新 guard comparison 探针通过。默认 64×64 cap 的完整函数从 20,710／20,711 个 if 降为 111／112，Clight 打印体约 13 MB→25 KB；linked 函数 72,083／105,857→879／916 字节。同源／候选／caps 的旧新产物、输出和代码大小均绑定；旧矩阵只复核，没有重跑。编译与执行时间未测量，不把这组代码规模结果称为 P4 完成。

当前后继优先级：

1. **主 domain 表达力。** 先把已有 `prototype/affine-nest/` 的递归 canonical 源、多参数和真实多指针 body 接入当前 kernel。该 IR／源对应／候选检查器已存在，不能重新包装成新算法。然后逐项检验深层 stable-temp 域与 memory-loaded／依赖读取的组合、一般域限制和复杂 body；已有两个 affine 域的调用数不代替这些验收。
2. **物理 alias 与依赖读取的组合。** 已有 affine-nest 多指针扫描可按真实访问点接受不同 blocks，或同一存储的分离 views。需要把它与 loaded-bound／多观察稳定性路线组合，并落实真实 typed pointer-store body 的 source correspondence／双观察拒绝；Mint32 写操作不能冒充合法 pointer-cell 改写。
3. **P4 独立计时。** 现在有紧凑的实际 compiler，可以按已有 schema 测同版原 CompCert、接受／回退／静态拒绝的 guard 与完整运行成本、编译成本和批次环境。无并发构建时测量，负收益照实报告；代码大小已经核对但不替代计时。
4. **同例责任与已有工作。** 用同一 source／candidate／condition 梳理 OLO、Chamois、Peek／COVE、CoreJIT 的 guard 安全、`B⇒A`、状态和 host 义务；记录本次真实复用的旧证书和新的 language/domain 证明，不主张 total proof burden 或 novelty 收益。

再次读取 narrative `7d94d81` 的 cutoff 澄清：最小 kernel 只组合局部证书；条件处理库可复用，语言安装必须有实际定理及具体 site 证据。新 cursor 工作正是核上库和具体实例，没有借机重排接口。guarantee/requirement clause API 和第二 IR 仍由实际受阻案例驱动，完整 goal active。

## 递归 affine 的当前 kernel 接入

[本阶段](research-checkpoint-2026-10-06-materialized-affine.md)将已有 normal-returning affine guard 接入当前 `guard_host`／`guard_certificate`／`preservation_certificate`。语言库证明 actual check、primitive safety、全部完成检查 sound、原入口前提和 checked-entry 运输；domain 直接消费旧 guard execution／candidate-local，factory 核对实际语法与候选，原 table host 接到新的 Csem→Asm。没有调用旧 stateful region theorem 作为新局部 correctness，也没有修改 kernel。

六个新 `.v`、26 端点审计和提取通过。单／多指针的交换和 2×3 tiling 实际安装，错误 reindex／domain 和资源限制拒绝；十二配置共 5,118 次新 assembly 调用核对完整数组与公开出口。四组 actual emitted Clight 插桩另核对 1,366 调用的接受／fallback、共享存储的分离访问、重叠拒绝和 undefined 参数零读取；不是新的机器路径证据。前阶段及旧 deep 的 source/native 报告保持历史范围。

后继顺序据源码核对修正：先明确 stable-temp 深层实例与 loaded/dependent 实例能够共享的 source／前提／候选接口，再处理实际阻碍组合的 memory-bound 语义；多指针 scan 已在 stable-temp 路线接入，下一项是与 header/多观察稳定性的物理分离组合。一般 source 域形状、typed pointer-store body、P4 独立计时和同例已有工作／作者责任比较仍未完成。新实例的三方分工沿 narrative `7d94d81`，不以 code wrapping、端点数或测试次数主张新颖性或作者负担下降。完整 goal active。

## Narrative 226ba94：功能闭合后改进条件可用性

本轮重新 fetch 到 `origin/topdown/research-positioning = 226ba94`，已同步
[paper narrative](topdown/paper-narrative.md) 的新增实施顺序澄清。先闭合约定范围的
实际证明链，scan 可作为合法中间实现，不因昂贵而中断正在进行的接入；但自动条件推导、
guard 成本和 per-instance 人工负担是最终验收内容。无需先完成整个未来路线图才改进条件。

后继行动按这个顺序约束：

1. 完成当前 recursive affine＋loaded bound 的候选／host／compiler 接入及实际提取和 C 运行。
   已存在的私有缓存、源前缀、alias 和候选证明继续复用；新缺口优先落实到真实 frontend、
   typed pool、非空递归例、接受／loaded fallback 和完整上下文，不用抽象接口增加代替它们。
2. 在已声明 affine 范围内实现紧凑 entry 条件：验证 projection、range／footprint 包络，
   或核对不受信任充分条件提案。保留 scan／保守拒绝作为剩余路径。
   替换条件必须证明实际检查安全、接受 ⇒ 所需语义义务和入口运输；不要求与旧条件接受集相同，
   也不要求全局最小条件。只做数学投影不会自动证明机器算术或依赖读取安全。
3. 分别测量生成代码规模、运行检查成本、实际接受输入；cursor 循环化只能直接改善代码增长，
   不能据此宣称消除了逐点检查。候选 proof 和 host proof 在契约不变时应保持复用。
4. 选择 CGO 2017 的具体 C 例和 benchmark kernel，与当前支持范围逐项对照：源问题、假设、
   变换、检查成本、接受率及实例作者需手写的内容。记录源适配，将差距归到 frontend／源覆盖、
   条件算法、未完证明或具体语义差异；验证本身不构成功能差距的解释。

上述顺序吸收的是当前 narrative 的新澄清，不改写旧阶段的固定能力或报告；最终完整目标保持 active。

Expression-header 后继的具体切口见
[阶段记录](research-checkpoint-2026-10-06-expression-headers.md)和
[接口 walkthrough](expression-header-services.md)：真实 signed-expression capture、raw observation
与 computed cache 的对应、任意 structured body 的源前缀及缓存运输、递归 affine numeric
site 已证明。43 端点审计保持原基线；没有新完整 candidate rule／compiler/native 覆盖。
后续先用实际 recursive write receipts 和 byte separation 填入新 prefix 的 body-check／coverage，
然后运输 numeric facts、连接 entry relation 和 typed factory／host。不能把库要求的这些参数
当成已经自动生产的证据，也不能把 first capture 许可推广到未来 loaded child。完整 Figure 2
接入与 compact sufficient-condition／实际 guard 工作量验收继续执行，不以本阶段为目标完成。

## 当前范围的运行链闭合后的下一项

[本轮运行阶段](research-checkpoint-2026-10-06-loaded-affine-multi-native.md)已完成上述第 1 项的
实际 frontend／typed allocation／非空递归接受和回退验收。再次 fetch narrative 仍为 `226ba94`，
main 正文一致。不等待任意多观察 header 或 pointer-store 等全部扩展，再开始第 2–4 项。

下一切口是单 loaded root＋canonical affine children 的稳定性条件：复用现有 actual source receipt、
write footprint coverage、numeric envelope 和 byte separation 服务，提出紧凑的充分条件，实际安全
接受后才跳过逐点稳定性扫描；未成功时保留原 scan／回退。不能把原 base 的有效性从 shifted
source access 推出，也不能用待证稳定性许可预读。候选 validator、候选执行和语言 host 在契约
保持时继续复用；若新 P 与原 scan reference 有差异，显式提供连接证书，不直接套旧 guard flag。

同步选定 CGO 2017 Figure 2 的源例，记录 frontend 适配与人工元数据；对每项无支持结果归因。
成本先分别记录 guard code bytes、实际点／地址比较工作和接受范围，再做同版 CompCert 独立计时。
本次 41 个 fast 分派是固定测试集的路径证据，不计作 benchmark 接受率或性能收益。

后继 [简化与工作量验收](research-checkpoint-2026-10-06-loaded-affine-reduced.md)完成了重复 numeric
probe elimination；没有消除稳定性／跨指针 point-pair scan。当前 46 个源点的三数组例仍有
`46 + 3*46² = 6,394` 次 guard pointer comparisons，已在旧／新未修改机器程序上分别观察。
需要优先减少此实际工作，而不是继续只统计打印体缩小。

Figure 2 覆盖探针确认 main grammar 的两个具体缺口：先接真实 loaded expression root（含加一
和机器回绕），然后将 dependent loaded child 接到同一递归 package／观察保持链。
空外层的一 word shape、alias 改变后续次数及失败后的原 repeated-load fallback 必须保留。
前端自动提出元数据、checker 核对原 AST 与执行对应；不能手工缓存第二维后称原例已支持。
通用 projection、实际 guard／运行计时、full kernel 和 per-instance 人工工作继续未完成。

## Loaded＋offset 根接通后的验收

[本阶段](research-checkpoint-2026-10-06-loaded-offset-affine.md)已实际完成上一节 expression-header
计划中 recursive body receipts、write-vs-observation check、cached-source bridge、entry relation、
factory／host 与提取运行。原 43 端点服务报告仍保留其历史范围；新链有独立报告。
框架 kernel 未增加语言或 polyhedral 操作，检查器接受蕴含 semantic P；没有要求接受集合完备。

后续两个切口按 narrative `226ba94` 继续：

1. OLO Figure 2 的第二 loaded child。先定义层次源前缀／reached-header receipt，让叶子检查
   从真实源到达取得权限，在先前检查接受之后保持所有已捕获观察。内层缓存模型必须在对应
   子扫描接受后导出；不得把尚待证明的完整 cached child 执行用作 guard 安全的输入。
   对 Figure 2 的 child 首次读取，用已到达的外层非空条件许可 capture；空外层保持 shape[1]
   未读。明确前置 stores 是否存在：未来才发现的 observation 不能自动假定过去 stores 不修改它。
2. 已接通范围的紧凑条件。复用 body receipts、numeric envelope 和 byte-separation 服务，
   提出安全的充分条件，检查接受后跳过点枚举；失败保留既有 scan／源回退。
   必须报告实际比较工作和有用接受范围，随后做独立计时与选定 CGO kernel 对照。

新的 native 元数据适配只识别 `load + signed constant` 根，其他 expression 服务仍须相应实例。
本阶段不提供一般自动 assumption extraction／projection，也不以 708 次调用推断 benchmark
接受率。全功能目标继续 active，文档与 main 持续提交。

## 第二 loaded header：服务完成后的接入顺序

[本阶段](research-checkpoint-2026-10-06-nested-headers.md)已关闭 ordered capture、reached child
prefix、row-local joint preservation→outer advance 和 two-cache execution 的语言服务。
权限运输自动复用 structured-store 定律，numeric probe 由 captured words 许可。
`shape[1]+delta` 的 read 定律和 active-outer／empty-child fixture 已有；当前没有新 compiler。

下一项依赖顺序：

当前 first-leaf／parameter domains、实际 capture＋gated numeric 和逐点
DOMAIN／SOURCE_WORDS 已由 [producer 后继](nested-constant-numeric.md)生产，
inner／outer physical scan 和 canonical transport 也已有实际端点。
下面按完整安装的剩余连接理解，不把独立端点相加称作已支持原 C。

1. 原 reached child body → affine child／grandchild decode → 实际访问许可和 write coverage；
   实现所有 observations 的 actual private scan，证明 inner points／outer rows 的完整覆盖。
   point 接受才推进 child，当前 row 接受才推进下一 outer row。
2. 接受后把 two-cache 原 nested syntax 运输到 canonical affine model：child captured parameter
   与 model bound 用不同 private temps，额外 assignments 和第三层原 `<5` 保持 public exits。
   不手工缓存输入 C 或只改 proposer metadata 后称原 source 已接通。
3. 接旧 multi-alias／candidate checker，核对 typed pools、原 AST key、capture-entry／checked-entry
   relations、fallback 和实际 host；新 Csem→Asm、提取和完整 C 接受／回退作为该切口验收。

功能链闭合后继续 compact sufficient conditions、实际 comparisons／有用接受域和同版 CompCert
计时，沿 narrative `226ba94` 不等全部未来 headers／BODY 扩展才开始。kernel 不增新操作，
model／candidate／placement 责任继续由相应使用者／checker／host 提供。
