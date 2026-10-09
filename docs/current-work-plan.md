# 当前工作计划：评审吸收后的验收顺序

## 当前执行顺序与责任（以本节为准）

### 首要任务：PolCert／CGO 2017 对齐与完整程序正确性

2026-10-08 用户确认：功能、优化效果和 benchmark 至少对齐 PolCert 与
CGO 2017 Optimistic Loop Optimization，最终交付完整程序正确性。
并发相关可不支持；其余顺序能力不能仅凭当前 matcher、profile、witness 或
lowering 限制移出目标。支持范围是第一优先级，未支持项须有详尽尝试与具体诊断。

本次同步 `topdown/research-positioning@8ce9c8b` 的功能与完整程序验收要求。
本节决定后续顺序。下面的 signed/header-empty、scan 和其他阶段记录保留成果与
回归证据；其中历史“下一步”不覆盖本节。新增证明端点、调用数量或条件 AST
缩小，不代替源范围、变换、benchmark 效果及完整程序保证的完成。

本次已核对[固定版本 inventory](benchmark-alignment-inventory.json)：62 个 Loop
输入与 strict manifest／saved route reports 的案例集合一致，保留 19 项并发
saved-best 的顺序配置，并定位 CGO artifact 的十组 serial NPB 与 BT 原
`rhs.c`。七条缺少 execution metadata 的上游候选记录也保留。来源、复现
命令与逐配置证据字段见[原程序对齐计划](benchmark-alignment.md)。这是清单
核对。随后已完成[首轮原案例尝试](original-benchmark-first-attempt.md)：62 项、
三配置共 186 次初始编译，180 次 native state digest 匹配；`corcol3`／`pca`
的六次初始化拒绝在显式常量折叠适配后匹配原 GCC digest。Active 124 对
Clight 全部与 disabled 相同，无 pipeline 调用，所请求优化支持仍为零。
原 BT Class S 的三配置各 17 个单元完成编译并通过 NPB 自检，十行数值结果
与 GCC 一致；11 个 marked rhs loops 仍未优化。这是原程序 baseline 与
缺口定位，完整 tiers／顺序路线／效果和成本对齐尚未完成。

针对实际数据类型差距，新增 generic value instruction／IEEE double 实例
两模块 259 行、五端点独立审计，114 reachable sources／256 bindings，
最多五个继承 globals，无新增公理。复用既有任意 chunk 的独立 footprint
交换，保持表达式运算顺序。该旧检查点仅有 model→Clight expression 方向。

后继[原 matmul typed bridge](original-matmul-typed-bridge.md)保留同一原 C、
double 运算树、global nested arrays 和 I64 controls，导出并精确核对完整
Clight 中的 selected region／assignment。八模块1,181行、40端点／10closed、
159 reachable sources／6,990 bindings、最多12 inherited globals，无新增公理。
已完成 source assignment↔memory action↔真实 PolCert INSTR／单 body Loop，
八字节 lvalue／raw load-store 对应及 global registry 非 alias；I64/I32 addition、
初始化／increment／test 是点级证明。Typed affine／tiling validators、extractor、
prepared codegen 已实例化，尚无 external double scheduler／native 安装。
严格 assignment 实例拒绝 Vundef 成功结果；source execution 生产真实 read
许可，不提前假设未发生的 loads。显式 entry／layout 前提未自动由 factory
生产，完整 I64 nest、runtime guard、candidate lowering、公开出口与 Csem→Asm
仍缺，requested optimized cases 保持零。

后继[原 matmul 内层循环](original-matmul-inner-loop.md)已完成实际 exported
Clight initialized k loop↔真实 memory iterations↔typed PolCert 完整 inner
Loop，保留最终 memory／全部 temps，并精确设置公开 k 出口。C／K global
block 分离证明重复 K load 的稳定性，static＋loop invariant 自动建立每个
assignment entry。五模块700行、27端点／4closed、212 reachable sources／
7,082 bindings、最多6 inherited globals，无新增公理。入口 K load／范围
仍是逻辑前提；没有新的 guard／factory、完整三层 nest、scheduler 或
selected Csem→Asm。新增优化案例仍为零。此次重新 fetch 核对 narrative
最新仍为 `8ce9c8b`，main 文本一致；责任边界与原计算验收要求继续适用。

再后继[原 matmul 完整 nest](original-matmul-full-nest.md)已完成实际 selected
三层 initialized Clight↔physical iterations↔完整 typed PolCert Loop 的有限
双向证明。M=0 保留原 j/k，M>0、N=0 保留原 k，其余公开终值精确为
i=M、j=N、k=K；所有其他 temps 和最终 memory 精确保留。入口 N load
仅在 M>0 时要求，K load 仅在 M/N>0 时要求；C store 的 global block
分离生产嵌套 header stability。四模块567行、23端点／8closed、215 reachable
sources／7,148 bindings、最多6 inherited globals，无新增公理。这仍是
非负有界 I64 的有限 source/model bridge，entry loads／ranges 尚是逻辑
前提；没有新 safe guard／producer／candidate／progress／全程序安装。
Requested optimized cases 保持零。

实际 `DoubleAssignmentIRs.Loop` 与 source bridge 的 Loop 是不同 AST 实例，
直接传递的 type rejection 已重现并保留。新增99行 adapter／4端点／1closed，
221 reachable sources／7,186 bindings，最多6 inherited globals，无新增公理，
将同一实际 selected source 双向接到 pipeline 的具体 Loop constructors。
这关闭了类型／执行衔接，不等于 external scheduler／codegen 已被调用。

后继[原 double prepared pipeline](original-matmul-prepared-pipeline.md)现已实际
运行该原源 request 的 extractor／OpenScop／Pluto／importer／typed validator／
prepared codegen。Pluto 产生 i/j/k→i/k/j，实际检查接受并保留原 IEEE
instruction；identity 接受，reverse／malformed／external Err 三种拒绝
均无 alarm。新135行 adapter／四端点／一closed，224 reachable sources、
7,217 bindings，至多十二 inherited globals，无新增公理。Native 验收六项，
绑定8,295文件，包含首版 probe dense-ID 诊断导出错误的重现；五项实际
pipeline 验收通过。没有 C optimizer／guard／candidate Clight 安装，
新增 optimized cases 仍为零。Codegen theorem 是 wrapped Loop 的 backward
方向；固定 captured 参数下的对应还须由最终 candidate/factory 交付。

最新[原 matmul header license](original-matmul-header-license.md)从实际
selected source 的有限正常执行取得原入口 memory 上的 M load；仅在
signed M>0 时取得 N，仅在 signed M/N>0 时取得 K。没有先假设 header
loads、非负范围、layout、stability 或 body operands 可读。两个模块157行、
六端点、218 reachable sources／7,263 bindings，至多六 inherited globals，
无新增公理；三次成功、六次失败的证明尝试保留。这里只关闭 safe invocation
的 source receipt 子步骤；没有实际 capture／range guard、入口 transport、
progress 或安装，新优化案例仍为零。2026-10-09 在 `d1f533b` 基线上再次
fetch narrative，最新仍为 `8ce9c8b`，两份正文与 main 一致。

最新后继[原 matmul conditional capture](original-matmul-capture.md)已生成
实际 Clight M/N/K 检查：先在 I64 上检查 0≤header≤98，才精确转换为 I32
私有参数；拒绝停止后续读取，零维填充剩余 caches 而跳过未到达 headers。
实际完整 program 的四个 fresh names 通过资源检查。所有完成检查的 E0、
memory frame、已定义 flag 与接受 soundness 已证；原 source 从 checked
state 的 fallback entry／public exit transport 已证。接受接到同一 captured
M/N/K 下的 source pipeline Loop。三个模块562行、20端点／4closed、
243 reachable sources／7,332 bindings，至多六 inherited globals，无新增
公理；4成功／16失败证明尝试保留。18项 native capture probe 包括6接受、
10拒绝及2个域外预期失败，绑定7,625文件。Probe 使用实际提取的 AST 和
CompCert Cop／Mem，global lookup 与 AST interpreter 由 harness 提供，
不执行 source／candidate／fallback／Asm。Static/layout/bindings 和给定
finite normal source execution 仍是逻辑前提；generated candidate 的固定
参数桥、progress 和 selected 安装未完成，新 optimized cases 仍为零。

最新[固定参数 generated→source 后继](original-matmul-prepared-parameters.md)
已将实际 generator 在 captured M/N/K 下的有限执行接回同参数 source
Loop 和原 Clight，恢复精确 public exit；验证保持 named context，实际
cleanup 不更换参数。通用 `POLIRS` adapter 与 double 实例两模块409行，
10端点、249 reachable sources／7,387 bindings，至多14 inherited globals，
无新增公理；3成功／11失败证明尝试保留。Kernel 和冻结 optimizer 未改，
没有新 native／cost 结果。这关闭固定参数的 backward 对应，不能证明
候选一定能执行。Forward execution／progress、double Clight lowering、
static metadata producer 与 selected Csem→Asm 仍缺，新优化案例仍为零。

最新[实际 generated candidate progress](original-matmul-candidate-progress.md)
将原 signed32 的完整 source→point-list 证明参数化为 `POLIRS` 并实例化
到 double；不是重新发明该 forward 证明。Actual final generated body
重新提取，checked coordinate swaps／domain equivalence 对齐表示，再双向
检查依赖。Actual capture 和原 source 的有限正常执行现可推出候选 Loop
在同一 M/N/K 下有限执行，最终 memory 相同。七模块1,860行、12端点，
256 reachable sources／7,468 bindings，至多14 inherited globals，无新增
公理；8成功／14失败证明尝试保留。提取后的最终检查器实际接受 identity
及 Pluto i/k/j，拒绝 wrong-witness／reverse／malformed／external Err，
另复现并修正第一版静态输出 marker 的范围错误，共七项验收、8,652 bindings。
Native 不执行 source/candidate model 或完整 C/Asm，无成本／收益结果。
这是 conditional finite model progress；double Clight lowering、static
producer、source-total／divergence 和 selected 安装仍缺，新优化案例仍为零。

2026-10-09 再次完整核对 narrative 与 context-lifting：刷新全部 origin refs 后
最新仍为 `topdown/research-positioning@8ce9c8b`，两份正文与 main 一致，
没有发现更新的远端澄清。继续采用三层责任与 source/model 方向约束。
本次实际 lowering 暴露一个语言接口缺口：旧 operand view 仅保留 I32
evaluation，丢失 affine compiler 已证的 signed range；后继接口携带该证据，
支持精确 I32→I64 cast。该修补属于 language lowering 服务，不扩 kernel，
也不由源码用户提供范围证明。

最新后继[原 matmul 实际 double Clight lowering](original-matmul-double-lowering.md)
复用既有 nested lowering 和同一 Loop AST，提供任意 rank 的 global double
tensor backend，保持原 IEEE expression tree。实际 source 的有限正常执行，
经真实 capture 和 final pipeline/lowering receipts，现已接到实际
`capture; if flag then candidate; restore else source` 的有限 Clight 执行；
最终 memory 和所有公开 temps 与原执行对应，M=0／N=0 的 i/j/k 出口精确。
五模块713行、21端点／4 closed，269 reachable sources／7,557 bindings，
至多14 inherited globals，无新增公理；6成功／22拒绝或中断尝试保留。
Native 六项验收接受 identity 和 real Pluto i/k/j，实际输出 candidate／
guarded AST；其余错误 proposals 拒绝，绑定8,328文件。它不执行 Clight
statement 或完整 C/Asm，没有新收益／成本结果。这个 local forward 结果仍消费 static/layout/
bindings 与 finite normal source execution；没有自动 metadata producer、
source-total/divergence 或 selected Csem→Asm，也没有新已安装 benchmark。

2026-10-09 再次 fetch 核对 narrative，远端仍为 `8ce9c8b`，main 的两份
正文一致。后继[实际程序 bindings 与 scoped host](original-matmul-program-bindings.md)
已补上 universal contract 与 actual program facts 的量化差距：检查指定 globals
不被 params/vars 遮蔽，证明该 invariant 经 allocation、两种函数入口及全部
source steps（含 call/return/goto）保持。Scoped language-host successor 复用
原 private-region AST transform，交付 whole-Clight forward simulation；静态
no-shadow／private-pool 拒绝返回原程序。原 matmul 的八项真实 typed global
声明检查，自动生产五个 data bindings、三个 header bindings 和 layout span，
已把实际 guarded execution 交付给 scoped region contract。六模块970行，
15端点／4 closed、275 reachable sources／7,650 bindings，至多14 inherited
globals，无新增公理；6成功／15拒绝尝试保留。Kernel 不改，没有第二 IR；
language host contract 增加一个有完整 simulation 证明的 scoped 后继。
实际 source progress、matmul 安装与 selected Csem→Asm 仍缺，没有新 native
或成本结果，新已安装 benchmark 仍为零。

下一实现继续该原 matmul 的整条链：原 I64 nest 的适用 progress protocol，
source/site typing／placement 与 private resources，以及实际 guard／candidate／fallback
到 factory／selected Csem→Asm 的接入；随后扩 fusion、multi-stmt-stencil-seq、
BT。特殊 fixture、局部证明或仅实例化 checker 不替代完整链。Capture
已消费 reached-header license 并生产范围／精确转换和 source state transport。
固定参数 backward 对应已消费真实 scheduler／codegen receipt；最终
candidate forward／progress 证书继续作用于同一 captured M/N/K，不能用
wrapped semantics 中仅长度匹配的存在参数替代，并交付 host 安装。

后继已复用 `FramedNestedClightFor(I)(M)` 的结构证明，在 ranged operand
接口下交付 double nested lowering 的执行／private frame，不需要为 double
再造 host。Double backend 已把 I32 私有坐标精确转换为 I64 global-array
地址表达式并消费真实 reads/stores。Candidate model progress
已沿 final candidate extraction／双向 validation／固定参数 reconstruction
闭合，source Loop→point-list 的 forward producer 已通用化并实际复用；
Clight lowering 由后继独立证明，host progress 与安装仍缺。
已定位一个具体 installation 差距：旧 `projected_region_contract` 对任意
program/locals 量化，当前 local theorem 消费实际 global/no-shadow bindings。
静态 declaration checker 不直接填平该量化差距。下一项沿 allocation、
函数入口与 source steps 生产／运输适用环境不变量，检查如何在现有 host
simulation 中复用；或证明符合既有 universal contract 的对应。选择须由
实际 matmul 安装证明决定，不先加 generic context record，也不留用户
callback。详见[契约量化责任](framework-responsibilities.md#实际程序事实与-host-契约的量化差距)。
带 min/max/floordiv 的实际输出仍要覆盖，
不能因 final extractor 目前只接受 affine bounds 将这些路线移出目标。

此前响应 narrative 分支澄清，重新 fetch 并完整核对 `8ce9c8b` 的
`paper-narrative.md` 与 `context-lifting.md`；两份正文与 main 一致。
核对基线为 `2ed2c60`，没有更新的远端 narrative 提交。具体落实到
[原 matmul 入口事实的生产责任](framework-responsibilities.md#原-matmul-入口事实的生产责任)：
静态 metadata、读取的 safe invocation、guard 接受事实、原执行的 reached
receipts，以及候选入口／出口运输分别验收。已有 source/model iff 不代替
这些 producer，也不代替 source progress 或实际候选的进展证明。

下一项完整接入必须自动建立仍显式的 static／layout／binding 前提，消费
已完成 capture 的 conditional-load／range／source transport 证据，并消费实际
scheduler／codegen 结果；不为 C 用户增加语义 callback。对未到达的 N／K 和 body operands
保持条件式许可；声明、symbol binding、稳定性或范围事实单独都不能证明
一次 load 的 definedness。拒绝后的 fallback 要从实际 checked state 接回
原 source，不能忽略私有 capture 或已执行 prefix 对入口关系的影响。
这些是下一实现的责任约束，本次核对没有新增 proof、native 或成本结果。

两个 signed-child 草稿尚未成功编译／审计／安装，不算新支持；其后续投入
按下面的实际 case/configuration 阻塞或主要成本安排。特殊 fixture 保持回归。

1. 建立 [PolCert／CGO 2017 对照清单](polcert-integration-target.md)：
   PolCert 62 个 case 全部保留，逐例运行适用的顺序配置；保存最佳用了并行的
   case 重新评估顺序路线。按作者 artifact 固定 CGO 2017 程序、版本与输入，
   从原 NPB Serial C／BT compute_rhs 和 LLVM Test Suite 输入推进；未取得的
   SPEC／其他源和语言缺口明确列为待解决，不能默默删除。
2. 批量定位实际失败并补源／目标支持：保留原计算、数值类型、参数规模、多语句、
   多数组、loaded bounds 与实际上下文。记录 source/model、proposal、validator、
   codegen、candidate checker、Clight lowering、installation 各步结果及已尝试
   修复；原 benchmark 不可由简化整数 fixture 代替。优先定位 matmul、fusion、
   multi-stmt-stencil-seq 和原 BT compute_rhs，完整清单继续保留。
3. 按案例接入缺失顺序路线：实际 scheduling→tiling 组合，以及适用的 ISS、
   intra-tile、diamond／two-level tiling、unroll／jam。复用现有 PolCert
   验证与代码生成，补 statement、witness、坐标和实际目标结构限制；
   不等所有 guard 边界补完才接真实 pipeline。Vector annotation／机器 SIMD
   另行调查，不能直接随并发排除，也不能用注解成功代替实际 lowering。
4. 每项扩展同时完成现有 host 上的安装：factory／site 自动建立调用、source/model、
   guard/candidate、scope、placement、progress、typing 与资源前提；保留
   memory／public exits／continuation，重复改写证据针对当前中间程序。
   复用 finite／open Clight host 和 CompCert，成功返回目标时交付实际
   Csem→Asm backward simulation。不能留用户语义 callback 或未证明的
   context lifting 假设；不先增加通用 context algebra、第二 IR 或公理。
5. 同源验收实际效果与成本：原源、PolCert／Polly 的适用顺序目标、候选本身和 GuardCert
   完整调用使用对应计算、输入与可比后端，明确报告 Polly／CompCert 后端配置差异。
   计入 guard、candidate／fallback、
   出口恢复，保存编译成本、代码尺寸、实际变换、接受／拒绝和负结果。
   Identity、全 fallback 或 tiny 回归不算所要求优化已支持；仅相对旧 guard
   节省也不算 benchmark 收益；效果差距有诊断仍属未完成，继续推进。
   最新联合 compiler 再做干净源码树全链复现。

已有 runtime empty 组合、signed-empty、RMW observation、canonical／dedup／linear
服务保持回归。Mixed negative/active、broader scalar/chunk、recursive loaded 与条件降本，按上述 benchmark 的实际支持缺口或主要成本安排；并未取消。
无具体阻塞的 kernel／库分类／host 抽象重构不优先于范围接入。
当前定位是“可复用框架与若干完整编译路径已有，目标优化器支持范围与效果仍待完成”，
不是“主体已完成、只剩论文评估”。进度逐程序／配置报告已实现、已尝试仍缺什么、
尚未尝试，以及完整证明与效果状态，不估工期或总完成百分比。

### Narrative 的持续设计约束

以下保留 2026-10-08 的旧导入记录：当时核对 narrative
`topdown/research-positioning@c4b1395`，在 guard library 澄清之上又同步
source/model proof directions 与 premise provenance。以下根据
[paper narrative](topdown/paper-narrative.md) 和
[context lifting](topdown/context-lifting.md) 固定验收责任，不声称读到了
更晚的提交。

具体证明链按 original Clight → source Loop → transformed Loop → lowered
Clight/public exits 逐段列出；loaded source 另列 capture/stable-source 桥。
Decode 是从 concrete execution 恢复 model execution，不是 parser，也不
自动是双向 equivalence。分开追踪静态 syntax/shape/resources、runtime
guard/capture/transport facts，以及作为证明起点的 original source execution；
不要求每个前提都有一个 emitted test，不在运行时先执行源程序来许可 guard。
最终 installed theorem 必须生产适用前提，不能留给源码用户。

该次旧导入时 remote 为 `c4b1395`，main 的 narrative 文本与该版本一致。[实际 loaded-affine 证明对照](snapshot-polyhedral-native-pipeline.md#sourcemodel-证明方向与前提来源)
已把 capture、cached-source、Clight-to-Loop、candidate lowering、public
restore 和全局安装分别关联到具体定理。后续 first-empty-child 等扩展沿用
同一前提来源审查；这项说明不新增实现里程碑或要求重命名定理。

Kernel 的验收止于局部证书组合；`C_host` 是实际 guarded choice 的语言
执行规律，整程序 installation 是另一项语言证明。新条件服务应分别交付
domain 的 `C_derive`、language 的安全求值/入口出口运输、factory 的 region
guarantee 与 site evidence，再消费既有 installation/backend。不能仅因
已有泛型 program theorem 就把 contextual closure 算作框架自动完成。

当前工作检验这条分工：canonical alias 域定理、实际 Clight scanner、
typed/fresh allocation、原 source 许可到 scanner 输入的自动生产及
factory/compiler/native 接入已完成；完整成本独立测量。最难位置是部分定义
的入口：child/header/RHS 只有原源执行许可时才可观察，新的私有坐标与 flag
必须运输到候选入口，同时完整公开出口满足 continuation 的要求。

验收条件服务的复用时，记录哪些原 candidate/host 定理沿用、哪些新增证明
由 domain、language 或 site producer 负责，以及源码用户是否只需标注 C
和策略选项。安全、充分性、接受域、代码尺寸、动态工作及完整调用成本分别
给证据；局部 helper 编译不代替 compiler 接入。General affine/OLO 功能
仍属于完整目标。

Guarantee/requirement 与 clause factoring 保持设计问题。先在至少两个
实际 host 上证明 transport/entailment 的复用，再决定接口；finite completion
与 open step simulation 分别验收。每次 rewrite 的 region/site 证据必须
针对当前中间程序产生，有限序列的组合不能修复过期的 placement 或 freshness。

### 已完成阶段：empty 与既有候选的 runtime 组合已安装

该阶段于 2026-10-08 fetch 与核对远端 heads，当时 narrative 为 `c4b1395`，
main 文本一致。其 proof directions／premise provenance 约束应用于
[runtime alternative 后继](affine-empty-runtime-installation.md)：旧 candidate
的 Clight→Loop→candidate→Clight 链原样消费，新的 empty 分支使用 actual
empty-source／exit 证书；不能把 polyhedral validation 当作 empty 或原源
对应的证明。

新 language service 消费旧 target 的 opaque small-step projected contract。
接受时产生 fast branch／原 suffix 的公开出口；拒绝时生产 source replay
entry 与 checked entry 的公开关系，复用旧证书。真实只读 prefix 可精确
重放，capture／Boolean 的私有写入另作运输。Factory 自动检查 prefix
outputs／pointer inputs、typed/fresh resources 与 signed 条件编码；静态
wrapper refusal 保留旧 target。源码用户无新增 semantic callback。

六模块529行、15端点／2closed／2,028bindings／旧42globals，无新增公理，
提取编译器与 selected Csem→Asm 接通。旧empty矩阵2,280／2,280全部path
保持。六配置RMW2,448／2,448完整输出/context通过；正常408输入保留126
candidate接受，新增58empty接受，fallback146→88，一份original fallback。
真实prefix／条件M-NULL安全与scheduler/resource refusal均实跑。

同binary另有word400／400、recursive-affine480／480、private-loaded270／270、
zero-width672／672。Zero-width保留60candidate并新增56empty，fallback164→108；
regression引用上述已经完成的normal RMW816／816，不重复计为新batch。

拒绝路径可能重复prefix／capture，完整调用成本未测；这不是收益结论。
该阶段提出的下一顺序是mixed negative/active child及general recursive loaded affine、
broader scalar/chunk、dynamic layout／完整OLO-BT与完整成本。后继条件服务
继续先明确调用许可与入口出口关系，再接原candidate／host；完整goal保持active。

### 此前：signed header 条件与可复用 empty client 已安装

2026-10-08，[signed header 后继](affine-empty-signed-installation.md)扩大
header profile 到有符号区间，复用既有 `PolCertAffineClight` analyzer／range
primitive／lowering。源码核对修正此前诊断：generic `typed_view`／`env_within`
与 encoder 已支持signed，限制是旧client传入的非负profile；不能将其原证书
直接用于负值，但也不需要新造算术语义。

新的empty condition client消费同一readonly condition／facts契约，source／
capture／公开出口／private Boolean／安装证明与具体编码解耦。Factory自动
生产调用／resource前提；源码用户API、kernel、host、candidate checker保持。
五模块391行、12新端点／2,000bindings／旧42globals，无新增公理。

同源同配置2,280 Asm／2,280 Clight完整输出通过；add矩阵接受33→87，
新增54个均为负M，无旧接受丢失，包含NULL body、undefined word和header overlap。
subtract矩阵保持87。极大cap／scheduler refusal另有190／190，确认signed
静态编码拒绝后实际安装旧condition并保留接受。单一original fallback保持。

同binary旧五族另有2,638 Asm／2,638 Clight，历史path／configuration记录相同，
RMW每种正常配置126接受保持。

这是bounded signed profile，不声称任意int32参数；generic dynamic wide guard
可作为后继producer，但还没有接到这个client。后续继续已有candidate的
runtime empty组合、mixed negative/active child、general recursive loaded
仿射域／broader scalar/chunk／完整OLO-BT和完整成本。完整goal保持active。

### 此前：empty rewrite 的共享 fallback 已安装

2026-10-08，[共享 fallback 后继](affine-empty-plan-installation.md)复用已证
header-only 条件、original source/capture 与精确出口，将 outer-empty／
all-empty alternative 降低为私有 Boolean 与一次原源 fallback。新的 Clight
language service 证明短路 choice factoring、接受分支重查 outer 的实际执行
及私有 flag 的公开投影；factory 自动检查第三个 signed32 private 和 resources。
共用 kernel／host／candidate checker 不变，selected Csem→Asm 已接。

四模块263行、9新端点／1,988bindings／旧42globals，无新增公理。
同源同配置2,280 Asm／2,280 Clight完整输出通过，全部逐输入path记录与
冻结旧compiler相同；实际triangle原源loop从32份到1份，每个测试函数
恰有一份。同binary旧五族共2,638 Asm／2,638 Clight回归通过，RMW正常126个快路径
保持；其历史path／configuration记录相同。条件本身仍是finite tree和Boolean assignments，不声称通用
condition size bound、最小条件或完整成本收益。

该历史阶段完成compact fallback；signed header参数已由上述后继接入。此前顺序为：
将empty选择接入已有candidate的运行时路径，继续general recursive
loaded affine／broader scalar/chunk／完整OLO-BT与完整成本。静态registry
优先不等于已经完成运行时组合。完整goal保持active。

### 此前：header-only empty rewrite 的安装与后继验收

2026-10-08，[实际全空 rewrite](affine-empty-installation.md)已接 original
loaded Clight、private capture、header-only affine endpoint 条件、精确公开出口、
factory 和 selected Csem→Asm。Outer `N<=0` 跳过 M，positive-root 下所有 child
不活动时跳过 body-only words／array／alias 检查；负的 K 出口恢复为 `j=0`。
这是实际 conditional rewrite，不需要 polyhedral C_opt；旧候选 route 保持。

十模块1,000行、29端点／5closed／2,076bindings／至多旧42globals，无新增
公理。两种width源、六配置共2,280 Asm／2,280 Clight完整输出与continuation
通过，包含NULL body pointers、未初始化body-only变量、header/data overlap。
同binary word400、recursive-affine480、private-loaded270、zero-width672、
RMW816各自Asm/Clight回归通过。既有builder静态优先，旧候选正常接受保持。

必须保留两个具体缺口：现有header参数profile只许可非负参数；`i-M`可接受
负K，但positive-root `i+M`中的负M仍安全回退。新直接tree还展开了32处triangle原源fallback，
没有compact或profitability结论。旧factory已经返回target的site没有新增运行时
empty分支，静态registry组合不能代替该运行时组合。

此前验收顺序（前两项已有上述bounded后继）：

1. 用既有private-Boolean/check-plan定律降低新条件，证明原guard与紧凑AST的
   对应、flag freshness及source/candidate入口出口运输，移除重复fallback。
2. 为header-only signed参数建立安全编码服务，自动从原源头部许可生产调用
   前提；不能只放宽Boolean而沿用非负typed-view／lowering证书。以负M的
   `i+M`、NULL body与undefined scalar为实际accept/refuse验收。
3. 组合empty与既有实际polyhedral候选的运行时选择，保留原接受域与candidate
   C_opt；source/site producer继续生产placement／effects／context证据，
   不增加源码用户completion或equivalence callback。
4. 继续general recursive loaded affine／dynamic layout／完整OLO-BT、
   broader scalar/chunk条件与完整成本。基础设施阶段不标记完整goal完成。

### Verified guard library 的组织约束

[服务目录与契约对照](verified-guard-library.md)按 arithmetic/representation、
range/footprint、memory separation、value/observation preservation、control/
conditional observation 五类整理现有实现。类别按建立的事实划分，可以重叠；
它们不构成所有 rewrite 的固定阶段。目录列出已有接口、定理、调用前提与
未实现边界，不新增 kernel 或通用 predicate compiler。

当前 header-snapshot 工作沿同一契约格式推进：每项明确 inputs、requires、
actual execution、accepted/refused facts、reads/private writes/public/memory/
events frame，以及从原 source/site 生产调用前提的责任。特别区分 temp
ports 与 memory-read receipts、原源许可与未来稳定、机器字替换与 mathematical
no-wrap。后继 [原 loaded setup 证明](affine-header-snapshots.md)已编译并独立
审计七模块／29 端点；原条件捕获、preparation 输入、current-observation row
decoder 与 reached-write permissions 已有。它还没有新 factory/native 接入。

Ordered dependent checks、短路、conditional capture 与 alternative sufficient
conditions 分别核对 actual exit 的事实运输。Separation 和 value-preserving
writes 可以建立同一 header observation relation，但两者都不许可 speculative
read，header stability 也不代替 candidate 的全部依赖条件。Pure alternatives
可复用 readonly branching；private-service alternative 的 refused-exit
transport 尚未有统一 combinator。

先用当前 actual `i<*N; K=i+*M` 桥和既有 zero/separation 路径检验共用契约，
有实际 client 复用再抽取 language adapter；继续复用 candidate/factory/
installation。现有载体是 Clight templates/scans，callable C routine 需独立
call/state/link/compiler 连接。库分类和未来 call/inlining 选择不延后当前主
任务，也不替代 compact-condition derivation、接受域与完整成本验收。

2026-10-08：已完成本阶段 [loop-linear canonical 服务](linear-canonical-alias-service.md)。
它把 canonical scanner 的 source/setup→实际安全执行和精确 Boolean 单独放入
`ClightCanonicalSourceInputs.v`，不要求 alias 模板 eligibility；domain client
证明同一循环系数、不同常数／稳定参数系数仍保留访问差值。Normalization
只判断算法适用性，实际地址继续使用原完整模板。新服务复用该 language
适配器及 common factory／loaded contract／selected compiler；kernel、host
和候选 checker 保持。Rocq 16 端点／9 closed／1,420 绑定／旧 42 globals，
无新增公理；新 compiler 的正常 1,000／1,000、移位 180／180、不同循环系数
旧扫描 180／180 full-output/context 检查通过。移位完整成本 810 batches 全输出通过，2×3／8×8 accepted 相对原服务
减少 38.43%／91.49%，仍为 source 的 7.52／17.01 倍。所有九个 median
高于 source，cap／child-empty 回归 5.88%／8.51%；不把 test 数的下降或
相对节省写作盈利。论文同步记录 proof、reuse、native 和独立成本。

后续优先级：

2026-10-08：[private-loaded affine actual pipeline](selected-private-loaded-affine-pipeline.md)
已把旧二维 root snapshot／temp-affine-child 库接到真实 Pluto／prepared codegen。
普通 request adapter 复用 signed proposer，原 private-loaded factory 核对实际
模型、candidate、validator／encoder ranges 和 width 前提。两新增接线模块
63 行、4 端点、1,810 绑定、至多旧 42 globals、无新增公理；全局端点直接
实例化共用 selected compiler。三个 stale legacy objects 在独立 namespace
重建，未覆盖原成功对象。Kernel／host／candidate checker 均不变。

六配置 810 Asm／810 Clight 全输出与公开 continuation 通过，两正常模式各
安装两处、16 accepted／74 runtime refused；同 binary 原 word 400／400、
recursive affine 480／480（含真实三层和同函数两 marked regions）通过。
旧 envelope guard 要求相同 pointer root；different-allocation 输入保守回退，
first-empty-child 仍回退。两次错误 harness expectation 保留，原 assembly
输出均匹配，第二次还完成 135 Clight 全输出匹配。没有新成本或收益结果。

**此前任务，现由后继接入**：接入 broader alias／value-preserving header 条件，复用同一
snapshot transport、candidate 和安装链，并继续 general recursive loaded
affine、scalar/chunk、完整 OLO 与成本验收。先核对既有 zero-RMW observation
服务能否由当前 actual body checker 自动生产调用前提；新充分条件须建立同一
N/M observation relation，不能用 header stability 代替 candidate data-dependence
条件，也不能把 source-user callbacks 当作 producer。服务接入后须测量同源／
同binary的完整接受和拒绝调用成本。全空 body-input bypass和 negative-width
clipped public exit仍需具体语言／domain证明。

对照实际定义后，zero-RMW不能直接填入当前稳定性字段：
`mint32_words_preserved`只保持已有defined Mint32 words；
`affine_snapshot_point_preservation`却量化任意point memory，并要求原始
`location_load` equality。下一适配应把transport实际使用的
`header_observations_match`不变量和word-valued receipts显式纳入domain的
observation保证，先证明separation路径到该保证，再证明checked RMW／zero
条件到同一保证。两者都由factory自动生产前提，保持data-dependence checker
与公开出口要求；不得把word观察保持扩写为完整memory equality。
这是具体domain／language桥的证明责任，在此诊断阶段尚无新接口或接受证据，也不要求
修改kernel。首个实际client须再核对body grammar、alpha的原源许可和compact
plan／registry连接，不能以另一个孤立condition helper算作接入。

2026-10-08：[actual-row observation 接入](affine-observation-installation.md)
已完成上述实际 client。Separation 与 checked zero-RMW 分别推出同一
`header_observations_match` row 保证；whole-loop transport 消费当前观察
不变量，而不把 Mint32 word preservation 当作完整 memory equality。
Factory 自动选择 context scalar、检查实际 row body；numeric/first-reached
preparation 接受后才读取 alpha。`alpha=0` 走值保持证明，其余走原 compact
N/M scan；data alias、actual candidate recheck、公开出口和原 source fallback
仍沿用。新 builder 先于 zero-width registry，Csem→Asm 直接复用 selected host。

十一模块／1,115行／29端点／2closed／1,992bindings／旧42globals，无新增
公理；23次编译尝试全保留，11成功／12拒绝。六配置2,448／2,448 Asm/Clight
全输出及continuation通过；正常各126 fast／146 fallback／136 unmarked。
两个frozen compiler在同一408输入、同一RMW源上的接受122→126，无丢失，
四项gain都是alpha0的N/M写入重叠。新binary word400／400、recursive affine
480／480、private-loaded270／270、zero-width672／672全部通过。

该actual服务的完整成本已独立验收：336 batches×65,536调用每批完整输出
匹配；旧、新、disabled-source均用同一RMW源。Separated-alpha0的tile／schedule
median比旧guard减少15.48%／8.26%，新增overlap接受比旧fallback更慢。
全部16个新median仍高于source（1.004–3.761倍），没有收益结论。首轮336
输出通过后汇总path lookup失败，source／outputs保留并绑定于修正报告。

**当前下一验收**：推进全空 body-input bypass、
negative-width clipped出口及general recursive loaded联合source/model；
broader scalar/chunk条件与完整OLO逐例对照继续在完整goal中。条件算法和
成本不因服务分类完成而降为可选，源码用户仍不承担语义callback。

[Zero-width installation](zero-width-installation.md)已连接 actual wider-domain
mapped/tiling checker、checked factory、compact plan与 selected Csem→Asm。
新 builder 先于既有 registry；两个原 loaded-affine C 函数的首行空／后续
非空路径实际接受。十一模块／33端点／1,934bindings／旧42globals，无新增
公理。六配置2,016／2,016 Asm/Clight全输出和continuation通过；同binary
word400／400、recursive affine480／480、private-loaded270／270通过。
正常模式各60 accepted／164 runtime fallback／112 unmarked；actual first-empty／
later-nonempty子集30 accepted／12 refused，另6个N/M同址的M0输入实际outer
count为0并回退；N1/M0的16个body-empty输入也安全回退。在原264个相同输入上，
接受从30增至40且无丢失。普通 pipeline request 本来就是真实未加 first-positive
限制的 source Loop；保留 proposer，改用更宽 assumed model 重新验证返回的
实际候选。完整成本与更一般 source 仍未交付，完整目标继续。

以下为模型／稳定性子阶段的历史范围，其安装缺口已由该后继接上。
[Zero-width stability](zero-width-stability.md)已从 ordered first-reached／range
checks 生产弱 ready，连接 source row decoder、实际 reached-point permissions、
N/M 短路扫描和 accepted cached completion，并对给定原执行保持精确 memory／
temporary exits。十模块／35端点／7closed／1,486bindings／至多旧六项 globals，
无新增公理；实际 scan AST 与旧版相同。Factory 仍须生产原 capture/header
调用前提，在新 assumed model 下检查实际 source/candidate/code，再消费这些
producer 与 model/restore 桥。Registry 必须选到新路径并保持旧 positive
输入的接受；该阶段没有 compiler/native 与完整成本结论。

[Zero-width 模型桥](zero-width-model-bridges.md)已证明 nonnegative width
域的 source decode、mapped/tiling candidate checker soundness、实际候选
lowering/public restore，以及 actual first-reached guard 到完整 typed view
和新模型假设的 producer；五模块／17端点／7closed／1,400bindings／至多旧
12globals，无新增公理。Kernel、host 和底层 validators 保持。
新 wrappers 必须验证实际候选在更宽 assumed model 下的正确性；不能推广
旧证书。具体更宽域候选的 checker acceptance 尚未实跑，尚无新 factory、
compiler、native或成本结论。原 snapshot native bindings已重新核对。

[Later-body 许可与条件服务](leading-empty-body-licensing.md)已生产实际原源的
empty-prefix／later-leaf、入口 body words，以及常数个 affine endpoint
条件的安全编码与 readonly 接受证书；五模块／24 端点／9 closed／1,432
绑定／至多旧六项 globals，无新增公理。旧 native bindings 重新核对。
新服务未接 factory/compiler，native first-empty-child 仍回退。
后继已新增 zero-width assumed model/checker 及 source/model/candidate 桥，
保留冻结的旧模型和报告。后继已用 full view/header/nonnegative width/ranges
取代新证明路径中的旧 first-positive ready 前提，生产 current-observation row
decoder、actual reached-point permissions、N/M stability和cached completion。
下一步 factory 调用新 checker，绑定实际 candidate/code并接compact plan／selected
compiler/native。新 source decoder 仍消费实际 cached source completion，
其 loaded-source producer不能留给源码用户。负 width 的旧 j-exit 公式也需
另证，receipt 不代替该证明；全空模型不许可 body-only reads。
随后扩展 alias sufficient conditions、recursive loaded domains、scalar/chunk
和 OLO具体源及完整成本。
[Native pipeline](snapshot-polyhedral-native-pipeline.md)已提取固定旧 registry
加新 snapshot factory 的 compiler；原 `i<*N; K=i+*M` 和 `K=2*i+*M` C
完成实际 Pluto/codegen／完整 checker／selected安装／Csem→Asm链。直接
tree compiler在 candidate accepted后被 SIGKILL；后继复用现有私有Boolean
lowering，15端点／1,850 bindings／旧42 globals／无新增公理，保留原condition
和candidate证明，编译时不展开完整tree。六配置1,584／1,584 Asm/Clight全
输出通过，正常两模式各两处、30 accepted／146 runtime refused；同 binary
word400／400、recursive affine480／480、旧private-loaded270／270通过。
空outer且M不可读的路径安全；first-empty-child仍保守回退。六次candidate
attempts不等于两处installation；两次harness诊断错误与原compiler失败保留。
本阶段没有完整调用成本或收益测量，joint recursive loaded语义未合并。

[Checked installation 阶段](affine-snapshot-installation.md)已把静态 AST/
grammar/shape/freshness 生产、typed conditional capture、具体原出口到 cached
source、alias/range/candidate 连接与 mapped／tiling／schedule factory接通；
新 builder 注册到共用 selected host，新 Csem→Asm specialization沿用原
installation/backend theorem。九模块／37 端点／17 closed／1,644 绑定／
至多旧 42 globals／无新增公理。该阶段的 proof connection已由后继native
pipeline消费；完整成本尚待验收。
原条件 capture、原源到 arithmetic guard 输入、concrete row decoder 和
prefix write receipts 已由 [新阶段](affine-header-snapshots.md)生产，29 端点／
1,332 绑定／至多旧六项 globals／无新增公理。该阶段不新增 Csem→Asm 或
native 结果，不把 cached completion 留作未经生产的调用前提。后继
[N/M stability scan](affine-snapshot-stability-scan.md)已实现 concrete row
conditions、接受才推进的 prefix scan 与 whole-loop cached transport；
actual scan 接受自动生产 complete cached source；后继 checked factory与
compiler proof已连接，native已由后继pipeline验收。
Root 空时不能观察 `*M`；header 已执行但 child／leaf 为空
时，header load 与后续 RHS 的许可须分开。Domain 给 no-wrap／reached-point／
footprint／source-model 充分性，language 给 actual guard 安全与 public/memory
frame 和 exit transport；factory 给 guarantee，site／selected host 给 placement／
progress 和全局安装。后继已固定实际旧 registry／ordinary Pluto adapter 的
compiler configuration；不能在提取端注入任意未证明的 builder。已有二维
联合源链不能推广成 recursive loaded-word 域
已经合并。随后推进 first-empty-child、broader alias sufficient conditions、
scalar／chunk 和 OLO 具体源与完整成本。Finite/open clauses 及第二 IR 仍以
实际复用需求为依据。完整 goal 保持 active。

以下记录保留各阶段当时的后续任务；本段决定当前执行顺序。

2026-10-08：[actual rank-three codegen](compact-affine-codegen.md)已完成当前
affine 源族的实际三层生成／安装。普通 oracle 压缩 parallel rows，既有 LCF
forward contract 与 `ExactCs.fromCs` 对全部原约束的 reverse check 共同许可
exact canonicalization；其他 abstract-domain 调用保留各自方向。原 signed
proposer、最终 source/candidate checker、guard、builder、语言 host 和
Csem→Asm 端点沿用，没有新 Rocq 模块、公理或 kernel 接口。

真实二／三层 triangular 和 descending C 在 tile／自动 schedule 两模式各
安装五处；八次候选尝试含额外 nested fragments，不等于八处安装。六配置
1,440 Asm／1,440 Clight 全数组／公开控制／continuation 通过，同 binary
loaded-word 回归 400／400。三个源族分别有 -1／-2 起点的实际接受。单次
同源同 binary codegen 对照：开启压缩 9.588 秒完成，关闭在 90 秒 deadline
仍未完成首个三层 codegen；不是统计编译时间／CPU 收益测量。两次 harness
assertion 历史保留，其 assembly 输出均匹配，并非观测到误编译。

下一主任务是联合 loaded 参数与非矩形源许可。用 `i < *N`、`K=i+*M` 的
实际 C 推动新桥：domain 证明 source-licensed snapshot 稳定、reached-point
的 no-wrap／control／address 事实及源／模型对应；language 服务证明条件
读取的安全、memory／public frame 与 actual guard-exit transport；factory
交付原 region guarantee，selected host 继续检查 placement／progress。
不能以两个已证 builder 的静态分派当作这个联合证明。当前 affine guard
要求 `affine_first_path_flag`，first child 为空而后继非空仍保守回退；该
接受域缺口与联合源桥一起处理。随后接 scalar／chunk、OLO 具体源与完整
guard／candidate 成本。完整 goal 保持。

现有 `ClightAffinePrivateLoadedCandidates.v`／planned-loaded 库已经证明较窄
二维 loaded root 加 temp-affine child、private snapshot、footprint／stability
和公开运输。下一轮先核对其实际 request／candidate 接口能否消费真实
Pluto/codegen，复用这些定律；不把这部分写作尚未证明。未预加载源中的
conditional `*M`、recursive rank 与 word/general-domain 结合仍是新义务，
不能把显式 unconditional preload 的源适配当作原源的许可证明。

2026-10-08：[signed affine bound proposals](signed-affine-bound-proposals.md)
已修复旧 zero lower envelope 漏掉负 tile 坐标的具体提案缺口。普通 interval
算法处理 signed floor／min／max 并保留原 membership guard；原 final checker
仍针对 actual source／完整 request 验证。没有新 `C_derive`／`C_guard`
定理、Rocq 模块或 kernel／host 变化。Floor -2 的真实二层 Pluto／prepared
codegen 在 start -1／-2 下实际进入候选；六配置通过 1,152 Asm／1,152
Clight 全输出／公开出口／continuation，同 binary 的 loaded-word 回归
400／400。新矩阵增加一个输入，不作为旧矩阵的配对性能比较。

下一优先项转为三层 actual prepared codegen 的独立定位。源码可见
Fourier-Motzkin projection 后的 canonicalization，而当前 ordinary oracle
`add` 保留全部约束；尚不能把 timeout 归因结论写作已测事实。若提出
constraint compaction，复用 `ExactCs.fromCs` 的原约束反向检查与 LCF
forward guarantee，不能只证 forward consequences 就删除原约束。
之后继续一般 nonrect reached-point 许可与 loaded-word 模型结合、scalar／
chunk 和 OLO 源；当前 passing tier 仍明确不标注三层函数。完整 goal 保持。

2026-10-08：[同一 selected 入口的 affine 接入](selected-affine-pipeline.md)
已落实 narrative 的真实 pipeline 要求到旧 recursive affine source。
Clight library 用已证明的 builder record 组合原 word 与 affine factories；
一次 table／selected installation／Csem→Asm 证明服务两者，kernel 不变。
普通 proposer 把原 checked request 和小范围提案送给实际 Pluto／prepared
codegen，最终 checker 仍核对原源与完整 bounds。非负起点的二层非矩形
域、同一函数两个标注 region、静态 refusal／实际 fallback 和 continuation
通过 1,008 Asm／1,008 Clight；同一 binary 的原 loaded-word 回归通过
400／400。四模块 208 行、9 端点、1,594 绑定、旧 42 globals、无新增公理。

这一交付只共享语言安装，不等同／合并两套 domain。当前优先切口是
signed affine bound enclosure（旧 zero lower proposal 会让负坐标 profile
被 final checker 拒绝）和三层 profiled prepared codegen 的长运行；必须取得
实际候选与新 runtime 证据。之后组合一般 nonrect reached-point许可与
loaded-word 观察、scalar/chunk 和 OLO 具体源。Rectangle box receipts 不能
许可源域外读取。当前二层 profile/cap 与已有三层手写候选测试均不代替
一般 affine 流水线闭合；没有新成本／盈利性测量。

1. 以本阶段的完整成本／诊断作为后续条件工作的基线。原严格-map服务退到
   四模板 pair scan，新服务用三模板 canonical scan；比较不能单独归因到
   normalization，也不重跑已冻结的历史实验。
2. 恢复主源覆盖工作：更一般参数化／非矩形 affine source、scalar／chunk、
   自动 source/model 与实际候选对应；用 OLO 的具体源和前提逐项验收。现有
   `GUARDCERT_TENSOR_CAP` 可配置，8 是已测默认 profile，不是数学定理或
   framework 的固定上限。更大 profile 和实际 locality 工作负载需要新证据。
3. 在已闭合的源族继续改进紧凑充分条件／首次拒绝停止／header 条件，分别
   证明安全、充分性和 actual-exit transport，沿用候选与语言安装。保证／
   需求及 clause factoring 仍由实际 host 复用驱动，第二 IR 不作前置任务。

以下去重及 service 阶段保留当时的交付和计划范围。

2026-10-08：[去重 alias scan 服务](deduplicated-alias-scan-service.md)已通过
实际接口复用验收。严格 root／完整 affine map 去重，domain 证明成员保持
和 point／canonical Boolean 规范精确；language adapter 从原 source／setup
生产剩余读取许可，沿用原 allocator 和 scanner execution，返回公开 frame
及 accepted entry fact。第三个 builder 直接接原 common factory、loaded
contract 和 selected compiler；专门 Csem→Asm 端点是一行实例化，无新增
installation proof body、kernel／host 改动或源码 semantic callback。

三模块共 308 行；11 端点／7 closed／1,414 可达绑定／旧 42-global baseline／
零新增公理。提取的三个注册策略 compiler 默认 `dedup`；正常矩阵通过
1,000 Asm／1,000 Clight，非 uniform 旧 scan 回退通过 180／180，完整输出／
公开出口／实际路径保持。新成本准备通过 243 重复 Asm／81 Clight 检查；
row 总 guard tests 361→181、4,741→2,041，kernel bytes 1,349→1,325。
这些是工作／尺寸证据。新完整成本 2,430 batches 全输出匹配，2×3／8×8
接受为 source 的 5.37–5.62／11.96–14.54 倍；相对本次 canonical 配对减少
12.64%–24.15%／15.37%–27.81%，接受路径仍没有盈利。26/27 medians 高于
source；仅 column start refusal 约低 0.12%，不执行候选。回退的小幅回归
保持，不能用诊断计数下降声称整体盈利或归因到单一组件。

下一项以完整成本和分项诊断确定 remaining header／alias／candidate 工作，再实现
常量 tests 消除、首次拒绝停止或 source-licensed header 充分条件。保持
安全、充分性、运输、实际 compiler、接受域与完整成本的分开验收，不复制
higher-level factory／host。严格模板去重不扩大一般 affine source 能力，
cap 8、非矩形 domains、scalar／chunk 扩展和完整 OLO 联合验收继续在 goal。
三模块的行数不是作者时间；第二 IR／clause algebra 仍不是主实例前置任务。

以下 service 阶段及其 narrative 规划保留当时交付范围。

2026-10-08：[Source-licensed scan services](source-licensed-scan-services.md)
已落实上述复用问题：Clight record 只要求真实安全执行、memory／public／
ports frame 和 accepted→entry fact，不强制新旧 Boolean equality。原 pair
与 canonical builders 自动构造这个已证明的边界；同一 factory、loaded
region 和 selected compiler 消费它们，分别证明完整 factory computations
等于冻结前驱。19 端点／1,414 绑定／旧 42-global baseline／零新增公理。
新 compiler 在两策略下各通过 1,000 Asm／1,000 Clight full-output/context
checks。普通 source/candidate proposals 与已证明 service implementations
明确区分；源码用户仍只给 C 和选项。

这一阶段证明同 host 上的两算法复用，不声称另一个 host 或 clause algebra
已经复用，也不减少 guard 工作／增加一般域。下一项直接在此接口注册第三
条件服务，消除重复／常量 access tests，再接同一 compiler 做真实接受／
回退／成本验收。之后以同样链检验 early refusal／header 条件；不能为继续
复制接线模块而延后条件成本。General affine／scalar／完整 OLO 联合能力
仍在 active goal。

### 本次 narrative 澄清对下一项验收的约束

2026-10-08，main `f41344e`。重新读取远端 `12419c1` 的完整 narrative 和
context-lifting，并对照 `ClightSourceLicensedScan.v`、
`ClightMultiTensorScanService.v` 及共用 factory／compiler。两份 narrative
文档与 main 相同；本次没有新的优化、证明或测量结果。

第三个条件服务用来检验接口能否减少真实证明工作。服务作者提供检查 AST、
结果 temp、checked allocation，以及从原 source 执行／setup／ports agreement
到安全检查执行、frame 和 accepted entry fact 的证明。它满足
`source_licensed_scan` 后，沿用 `check_scan_service_full_execution`、
原 loaded-region contract 和 `compile_selected_word_nested_store_service_regions_correct`。
新服务不应再复制这三层证明；记录新增的 domain／language 证明、代码生成
与 driver 注册工作，和实际复用的端点。代码行数可记录，不能代替作者时间
或已经减少验证负担的结论。

这项服务的具体验收顺序是：

1. Domain 证明 access-template 去重保持所需 alias 条件；language 证明
   删除检查后每次剩余读取仍由原 source 许可，机器执行、memory／公开
   frame 和私有结果满足接口。去重可以追求精确 Boolean，但通用接口只
   要求接受充分性；将来更强的充分条件可以拒绝更多输入。
2. 自动 builder 生产 typed/fresh resources 和证书，接同一 factory、
   loaded host 与实际 C→Asm compiler。支持族的源码用户仍只给标注 C
   和策略；候选 proposer 提交普通数据，不提交 semantic callback。
3. 验收实际安装、接受／回退／空域／continuation，并保留 intermediate
   model、scheduler／codegen 和 validator 记录。完成执行作为 scan 定理
   的前提，不代表该接口自动证明 source progress 或任意 context 安装。
4. 分别报告接受域、检查工作、代码尺寸和完整调用成本。既有 canonical
   测量的所有输入仍慢于 source；新增服务的节省及收益必须重新取得证据。
   新旧条件精确对应、检查数下降、编译器正确性均不能单独证明可用性。

OLO 2017 仍约束自动条件处理与使用体验；一般 affine 功能及其差距继续
记录。Context clause factoring 以现有 host 的实际复用为依据；第二种 IR
是可选证据，不能成为主 CompCert 实例的隐含前置任务。

以下保留前阶段当时范围。

2026-10-08：[Canonical alias 完整 compiler](canonical-alias-compiler.md)接通
checked 四向量 allocator、原 setup/source 到 ranges/receipts 的自动生产、
新实际 scan exit 到原 candidate/fallback/public restore 和 selected host。
严格 uniform maps／cap 静态匹配用新 scan，否则安装旧 scan；两分支 flag
精确等于原 Boolean。Outer empty/header source refusal 保持。七新模块／
23 端点／10 closed／最多 42 旧 globals／1,410 绑定，零新增公理，新提取
Csem→Asm compiler 已运行。

相同矩阵通过 1,000 Asm／1,000 Clight calls；不同 affine maps 补充通过
180／180，真实候选安装而生成旧 scan。完整 memory/public outputs/paths
保持，不扩大一般 affine frontend。二维占用九 scan slots，原为五；有限
pool 的静态 installation 接受域不声称保持。原 candidate checker、host
和 kernel 不变；源码用户仍只给 marked C／策略。

完整 source／memo／canonical 配对成本与实际 Clight 工作诊断记录于
[canonical 完整调用测量](canonical-alias-complete-cost.md)：2,430 batches
全部完整输出匹配；2×3 接受成本为 source 的 6.34–7.24 倍，8×8 为
14.29–20.17 倍。相对旧 memo 分别降低 38.01%–45.37% 与 91.15%–93.01%，
但没有输入的 median 优于 source，部分 bypass 观测 regression 保留。
Row guard tests 720→361、71,234→4,741；function bytes 1,344→1,349。
不能据此声称一般 OLO 盈利性。

后续优先从该结果确定紧凑服务：重复／常量 access tests 的安全消除、首次拒绝停止，以及
header stability 的充分 entry condition；分别证明 exactness／sufficiency、
原源读取许可和 actual-exit/public transport，再接实际 compiler 验收。
同时把 scan resources、实际执行／结果／公开 frame 的语言接口抽成可复用
服务，用原 pair scan 和 canonical scan 两实例检验 factory/candidate 接线
能否保持同一份证明；不以复制后继模块当作作者负担已降低的证据。
一般参数化／非矩形 affine domains、更多 scalar/chunk、完整 OLO 联合功能
与作者负担仍在 active goal。新服务不能通过 hidden same-block、语义
callback 或额外私有 pool 假定转嫁责任；kernel API 仅按真实复用证据更改。

以下保留前阶段当时范围。

2026-10-08：[Canonical alias Clight scanner](canonical-alias-scanner.md)完成四个
语言模块，实际运行 difference bounds、canonical coordinates、pointer tests
和 rectangle flag accumulation；memory 不变且 source/read ports/live frame。
14 端点、4 closed、最多 6 项旧 globals、692 可达绑定，无新增公理。低层
端点消费 source-box receipts 与 checked fresh resources；自动 factory 尚未
接线，不能据此声称新的 native compiler 或性能结果。

**下一项直接接 typed allocator、eligible factory 和实际 compiler。**
从原 header/numeric setup 生产 count range/receipts，自动选择额外私有
positions/limits，实际出口接原 candidate/region guarantee/selected host；
不匹配沿用旧 scan。随后相同 native/context/full-output 矩阵与新完整成本。
当前 compiler 仍使用 quadratic pair scan，完整 goal 未完成。

以下保留前阶段当时范围。

2026-10-08：[Canonical alias 域服务](canonical-alias-condition.md)已证明
任意维矩形坐标差覆盖、canonical points 在原域、严格相同 affine templates
的实际 CompCert modular pointer/alias Boolean 对应，以及接受推出原 source
footprint restricted nonalias。20 端点、17 闭合、最多四项旧 globals、670
可达绑定，无新增公理。Source-model execution 自动许可 canonical accesses；
kernel/candidate/host 保持。2×3/8×8 的数学位置空间为 15/225，相对原 pair
空间 36/4,096；不是新的 runtime 工作或成本结果。

**下一项直接实现 actual Clight scanner 和 factory/compiler 接入。**
从现有 header 接受/numeric setup 取得 source-model 许可，证明差值 bounds、
canonical coordinate machine arithmetic、pointer equality 和 flag 的完整执行；
自动 fresh typed cursors，运输 actual exit/public state，复用原 candidate 和
selected host。Eligibility 不匹配保留原 scan，runtime refusal 保留 source。
随后相同 native/context/full-output 矩阵与新完整配对成本。当前 compiler
仍使用原 quadratic pair scan，数学 spec 没有替代端到端验收。

以下保留前阶段当时范围。

2026-10-08：[双 loaded 完整调用成本](word-nested-store-complete-cost.md)已完成。
同一源码 source/shared/memo 三 modes、三 profiles、九 cases、三十随机配对轮，
共 2,430 batches；全部 warmup/final memory/public outputs 匹配。未插桩
CompCert assembly 的完整调用含 header reset、全部 guard、候选/回退和出口。
普通 2×3 新版本约为 source 的 11.45–11.61 倍，8×8 为 186.58–226.66 倍；
旧/新有改善也有回退。静态尺寸和 setup 次数降低没有满足可用性验收。
8×8 row guard tests 71,252→71,234，其中 setup 33→15；主要 scan 保持。
这是已闭合源族的测量，不新增 compiler/语义证明或一般 affine 覆盖。

**下一项优先实现紧凑 alias 充分条件及安全 actual Clight encoder。**
先以 checked 相同 affine access maps 的 canonical point-difference coverage
减少接受路径比较；不匹配时沿用原 scan，同时考察首次拒绝停止。Domain
证明 coverage/地址对应/accepted→restricted nonalias；语言服务从原 source
许可读取，证明算术、循环和 flag 的实际执行及 public transport；factory
接原 candidate/region guarantee 和语言 host。当前只是设计，须完整证明、
提取和 native/full-call 验收后才宣称实现。不能依赖跨 CompCert block 的
undefined pointer ordering，不能隐藏 source-user same-block 假设。

Kernel/host API 继续按 narrative 的责任边界复用；general affine domains、
source/scalars、完整 OLO 联合功能及作者负担仍在 active goal。成本优先
不取消功能目标，也不以更多小 fixture 延后已有族的实际成本验收。

以下保留前阶段当时范围。

2026-10-08：[Narrative/kernel/host 对照](narrative-kernel-host-review-2026-10-08.md)
已按代码回答 context-lifting 的八个问题；fetch 后可见仍为 `12419c1`，
两正文与 main 相同。Kernel 止于局部 guarded 证书组合，whole-program
installation 是语言 host 的实际证明。Finite/open 可以共享边界 relation，
不能合并 progress；guarantee/requirement clause 化继续作为待验证设计。

[Readonly probe 后继](word-nested-store-probe-memo.md)已接真实 compiler：
精确 Boolean 结果、test 次数不增加、原 candidate/host 证明复用；五模块
18 端点、1 闭合、1,380 绑定，无新增公理。相同 1,000 Asm/1,000 Clight
完整输出与观察路径保持。额外 2,000 次配对 Clight 诊断的 setup 计数
合计 6,564→3,228，普通配置 972→468；普通 2×3 function 1,442→1,344 bytes。
未前移读取或添加 mutable cache；header/alias scan 复杂度和 cap 8 保持。

**下一项直接测完整调用的配对成本，并继续证明紧凑充分 entry conditions。**
计入 capture、header/alias scan、candidate/fallback 和公开出口；setup 节省
不能代替全调用 CPU 收益。以 OLO 功能/接受域/源码用户与实例作者负担验收，
不以更多 source grammar 延后已闭合族的成本。一般 affine domain/source/scalar
仍在 active goal；kernel API 或 contract algebra 仅在实际复用证据支持时更改。

以下保留前阶段当时范围。

2026-10-08：[双 loaded shared setup/尺寸](word-nested-store-shared-setup.md)复用
既有 Clight check-plan 服务，把 numeric/layout/box/profile 的拒绝叶子合并
到一次分派；自动在候选检查后选择 checked fresh typed flag。原条件、header/
alias scan、candidate checker 和 host 均保持，新 Csem→Asm 入口及提取通过。
11 端点／1 闭合／1,376 绑定，核对 parent 1,374，零新增公理。相同十组
1,000 Asm／1,000 独立 Clight calls 的完整 outputs 和观察路径保持。

配对 `nm -S`/Clight 计数：普通 2×3 单 region 从 2,750 降至 1,442 bytes，
root-source copies 36→4；参数 stride 40→4。未标注/unsupported/driver/main
尺寸保持。这是代码增长证据，不是 timing/guard 工作或源程序收益。

**下一项复用/实现重复 probe 与静态事实 residualization，接实际 compiler，
验收条件安全/接受域/guard 工作，再做完整配对成本。**不得以更多 source
grammar 延后本源族的 OLO 可用性验收。Header/alias scan 的复杂度和 cap 8
尚未改善。通用 pointer-order interval 替换有真实 Clight 定义性缺口：不同
allocation 的 ordering 可为 `None`；现有 envelope 需要共同基址。新的
紧凑服务须明确语言可编码的 evidence，不隐藏 caller same-block 假定。
一般参数化 affine source/scalar、OLO 完整能力和作者负担仍在 active goal；
kernel/host contract 与 guarantee/requirement clauses 的开放边界保持。

以下保留前阶段当时范围。

2026-10-08：[双 loaded 实际 C/Pluto/codegen/native](word-nested-store-native-pipeline.md)
已关闭前一阶段的实际驱动缺口：proved administrative-skip adapter 运输原
frontend source guarantee；自动普通 metadata、真实两轴模型、Pluto 与
per-statement prepared codegen 接入提取的 selected compiler。完整 checker
重检 distributed/completed/rebound Loop，不添加虚拟 axis 或语义 callback。
新 adapter/整程序审计 7 端点、2 闭合、1,374 可达绑定，核对冻结 parent 的
1,380 绑定，保持旧 42-global baseline、无新增公理或 kernel/host contract。

十组配置的 1,000 次未插桩 Asm 和独立 1,000 次 Clight 分支检查通过，完整
memory/public exits 与逐次读取实际 header 的源模型一致。成功配置每组安装
四 sites；普通/单位 tile、行/列、参数 stride、真实 schedule、重复标注、
continuation、header/cached 两层回退、空域及失败 scheduler 均覆盖。
报告 `build/multi-word-nested-native/native-v1/report.json`；本族支持的是
两轴 loaded 矩形源族，不将调用数当作一般 affine domain 支持。

**下一项直接验收已闭合源族的紧凑条件及 OLO 完整功能/可用性，不能以更多
源 grammar 扩展无限延后。**当前 cap 8、header 逐点 scan、跨数组 point-pair
scan 和多份 fallback 的成本/代码尺寸仍有明确风险。域库构造紧凑充分 entry
condition；语言证明安全求值及 actual-exit/public transport；复用现有
candidate/region guarantee/host，再分别测接受域、guard 工作、完整成本/
收益和作者负担。一般参数化 affine source 与 scalar 扩展仍在 active goal。

再次 fetch 所有远端 heads：narrative 可见仍为 `12419c1`，两正文与 main
相同。其 kernel 局部截止、language 的 progress/boundary/installation、
domain 的充分前提/模型对应，以及 guarantee/requirement clauses 开放讨论
继续约束设计；不为文档叙述新增 kernel API。本阶段新增功能运行证据，
没有新增成本或性能收益结论，完整 goal 未完成。

以下保留前阶段当时范围。

2026-10-08：[双 loaded store-list 候选与整程序证明](word-nested-store-affine-compiler.md)
已把实际 header-guard 出口的 cached execution 接完整多数组 affine/tiling
candidate checker，证明两层 fallback/public transport，生产 projected region
guarantee，再消费既有 expression-progress selected host 接 Csem→Asm。空域
分支绕开整个内层候选准备；真实执行 fixture 证明任意候选不可达且 child／
数组仍未定义。三模块／14 端点／6 闭合／1,380 绑定，保持旧 42-global baseline，
无新增公理、kernel 或 host contract。二维两数组有意依赖的普通模型检查通过。

**下一项直接接本族实际 C 驱动和真实 optimizer，不能再以接口样例替代。**
从 marked C 的真实规范化 AST 自动生成普通 loaded/model metadata，接两轴
Pluto／prepared codegen 和已证明 compiler 的提取，验收 native 接受、两层
refusal、缺失 child 的空域、多个标注及 continuation。C wrapper/reset/header
适配、真实调度维度与分配资源是当前具体连接风险；不引入虚拟第三轴来
掩盖两轴缺口。既有 temp-bound native 的证据不自动覆盖新族。

本次 fetch 后 narrative 仍为 `12419c1`，两正文与 main 相同。其三方责任继续
约束工作：kernel 止于局部证书组合；language host 证明 boundary/progress/
placement/installation；domain/factory 生产前提推导、局部对应和 guarantee，
支持族源码用户只给 marked C／策略，不补 semantic callback。Guarantee／
requirement clause 化保持开放。紧凑条件／OLO 完整功能、代码尺寸、检查工作、
接受域、成本和作者负担仍需独立验收，不等待所有 source 扩展；一般参数化
affine source／scalar 等仍在 active goal。本阶段没有新 native 或成本证据。

以下保留前阶段当时范围。

2026-10-08：[双 loaded store-list 数据入口](word-nested-store-data-factory.md)
已自动生产七个私有 int32 slots、source/body syntax、scope、rename 与原 loaded
source progress，接完整 header rewrite 的实际执行定理和既有递归 cached
multi-tensor model checker。三模块／34 端点独立审计：29 闭合、最多 6 项旧
globals、1,280 可达绑定，零新增公理；自动 package 的真实接受、child alias
fallback、空域执行与静态 refusal 均检查。Kernel/host contract 保持。

**下一项接同族真实 candidate 分派和 region guarantee。**静态 model 构造不
读取 runtime child cache；空域接受必须绕开无条件参数准备，活跃接受从
actual guard exit 的 cached execution 接完整候选服务。内层拒绝执行 cached
source，外层拒绝执行原 loaded AST，分别证明 final memory/public exit。
之后消费已有 expression-progress selected host、marked C、真实 Pluto／
prepared codegen，完成本族 C→Asm/native/context。原 source progress 已由
factory 生产；placement、pool declarations 和 site/context requirement 仍由
语言 host 的安装证据负责，局部 execution 定理不替代这些证据。

当前 data description/model proposer 属于 domain 库接入方；本族自动 C
metadata frontend 未接，不把普通数据 API 称为已经完成的源码使用体验。
此次 fetched narrative/all heads 可见仍为 `12419c1`，两正文与 main 相同，
未发现较新已推送澄清；三方责任和 guarantee/requirement 开放边界保持。
已闭合 slice 的 compact conditions/OLO 代码尺寸、运行工作、接受域、完整
成本及可用性验收继续独立推进，不等待所有 source grammar 扩展。
一般 affine source/scalar 扩展仍在完整目标；本阶段没有新 native 或成本。

以下保留前阶段当时范围。

2026-10-08：[完整双 loaded guard 与 cached/original 分派](word-store-nested-guard.md)
已从原 source 执行生产 conditional capture、ready 和 gates；outer 空域跳过
child capture/cache 与全部数组检查。活跃接受接联合 scan，再从 actual guard
exit 执行 cached nest；拒绝运输原 AST，两条路径保持 final memory/public exit。
真实内存接受、child-only alias 拒绝和 child/cache/数组 temps 未定义的空域都
有完整 guard/rewrite 推导。两模块／20 端点审计通过，3 闭合、最多 6 项旧
globals、1,142 项可达绑定，无新增公理；kernel/host contract 保持。

**下一项接同族 source/model/candidate 与 data factory。**接受时须区分空域
与活跃状态：空域可能没有 child cache，不能进入无条件读取它的 setup。
活跃路径从实际 guard exit 运输 cache/dimension/scalar bindings，接现有
递归 source factory、完整模型/候选 checker 和公开恢复；由 factory 生产
original loaded-source progress、typed resources、scope、region guarantee 和
placement，再消费 marked C／真实 Pluto／prepared codegen／selected host，
取得本族 C→Asm/native/context 验收。Cached AST 的 progress 不替代原源证据。
这仍是局部完整 rewrite，不是新 installed loaded polyhedral compiler。一般
affine domains、scalar/source 扩展和已闭合 slice 的 compact condition/OLO
完整成本、接受域与可用性继续在 active goal。本轮没有新增 native 或成本。

以下保留前阶段当时范围。

2026-10-08：[双 loaded axis 的联合 scan 与实际 cached 出口](word-store-nested-scan.md)
已将任意 checked store list 接到原 nested source 的逐点许可。当前点接受保持
两份 header，当前行全接受才推进外层；实际双 cursor loop 在内层首次拒绝时
停止外层。全接受从原源导出 cached nest，再运输到 actual scan exit。入口
锚定 prefix 服务消除对无关 ready 状态的 header-law 要求，kernel 不改。
真实 allocation 例证明两份 header 同 word 时接受，以及只修改 child header
时拒绝；原源只执行一个点，不假设后续点有许可。
六模块／50 端点审计通过，9 闭合、最多 6 项旧 globals、1,138 项可达绑定，
无新增公理；前一 1,114 项绑定的成功 report 保持。

**下一项先接原 nest 的 conditional capture/gates 与完整 cached/original
dispatch：outer 空域必须跳过未定义 child header。**当前双-axis theorem
要求两份 ready、非负 count 与 row-zero，不将它当作完整 guard producer。
随后接同族 source/model/candidate、公开恢复和 data factory，自动生产资源、
scope、progress、region guarantee 与 site placement，消费既有 marked C／
真实 Pluto／prepared codegen／selected host，取得本族 C→Asm 与 native 验收。
框架负责局部证书组合，语言负责安全／frame／progress／安装，domain 负责
充分前提与模型／候选对应；guarantee/requirement clauses 仍为开放设计。

本次 fetch narrative 可见仍为 `12419c1`；读完正文及 context-lifting，与 main
无差异。其边界直接约束上述最难连接，不为叙述新增 kernel API。已闭合
temp-bound slice 的紧凑充分条件／接受域／代码尺寸／运行工作／完整成本和
OLO 功能及可用性比较保留为独立验收项，不要求先完成所有 source 扩展。
该局部阶段未新增 loaded compiler、native 或成本证据，完整 active goal 不变。

以下保留前阶段当时范围。

2026-10-08：[完整 store-sequence guard／cached 分派](word-store-sequence-scan.md)
已从原 loaded loop 的正常执行生产捕获／ready，先检查 row-zero／非负 gate，
再执行静态生成的短路 cursor loop；首个拒绝停止，不使用后续原源许可。
全接受产出 cached source，并运输到实际 guard exit；完整 cached/original
分派证明保留 final memory 与公开 temps。真实内存 fixtures 覆盖后续 RHS
使用前一 store 初始化、第二 store/header 别名回退、空域未定义数组指针。
四模块／35 端点／7 闭合／最多 6 项既有 globals／1,114 绑定，无新增公理。
**下一项组合完整 original loaded nest 的多 header／条件读取与 cached/model
对应，再消费同族多数组 candidate、公开恢复、data factory／selected host、
真实 polyhedral pipeline 和 C→Asm／native 验收。**一条 axis 的实际 guard
不作为完整多维 loaded compiler 的完成；本次没有新增 native 或成本结果。
Kernel／host contract 未改；静态 scope／rename／typed resources 尚须由同族
factory 自动生产。再次 fetch narrative 仍为 `12419c1`，正文与 main 一致。
已闭合 temp-bound slice 的 compact-condition／接受域／代码尺寸／运行工作／
完整成本和 OLO 比较继续在 active goal，不因单轴服务完成而延后或删减。

以下保留前阶段当时范围。

2026-10-08：[实际 store 序列／loaded prefix](word-store-sequence-prefix.md)
从任意 assignment list 的真实中间内存取得每条 store 的检查许可；只回运
权限，不前移后续 RHS 值。实际 AST checker 生产 word index、flatten、
normal／quiet／temp 写集。静态 readonly 地址树接受时保持捕获 header，接
单一 loaded axis 的原源 prefix advance；cached-source 执行不是许可前提。
四模块／44 端点审计通过，16 闭合、最多 6 项旧 globals、1,100 项绑定，
无新增公理；真实内存 fixture 构造 source/check 的局部执行，未新增 native。
**下一项组合完整原 loaded nest 的多 header／条件读取与全接受 cached/model
对应，运输到实际 scan exit，再接同族 data factory、checked candidate／
公开恢复、真实 Pluto/codegen 和 selected Csem→Asm／native 验收。**局部
服务不是新完整 loaded compiler；scope／rename／资源的自动生产仍须接同族
factory，不向源码用户转嫁 semantic callback。

[Narrative 对照](narrative-store-sequence-review-2026-10-08.md)再次 fetch 并核对
远端全部 branch heads：可见 narrative 仍是 `12419c1`，两正文与 main 一致，
未观察到较新澄清提交。Kernel 止于局部证书；language 提供安全、frame、
progress、boundary／placement／安装；domain 提供充分前提、原源许可与
模型／候选对应。Region guarantee 与 context requirement 保持区分，不因
本次澄清新增 kernel API 或 contract algebra。已闭合 temp-bound slice 的
compact condition／code size／runtime work／接受域／完整成本与 OLO 比较
继续在 goal 中，不等待所有 source grammar 扩展。以下保留前阶段范围。

2026-10-08：[多数组 actual C 接入](multi-array-affine-native-pipeline.md)已完成
本族 marked frontend、自动 source metadata、真实 Pluto／per-statement prepared
codegen、完整候选检查和已证明的 selected compiler 接线。八配置 768 次未插桩
Asm／768 次独立 Clight 验收通过，核对完整数组与公开出口；五支持 sites 实际
安装，未标注／unsupported 保留，两层 runtime fallback、重复 region、周围
memory effects 和 scheduler failure 均检查。自动调度未使用 `--identity`。
复用前一 Csem→Asm 定理及 42-global 基线，kernel／host contract 未变；真实
安装与通用整程序定理现在分别有证据，不再将此接入记为 pending。

再次 fetch narrative／context：远端仍是 `12419c1`，与 main 一致。三方责任和
内核止于局部正确性的边界保持。**下一项推进同族 loaded 两-store 原源的逐条
header 保持、下一读取许可及实际 guard-exit 连接，随后接同一数据 factory／
selected host。**本 temp-bound slice 已闭合，不为所有来源扩展延后条件改进：
独立的研究任务是可证明的紧凑充分条件、code size／运行工作／接受域、完整
成本及 OLO selected-source 比较；该语言下的安全观察与出口运输必须单独证明。
Coordinate-only scalar receipt 和一般 affine domains 仍待实现。本次没有新增
成本、收益或作者工作量结果，完整 active goal 保持。

以下为前一 compiler／提取阶段的历史边界；其中同族实际 C 接入已由上述后继完成。

2026-10-08：[泛化 actual exit 与 selected compiler](multi-array-affine-versioned-compiler.md)
将同一 source package／typed allocation 的完整 setup、affine scan、checked
candidate、public restore 和原 AST fallback 接成实际执行，并由 data factory
生产既有 projected region guarantee。Selected language host 复用 occurrence
选择与同一 source progress classifier，新的 Csem→Asm 定理已编译／独立审计；
kernel 与 host contract 保持。**下一项直接接此同族的 marked C frontend、
自动 metadata、真实 scheduler/codegen 与提取编译器，验收完整 C／Asm 的
接受、两层 fallback、未标注 exclusion、多 site 和公开 continuation。**
整程序正确性定理与具体安装／运行成功分别记录；不等待所有 loaded-source／
一般域扩展才执行这项接入。

提取后 full factory 的九项检查通过：identity／三种真实 codegen masks 接受，
四种 source/candidate/resource 错误拒绝；selected statement host 实际安装
两个标注 site 并保留相同的未标注 site。该测试运行 checker／语句生成及
statement traversal，没有执行 emitted Clight 或新 C／Asm，不能抵扣上一项。

本次按用户提醒再次 fetch／读取 narrative 和 context-lifting：远端最新仍为
`12419c1`，与 main 两正文一致，无新差异。Framework 只负责局部证书组合，
language 提供 check/frame/progress/placement/install，domain 提供充分前提、
来源许可／coverage 与模型／候选对应；新数据接口不要求源码使用者补语义
callback。当前最难的剩余语义位置仍是两次 store 的 loaded 原源逐步保持与
未来读取许可；scan 平方成本、紧凑条件和 OLO 功能／可用性验收继续属于 goal。

以下为上一泛化 scan 阶段记录，其 actual-exit／candidate／projected／compiler
证明缺口已由上述后继关闭；同族实际 C 驱动和 native/cost 尚待验收。

2026-10-08：[实际 affine access scan](multi-array-affine-access-scan.md)将同一
source package／typed allocator 接到任意访问数和 identifiers 的静态 Clight
双矩形。原源 trace 许可实际 affine write/read 地址，接受生产 actual
footprint separation；flag 自初始化，memory 与全部 source／caller temps
保持。Kernel／host 定义保持，新族未安装。
**下一项直接运输同一 source/model／受限 locator 到实际 scan exit，接
checked candidate／restore／原 AST fallback，生产 projected guarantee 并
消费 selected host／Csem→Asm。**Coordinate-only scalar 的 source 可观察性
gate 仍保守拒绝，需要后继 receipt/checker；loaded 两 store 的 header/prefix、
一般 affine domains、紧凑条件与 OLO 完整可用性继续属于 active goal。
本轮 fetch 并读完 narrative／context-lifting：远端仍为 `12419c1`，两正文
与 main 一致。真实 polyhedral 集成、三方责任及最难的状态连接继续约束
实现顺序，局部服务不算新族整程序完成。

以下为 data-factory 阶段记录；generic scan 的许可／coverage 已由上述
后继推进，actual-exit／candidate／placement／完整安装仍待完成。

2026-10-08：[数据 source factory 与 typed scan 资源](multi-array-data-factory.md)
已从任意 identifiers／assignment list 的实际 temp-bound AST 生产 source
package、静态 freshness／shape、checked box 与原源 progress。完整 setup 接受
导出实际源 Loop 模型，无入口 numeric／layout／box 或 NonAlias callback。
Allocator 为两个 rank 维 cursor＋flag 选择 fresh int32 slots，生成 scan AST
并证明源＋caller frame；九个闭合计算 witness 覆盖换名接受、metadata／pool
拒绝和显式 progress 限制。初版 single-body proposer 的两-statement 误识别
已由独立核对 reset／child 的后继 factory 修复，原拒绝与日志保留。
**下一项将该相同 package／allocation 接泛化 runtime alias scan 的源许可、
动态 coverage 与接受充分性，运输到 actual exit，接既有 candidate／restore，
生产 projected guarantee 并消费 selected host 安装。**当前 typed allocation 和
source progress 服务已生产；前一 full guarded statement 的固定名实例尚未
泛化，不能把这些服务合称新族 compiler／native 完成。Loaded 两 store 的
header／prefix、一般 affine domains 和 OLO 可用性继续在 active goal。

以下为上一任意 caller 边界阶段记录；typed resources／source progress 的生产
已由上述后继推进，泛化 guard／candidate／placement／整程序接线仍待完成。

2026-10-08：[任意 caller 边界](multi-array-public-boundary.md)已从实际 pair-scan
写集和静态 disjoint 检查导出任意 live frame，移除固定 source ports 子集要求；
完整 setup／alias 两分支接同一 checked candidate／原 AST，并生产现有
`PrivateRegion.projected_region_contract`。Kernel 保持。重新 fetch narrative
仍为 `12419c1`，两份正文与 main 一致；三方责任、真实 polyhedral pipeline 和
OLO 功能／可用性验收继续约束 active goal。
**下一项为该族的 data factory 生产 source recognition、可实例化的名称和
fresh typed guard slots、scope／progress／selected placement，再消费已有 host
安装 canonical 同族并接 Csem→Asm。**任意 live frame 与 local small-step
contract 不替代资源分配或 source progress；不向源码使用者索要 semantic
callback。两 store 的 loaded 原源 prefix／header 保持随后接相同路径；新族
compiler／native／cost 及完整 OLO 尚未完成。

以下为完整条件阶段记录；其中任意 live frame 与 projected guarantee 缺口已由
上述后继闭合，typed allocation／progress／placement／安装仍待完成。

2026-10-08：[canonical 两数组完整条件](multi-array-complete-guard.md)已复用
range／volume／box 编码器，从实际多 assignment 源许可观察，接受时生产全部
numeric／layout／box／profile 前提。新 full versioned statement 对 setup 与
alias 拒绝均执行原 AST，接受执行 checked candidate 并恢复 iterator；整段局部
定理已移除动态 setup／NonAlias 入口假设。四模块／26 端点独立审计通过
（8 闭合、最多 14 项旧 globals），129 项绑定及 parent closure 保持旧
42-global 基线，零新增公理。
**下一项直接为 factory 补任意 program-live temps 的 frame 和 fresh typed
private pool、checked source/site 与 progress 证据，再接 canonical 同族安装；
同时推进两 store 的 loaded 原源 prefix／header 保持，组合相同 loaded/Horner
路径后再完成其 selected Csem→Asm 和 native/context 验收。**固定示例的 live
子集定理不覆盖 host 的全部 `program_temps`；不能把这项 frame 或 source/model
缺口变成源码用户的 callback。当前 producer 返回 local statement，尚非新
整程序 compiler；alias scan 仍平方成本，完整 OLO 可用性目标保持。

以下保留 scan-exit 阶段记录；其中动态 setup 生产缺口已由上段闭合。

2026-10-08：[实际 scan exit 的双分支执行](multi-array-scan-exit.md)已将
dimension／bound／scalar／受限 locator 前提运输到检查出口，接实际 checked
candidate、公开 iterator restore 和同出口的 original AST fallback。三模块／
11 端点独立审计通过（6 闭合、最多 14 项旧 globals），97 项绑定及 parent
closure 保持旧 42-global 基线，无新增公理或 kernel／host 改动。**第一项的
canonical runtime scan、coverage、actual exit 与局部 versioned execution
现已闭合；下一项生产仍显式的 numeric／layout／box／profile 前提，并由
typed factory 生产静态／region 证据，同时推进两 store 的 loaded 原源 prefix／
header 保持，随后接同族 selected Csem→Asm。**此 alias-choice 局部定理仍
以 setup 成立为前提，不能称为已覆盖 setup 拒绝的完整 guard 或新整程序编译器。
本轮再次 fetch narrative，远端仍为 `12419c1`，正文与 main 一致；按其三方
责任和实际 polyhedral pipeline／OLO 可用性验收继续实现。

以下为前一 canonical scan 阶段的记录，actual exit 缺口已由上段闭合。

2026-10-08：[静态多数组 runtime pair scan](multi-array-runtime-pair-scan.md)已完成
canonical 两数组同坐标源的固定 Clight AST、运行时双矩形遍历、自己的 flag
初始化、原源执行许可与 footprint separation 接线。四模块／15 端点独立审计
通过（7 闭合、最多 6 项旧 globals），113 项绑定及 parent closure 保持旧
42-global 基线，无新增公理。**下一项是将 entry locator／模型前提运输到实际
scan exit，接真实 candidate 执行和公开 iterator 恢复；随后适配两 store 的
loaded 原源 prefix／header 保持，组装 data factory 并接 selected Csem→Asm。**
当前扫描运行成本为点数平方，flag 变 false 后仍检查所有已许可点；不是 loaded
source 的拒绝短路／前缀推进，也未新增 compiler／C／Asm／cost。下列第一项的
canonical code／coverage 已闭合，actual exit 与完整 factory 尚未闭合；完整
OLO 目标及三方责任保持。

2026-10-07 再次 fetch narrative：远端仍为 `12419c1`，两份正文与 main 一致。
[源码对齐复核](topdown/implementation-alignment-2026-10-07.md)明确：kernel 止于
local guarded correctness；语言证明 check／frame／progress／安装；domain 证明
足够前提、推导、coverage 与 actual source/candidate 对应。源码使用者给标注 C
与 phase/tile 选项，不为缺失证明填写 semantic callback。Host 条款拆分仍是开放
设计问题，不先重构 kernel。该方向与完整 OLO 验收继续属于 active goal。

1. **静态生成多数组 runtime guard。** 生成的 AST 只依赖静态 source metadata
   和资源选项，未知 counts／parameters／locations 在运行时观察。已有
   entry-indexed reference footprint 不当作该实现。验收检查安全、动态 coverage／
   接受充分性、private frame、actual guard-exit 运输和 data factory 证据生产；
   不能以前置 `NonAlias` 许可检查自身。Canonical temp-bound scanner 及双分支
   出口执行和完整 setup guard 已闭合；下一验收是任意 program-live frame／
   typed factory 及语言 host 接线，不能将证据生产交给源码使用者。
2. **同族 loaded 原源推进。** 每个实际 point 获得 read/write 许可，逐条证明
   两次 store 保持 captured headers 后，才推进下一 original source test。
   完整接受导出 cached 源；拒绝不观察未来地址。不能用尚未建立的完整 cached
   rectangle 执行许可该 scan，也不能从 permission transport 推出 entry 值定义。
3. **同一程序完整安装。** 将相同多数组证书接到真实 polyhedral phase／codegen
   candidate、公开 iterator 恢复、原源 fallback、family factory、selected host 与
   Csem→Asm。验收 annotated／unannotated、多 site、空域、alias/profile 拒绝及
   continuation；已有单 body 的整程序端点不算新族已安装。
4. **该 slice 闭合后改善条件与可用性。** 用有证书的紧凑充分条件替代适用 scan，
   分别衡量 code size、check work、接受域、完整成本和实例作者责任。条件替换
   复用适用的 candidate／host 证明；cursor 不当作消除逐点运行成本。

下文保留历史阶段记录和当时的下一项。本轮新增完整 canonical condition 与
versioned execution 的局部证明，
没有新增 compiler／native／cost 结论，也没有缩小完整目标。

## 历史阶段记录

2026-10-07 当前：[多数组源许可后继](multi-array-source-permissions.md)已取得 actual first leaf 的两数组 pointer／ld／alpha 观察证据（在 layout／box／alias 前提之前），并沿真实 source trace 将每次 write 的 Writable、read 的 Readable 许可运输回 entry，再接到 actual Clight pointer comparison 的有效、对齐地址证书。四模块／32 端点审计通过（10 闭合、最多 6 项既有 globals），123 项绑定加 parent closure 保持旧 42-global 基线，无新增公理；实际 alloc→Vundef→store→integer witness 明确证明许可不能前移数据值。**下一重点是把 entry-indexed reference footprint 实现为静态生成的 runtime scan，并适配原 loaded-header driver：每个实际 point 获得许可且证明两条 store 的 header 保持后，才可推进到下一源码 test。不能从尚未证明保持的 loaded 原源直接声称整个 cached rectangle 已执行／获得许可。**随后将相同证书运输到 actual guard exit，组装 data factory／region guarantee，接 selected host 与 Csem→Asm，再验证多数组 C／Asm／上下文和成本。该方向继续在 active goal 中；kernel 只负责局部证书组合，语言负责 observation／store permission／pointer primitive／安装，domain 负责来源许可、条件充分性和动态 coverage。当前 reference alias tree 不是可在编译时按未知入口值展开的 runtime encoder；完整安装、loaded-header stability、recurrence／general affine domains、紧凑条件和 OLO 验收仍未完成。

2026-10-07 当前：[多数组完整源循环后继](multi-array-tensor-source.md)已接上真实 active temp-bound Clight nest→固定 entry Loop model→checked generated candidate 的实际 Clight 执行→公开 iterator exit 恢复，四模块／28 端点独立审计通过，19 闭合、最多 14 项既有 globals，无新增公理；123 项绑定加已验证的 parent closure 保持旧 42-global 基线。Registry transport 只约束 checked source array IDs，允许 counter reset 改变无关 raw entries；没有要求整个临时变量环境不变。前一 [body/codegen 阶段](multi-array-tensor-body.md)的五模块／30 端点／11 extracted cases 保持原有范围。重新 fetch 的 narrative／context-lifting 仍为 `12419c1`，正文与 main 一致。**下一优先级是为这份完整源／候选局部定理生产条件：逐个读写的原源 prefix 许可、安全充分的跨 array alias condition、两条 store 对所有 captured header 的保持，以及许可到 actual guard exit 的运输；再构造 data factory 和 region guarantee，消费 selected host 接 Csem→Asm。不能把尚未生成的 availability／NonAlias 前提留给源码用户做 semantic callback。**Kernel 仍止于 local guarded correctness；语言提供 memory/frame/control/install 定律，domain 负责模型／充分前提／condition derivation。`alpha==0` 不使 copy body 保持原内存，第二次读取可能依赖第一次写入的初始化，entry guard 必须证明 forwarding 或使用其他 source-licensed 表达式。当前未新增 multi-array runtime guard、C／Asm 安装或成本结果；已有 flat multi-pointer 整程序入口不算同一 loaded/Horner 路径完成。Recurrence／general affine domains、紧凑条件和 OLO 可用性继续属于 active goal。

2026-10-07 最新：[单位 tile 与 positive offset](unit-tile-and-positive-offset.md)已用 untrusted singleton completion／all-unit mapped proposal 通过八种实际 domain checker 与单区域安装探针。相同 completed compiler 的真实 `*h+1`／`h[1]+1` 矩阵通过 1,215 未插桩 Asm／540 独立 Clight 检查，覆盖 wrap、空 root／不可用 child、header alias、多 site 与 context。两项新语言模块的八端点（五闭合，其余四项既有 globals）解释实际 cached profile 所蕴含的 mathematical no-overflow；不是新 runtime encoder 或 compiler theorem。Kernel／source factory／selected host／42-global Csem→Asm 入口保持。**下一域验收是同一流水线的双数组 statement sequence，以及 k 从 1 开始的真实 recurrence：前者接实际各访问的 source-prefix 许可与多 pointer 模型，后者扩 lower/domain 与 neighbor access 并区分合法交换和非法依赖反转。证据须由 checked source data 生产，不能让 caller 补 simulation。**完整单位矩阵已通过 2,352 Asm／1,792 Clight 检查，含全部八种 mask 与两种 layout；不把 probe 安装或旧路径 multi-pointer 服务当作新的整程序能力。新的 unit／offset 变体没有成本结果，完整 goal active。

2026-10-07 最新：[收紧 actual candidate 的边界](tight-loaded-word-candidates.md)定位并修复了 untrusted affine adapter 将每个 tile 的点循环扩大到完整 source extent 的枚举问题；新 proposal 保留 tile-local bounds 并提出 guard 精简，最终 source/candidate checker 重检。复用同一 zero-preparation Csem→Asm 入口、原 42-global 基线与 closed kernel，零新增 Rocq 模块／公理。七配置 784 未插桩 Asm 与 336 独立 Clight 分派检查通过；[2,3,2] 两种坐标序及 [4,5,3] 接受，[1,1,1] 因 codegen 消去 tile 维而与 witness depth 不符、静态拒绝安装。失败 audit 完整保留，后继复用三个编译结果只读并重跑输出。新 1,152 配对批次的 dense 零值成本 row 21.00→2.97、column 19.36→2.97 倍 source；48 组实际指令计数 row 939,471→167,282（source 63,749），两代仍各 4,805 RMW stores。所有 Clight guard diagnostics 不变，非零仍扫描。**下一项：通过 checked proposal／bridge 支持被消去的 degenerate tile 坐标；推进 source-licensed nonzero 紧凑条件，并在有实际重排收益的 workload 上验证完整成本与 profitability；继续扩 general loaded affine domains／dynamic layout／完整 BT 及比较作者责任。**不是 source speedup，也不是完整 OLO 功能完成；完整 goal active。下文保留各阶段范围。

2026-10-07 最新：[zero-RMW条件的完整安装](zero-loaded-word-installation.md)已从原正域首点生产scalar许可，证明值保持的original／cached对应，并运输helper／flag到实际canonical及完整guard出口。通用preparation adapter与data factory接新的selected Csem→Asm入口；七后继模块／21端点／610依赖独立审计保持旧42-global基线、零新增公理，kernel保持。新提取编译器完成真实调度／分块／codegen；560未插桩Asm与224独立Clight分派通过，两个不同header raw值可与output别名且alpha=0接受。非零保留旧scan；空域／profile／start拒绝跳过scalar检查，fallback保持完整原足迹。**同输入旧／新1,152配对批次已完成：dense零值scan从4,805降到0，但row完整成本17.57→20.65倍source，column20.09→18.98倍；alias新增接受约4.1倍。下一项优先定位实际candidate lowering／公开出口／backend成本，再改进nonzero紧凑footprint和profitability策略。**一般loaded域、动态layout／BT完整原例、代表性benchmark和作者负担仍未覆盖，完整goal active。以下记录保留各阶段当时边界。

2026-10-07 最新：[同一loaded族的condition与成本](loaded-word-condition-cost.md)复用冻结v3未插桩Asm完成20轮／720配对计时批次，全部按实际重复次数核对完整数组与公开出口。Clight诊断独立计guard工作：31×31×5接受域扫描4,805点、22,243次if；完整调用row／column成本为source的17.69／20.43倍，当前简单RMW没有收益，不能把全部开销归给scan。新的源码checker、成功原RMW许可scalar、`alpha==0`到所有已定义Mint32观测保持及现有readonly_condition编码已证明；23端点／554依赖、四闭合、最多六项既有globals、零新增公理。两个不同raw header可与output别名；尚未安装新条件。**下一项直接证明positive source-prefix许可、capture／helper／check-exit到canonical源的值保持路径，接新的data factory／selected compiler并重做同C与成本；同时推进nonzero RMW紧凑footprint条件、候选lowering成本和profitability拒绝策略。**成本、接受域和完整安装分别验收，不用局部条件证书替代已安装优化，也不把当前微型输入当作benchmark收益。Kernel及历史证据保持；完整goal active。

2026-10-07 最新：[loaded-word factory及前端安装](loaded-word-family-factory.md)已从AST／WORD／scope／typed private pool产生静态证据与canonical tensor package，消费actual generated candidate checker，导出局部contract并接三个selected Csem→Asm入口。26／8／7端点独立审计均保持42-global编译器基线，零新增公理。真实前端reset和leaf的skip以及header[0]由语言等价性定理覆盖，回退使用等价基础源AST。v3提取和同一loaded＋runtime-Horner C的真实调度／分块／codegen安装通过420未插桩Asm及168独立Clight分派调用；changing-header alias／profile／layout回退、条件式空域、marked／unmarked、多site和continuation均验收。先前源码匹配失败和输出完整保留。**下一项在同一已安装族上改进condition并量化接受域、guard工作、代码尺寸、配对完整成本及作者责任，同时按完整目标扩source／domain能力。**下文历史下一项保留，以本段为准；完整goal保持active。

2026-10-07 最新：[loaded word完整driver](tensor-loaded-word-driver.md)已组合
原源许可的conditional capture／profile／helper初始化／全scan，并导出实际scan
出口的canonical tensor源执行；完整numeric／layout guard及实际生成candidate
checker接到同一次完整check出口，公开counter恢复与原final memory保持。新的
局部`projected_region_contract`可供Clight host消费；原AST fallback有独立
footprint运输。22端点／524依赖独立审计通过，无新增全局公理，kernel保持。
Incoming caches／helper为None的接受、alias拒绝、profile拒绝跳过undefined data、
空outer跳过不可用child／helper、非零起点跳过capture均已证明。通用full guard／
candidate接线是语言／domain定理；实际fixture仍为旧wrapping地址，未实例化
runtime-Horner RMW的完整候选路径，没有新的compiler／C／Asm／cost。
**下一项直接实现data-only loaded-family factory，生产实际AST／WORD／scope／
freshness和canonical tensor package及accepted-entry证据，接selected progress／
placement和新Csem→Asm入口，再提取同一真实loaded／dynamic C流水线。**继续
验收marked／unmarked、多site、alias／profile回退、条件式空域和continuation。
完整goal保持active；不以局部contract或新端点替代完整程序与后续条件／成本验收。
下面各阶段“下一项”保留核对当时范围，以本段为准。

2026-10-07 最新：[完整word outer扫描](tensor-word-outer.md)已闭合全部
row／column／literal-component检查及接受后的实际nested cached源执行，并将
缓存源运输到实际scan出口，保持原final memory及protected public exit。Header
laws／observer scope由actual receipt生产，runtime语法只用固定地址templates；
fixture实际消费该adapter。41端点／456依赖独立审计通过，13闭合端点，最多
六项既有CompCert globals，无新增公理；真实两loaded bounds的接受／alias拒绝、
可能变动bounds的原源完成、空outer和拒绝后跳过未定义读取均已证明。Kernel、
旧报告及保留草稿保持。**下一项是条件式capture／profile／scan完整driver，
canonical tensor与完整guard出口参数，接真实生成candidate，再由data factory
交付local/site证据并接selected Csem→Asm。**本阶段没有新增compiler／native／
cost；单独完整scan不算同一loaded／dynamic C的优化已安装。完整goal继续active。

2026-10-07 [本次 narrative 责任核对](narrative-responsibility-check-2026-10-07.md)
重新 fetch 并读完12419c1的澄清，正文与main一致。明确区分 `C_host` 的局部
choice定律与语言／site的整程序安装；逻辑证书链不变成源码使用者的语义callback。
进行中的outer证明按“原源许可→接受推进前缀→cached源／模型到实际guard出口→
真实候选与公开出口→factory／site／selected host”验收。Outer草稿不计入已审计
成果；三方责任及最难的状态连接见上述记录。Host条款仍是开放设计问题，kernel
保持；同一loaded／dynamic C的完整流水线及后续条件／成本验收继续属于active goal。

2026-10-07 最新：[loaded column 扫描](tensor-word-column.md)已补齐当前行的完整
column／literal-component私有扫描、逐列原源前缀推进、完整接受后的实际cached
child-loop执行，以及接受当前行后推进原outer前缀。检查许可仍来自原源执行，
不预设cached源可执行。独立37端点／452依赖审计通过，13闭合端点，其余最多
六项既有CompCert globals，无新增公理；真实内存接受／alias拒绝、原loaded
child-bound可能变化时的完成执行、同出口cached执行和零列跳过未定义检查均已
证明。最小kernel、旧报告和未跟踪草稿保持；没有新增compiler／C／Asm／cost。
**下一项是用当前行step执行完整outer扫描，导出整个nested cached源与canonical
tensor对应，再接真实candidate、完整guard、data factory和selected Csem→Asm。**
首点、component或column服务均不当作loaded／dynamic整程序集成完成。
完整目标active；下面保持narrative验收顺序和历史阶段范围。

2026-10-07 本轮重新fetch并读完narrative与context-lifting：远端仍是
`12419c1e1e3da450bf378742a2fb4e204e51e060`，两个正文与main一致。
以下顺序落实澄清，不新增kernel接口或要求使用者手填四份语义callback。
当前真实tiling路径已经闭合；loaded＋dynamic的后继验收细化为：

1. **实际原源→完整缓存源。** 从loaded source的实际执行生产条件式capture、
   原inner／outer前缀和每个动态word地址的检查许可。接受本点并证明两个raw
   header保持后才推进原前缀；拒绝停止后续检查。完整接受再导出整个nested
   cached源执行，禁止以假定cached源可执行来许可未来检查。语言库负责word／
   permission／frame／scan执行定律，domain producer负责源shape与header接线。
2. **缓存源→真实候选。** 连接literal准备、canonical tensor模型、numeric／
   no-wrap／layout／dependence条件及actual guard-exit状态；复用已接通的真实
   scheduler／prepared codegen、最终candidate checker和公开出口恢复。保持
   raw-codegen与adapted-candidate两条证据的区别。静态AST／scope／freshness
   由该family的数据checker生产，不能把缺失的对应变成caller语义假设。
3. **同一个程序的安装验收。** 新factory接selected Clight host和Csem→Asm，
   验收同一loaded＋runtime-Horner源的接受／alias拒绝／profile拒绝／条件式空域、
   marked与unmarked、多site和continuation可见出口。已有首点／component定理，
   或分离的loaded与dynamic示例，均不能替代该完整程序证据。
4. **随后改善条件与衡量可用性。** 在上述范围闭合后提出紧凑充分条件，独立证明
   安全、acceptance soundness及entry-state transport，复用candidate与host证明。
   分别测接受域、guard工作、code size、编译／完整运行成本和实例作者工作，
   与OLO同类源问题比较；cursor代码缩小不当作逐点成本消除。

具体端点与责任见[narrative到真实候选接入记录](narrative-to-tiling-integration.md)。
Host边界条款仍是待实际实例检验的设计问题，保持现有局部／安装责任边界。
本轮为计划细化，没有新增proof／native／cost结论；完整目标继续active。

2026-10-07 当前：[narrative 澄清与真实分块接入](narrative-to-tiling-integration.md)
按远端12419c1落实三方责任：kernel组合局部证书；语言host负责检查语义、private
资源、公开frame／出口、placement／progress及完整程序安装；domain负责前提、
源／模型、真实候选执行和条件编码。最小kernel与原guard证书保持，不将host
contract clauses的开放讨论当成已完成API。新的data接口携带实际候选Loop＋
point-space witness；不再由两项tile size重构固定目标。真实Pluto affine／tiling
phase经验证和prepared codegen；原始min／max／floor边界无法再提取的问题由
不受信任的自动仿射边界展开提出候选，再通过已有已验证source／candidate
checker取得完整对应、前向执行与公开出口恢复。两份Loop均保存；没有单独
raw→adapted等价性定理，raw codegen后向定理不冒充最终候选证书。
独立13端点／442依赖审计、提取与新selected Csem→Asm端点通过，保持42-global
基线、零新增公理。新矩阵648汇编／288独立Clight调用通过三组tile sizes、两种
layout、marked／unmarked、多site、runtime回退和外部失败／损坏输出；不是成本
或收益结论。**下一项在同一真实pipeline组合loaded bounds＋dynamic layout，
再验收稳定性条件、条件生成的手工负担、接受域、guard工作与完整成本。**
继续把OLO作为功能和可用性验收参照，不用端点数或调用数代替能力覆盖。
完整目标active，计划不再将固定候选fixture视作polyhedral pipeline完成。

2026-10-07 前一阶段：[真实 affine pipeline](connected-polyhedral-pipeline.md)已接通
标注C→canonical source／实际extractor→OpenScop→Pluto→checked affine import／
validator→PolCert prepared codegen→原有mapped-domain factory／lowerer／guard→
selected host→Csem→Asm。新增桥接2端点／88依赖独立审计，零新增全局公理；
既有selected compiler／42-global基线和最小kernel保持。新native矩阵648汇编／
288 Clight调用验收实际phase、marked／unmarked、多site、runtime回退及外部失败／
损坏输出。独立layout phase从访问矩阵自动提出非恒等(j,i,k)调度，另144汇编／
144 Clight调用通过；目标Loop由真实codegen产生。Pluto在这批源上自身保持原序，
不把layout heuristic归给Pluto。实际完整调用链和中间IR已保存；没有新成本结果。
兼容路径复用ExtractorCorrect／AffineValidator／PrepareCodegen，没有literal
调用旧PolOpt.Opt_prepared；strengthening及真实tiling phase尚未连接。先前“真实
scheduler／prepared codegen未接通”保留为当时记录，已由此有界slice推进。
**当时的下一项是连接checked tiling transition与生成代码的point／reindex／progress witness**，
再扩loaded-header＋dynamic layout，并验收guard工作、接受域、代码尺寸和配对成本。
Framework仍止于局部证书组合；语言负责安装，domain负责模型与实际候选执行。
远端narrative再次fetch仍是12419c1，与main澄清正文一致；完整目标active。

2026-10-07 当前：[显式标注选择与安装](selected-polyhedral-regions.md)已实际接通
新selected compiler：Cabs中保留pragma请求、fresh label／manifest经归一化传递，
Clight语言host按选中位置限制遍历，避免改写同形未标注循环。13端点／438依赖
审计、提取、648汇编调用／216独立Clight分派和14个frontend边界案例通过，零新增
公理；新Csem→Asm端点复用原literal tensor guard／candidate。Kernel和旧报告保持。
此entry默认marker-only；旧binary仍是冻结回归。Parser metadata pass不是新的
verified Cabs frontend，端点仍从Csyntax开始。当前candidate仍由旧Loop策略产生，
**真实scheduler／prepared codegen未接通**，不能据此关闭polyhedral集成里程碑。
下一项立即实例化实际流水线：补齐`GuardMemoryInstr.to_openscop=None`及phase
export／scheduler，保留阶段IR和验证结果，消费真实prepared-codegen Loop并核对
lowering／progress／guard-exit参数及公开出口，再跑同路径marked C。已有word-column
工作保留，不先扩完所有源类。具体责任和边界见上述记录；完整目标active。

2026-10-07 优先级更新：已读取 narrative 最新 `12419c1`（新增 `1c63ccb`／
`12419c1`），同步正文并完成[真实流水线接入复核](narrative-pipeline-review-2026-10-07.md)。
**下一集成里程碑改为 `#pragma scop`／`#pragma endscop` 显式区域选择，以及
真正的多面体提取→调度／变换→验证→代码生成→guard／原源fallback→Csem→Asm。**
默认只向loop pass提供标注区域；同形未标注循环也必须不被安装表改写。
先选择一个已有完整证明的source family接通实际流水线，不等待所有word
inner／outer与后续source扩展。已开展的word-column证明保留；只优先关闭本次
集成需要的直接依赖。先证明后改进guard成本的顺序继续成立，但不用于推迟实际
optimizer接入。内置Loop候选仍作回归／外部API，不再作为该里程碑完成的证据。
验收须同路径保存中间IR／validator结果、实际scheduler／codegen调用，覆盖
标注与未标注、多site、静态拒绝和动态回退，并有新完整程序端点及native C。
最小kernel保持；语言负责位置／安装，domain负责条件模型与生成候选对应。
全文以下较早的“下一项”保留当时记录，以本段和新复核的顺序为准。完整目标active。

2026-10-07 当前：[narrative复核](narrative-review-2026-10-07.md)确认远端
`271f6fc`与main正文一致。保持“先闭合约定范围、再改进条件”的顺序，并行
维护实际LNCS正文；kernel只负责局部证书组合，语言提供执行／安装定律，domain
生产模型假设、入口义务和实际源／候选对应。四条逻辑链不变成四份用户手填record。

[Word component scan](word-component-scan.md)已关闭动态变量乘积下的完整
literal第三层私有cursor扫描：逐点许可来自真实源前缀，接受保持两个header后
才推进，拒绝停止未来检查。完整接受导出实际cached-loop执行和相同退出状态。
40端点／447依赖独立审计通过，无新增公理；真实内存五次原源store与actual
scan接受／alias拒绝已证明。最小kernel及旧报告保持，没有新loaded tensor
compiler／C／Asm入口。该family的data-only factory仍需生产静态scope／freshness
证据；当前语言服务不等于新使用者界面已经交付。

下一项：把该component保持接到真实inner-prefix advance，继而覆盖全部outer
rows，导出完整nested cached源与canonical模型；核对model-entry到actual check
exit的frame、numeric／dependence和候选出口，接factory／语言host并运行完整C。
这一slice闭合后转入紧凑充分条件、实际guard工作／接受域／配对计时与作者责任
比较，不等待全部未来frontend／polyhedral扩展。Cursor缩小代码不等于消除逐点成本。

2026-10-07 最新：[loaded tensor 首点服务](tensor-header-point.md)交付 typed
word算术运输、原store权限到guard-entry运输、observation分离／保持、条件式
header capture和同一次原源执行到首点实际check的组合producer。40端点／445
依赖独立审计，无新增公理；fixture覆盖真实动态Horner RMW、机器中间值wrap、
两header保持及alias拒绝后跳过未定义测试。旧208端点／native／cost保持。
**接下来关闭完整逐点source-prefix链**：每次接受后生产下一第三层／child／outer
点的实际执行与权限；拒绝停止未来检查；完整接受再导出cached source。随后
连接动态tensor guard、literal准备、实际candidate入口／公开出口、data factory
和语言host，验收同一loaded＋动态layout C 的接受／回退／上下文及完整成本。
首点服务不是完整优化器；本阶段没有新Csem→Asm入口、C／Asm matrix、成本或
比较作者工时。Narrative的最小kernel与三方责任保持，完整目标active。
以下保留各阶段的当时范围。

2026-10-07 最新：[literal-bound tensor](tensor-literal-bound.md)已把实际 `<5>`
接入private初始化、原源到prepared canonical执行、guard-exit候选运输、原AST
fallback和expression-progress安装，完整Csem→Asm与提取／运行均通过。
208端点（旧181＋新27）／440依赖，无新增全局公理；八配置1,152汇编／432
独立Clight调用，含两种地址次序、literal 3／5／0／6、两site和goto／memory。
[本轮narrative吸收](narrative-literal-bound-check-2026-10-07.md)落实三方责任、
四条逻辑链与最难的状态连接；重新fetch仍为`271f6fc`，main正文一致。
Kernel、旧proof／native／cost证据保持；没有新成本或作者工时测量。
**下一功能项是 loaded `grid[0]`／`grid[1]+1` 与实际动态Horner layout的同次
rewrite**：必须生产源路径capture许可、header稳定、raw→cached→prepared入口、
guard exit与候选／公开出口对应，再验收同一实际C的接受／回退、安装及完整成本。
不能将旧固定布局loaded实例和新tensor实例相加称已覆盖完整OLO／BT。
随后继续更多body／cross-tensor alias／affine domains、最新入口source-only
rebuild与代表性性能／比较作者工作。完整目标active。以下各段保留历史状态。

2026-10-07 最新：[坐标次序实例](tensor-coordinate-order.md)已经以数据提案接入
`[j,i,k]`，并保持旧`[i,j,k]`实际源。原181端点证明／kernel／host不变，七配置
504汇编／216 Clight调用核对两种源、全部6,144 words、连续两site和goto／内存
上下文；错误坐标、reindex和零tile均静态拒绝。[单独成本实验](tensor-coordinate-cost.md)
30轮／960批次在stride<2048 profile上测得大stride输入的交换／tile完整成本为
source的0.764／0.899倍；小输入负结果、回退和raw数据均保留。
下一功能项：复用`constant_loop_preinitialized_model`，把实际literal `<5>`
接到fresh typed helper准备、raw→prepared canonical source、guard exit／原AST
fallback运输；安装实际使用已有expression-progress host。当前temp-bound host
不能直接接受literal子循环，不能只做AST替换。随后组合loaded-bound／动态
layout、更多body／cross-tensor alias／affine domains；source-only rebuild和
比较作者工时仍未由这轮实测完成。完整目标active。下面是各阶段的历史状态。

2026-10-07 当前：[tensor 成本](tensor-region-cost.md)已验收30轮／960 fresh-process
batches。实际prefix无scan，三个接受输入30／1,125／4,805源点都执行39次判断；
当前行连续RMW源的交换／tiling无净收益，所有negative results／raw data保持。
[责任清单](tensor-proof-ownership.md)核对39新端点的语言／domain／接线／fixture
归属；数据factory生产已支持family的local/site证据，未测其他framework作者工时。
[OLO核对](olo-tensor-comparison.md)继续区分本例的temp bounds和Figure1的loaded
bounds／+1／literal third bound，不把分离实例相加称完整覆盖。
下一项用已有parametric coordinates接入原先按列访问、重排后按行访问的实际源，
复用原checker／host并测有利场景；继续literal-bound transport和loaded-bound／
动态layout实际组合，再扩展body／alias／affine domain与完整BT。
Kernel与原181端点／native证据保持，完整目标active，见
[checkpoint](research-checkpoint-2026-10-07-tensor-usability.md)。
以下保留各阶段当时验收状态。

2026-10-07 当前：[tensor region compiler](tensor-region-compiler.md)已连接实际原
AST、数据 factory、kernel local certificate、typed pool／progress／语言 host 与
Csem→Asm。行政 skip 运输修复了真实前端全回退；181端点（旧142＋新39）／368
依赖审计、完整提取、216 assembly／108 Clight dispatch calls 通过。三个函数
覆盖 RMW 交换／tiling、两次 rewrite、公开退出值、goto 和外围 memory effects。
当前仍是 positive rectangular temp-bound nests、单 Horner RMW leaf、一个 tensor。
[本轮 narrative 核对](narrative-implementation-check-2026-10-07.md)固定三方责任、
四条逻辑链和 local／installation 边界：kernel 保持，host 与 site 另证安装。
该子集端到端闭合，下一项立即做同例 OLO 的 code／check-work／接受域／完整成本
与作者负担比较，再扩展 literal-bound、body／affine domains、跨 tensor alias／
loaded stability 和完整 BT。暂无新入口成本、GDB probes 或 source-only rebuild。
证据见 [checkpoint](research-checkpoint-2026-10-07-tensor-region.md)。完整目标 active，
以下保留此前阶段的当时范围。

2026-10-07 当前：[tensor 坐标条件](tensor-coordinate-guard.md)已将全部 affine
read/write 的 box extrema 编码为安全 signed32 Clight checks。实际 full guard
接受生产 count/scalar bindings、pointer/dimension view、BOX 和 candidate 输入，
连接真实原 execution 到 mapped／tiled execution 与公开 iterator 恢复。
142 端点＝此前 111＋新 31／306 依赖审计、13 项提取运行通过；提取不执行生成
Clight，无新整程序 compiler。静态 profile 必须由实际入口 checks 验证，不是
caller semantic callback；不支持的运算静态拒绝，profile 外输入运行时拒绝。
下一项按 [checkpoint](research-checkpoint-2026-10-07-tensor-box.md)交付原 AST
data factory／kernel local certificate，再接 literal-bound transport、source
progress／private resources／placement 与 Csem→Asm；当前仍为 positive
rectangular temp-bound nest、单 leaf、一个 tensor。Narrative 重新 fetch 仍为
`271f6fc`，main 正文相同。最小 kernel 保持；不把执行桥当作完整安装。约定子集
闭合后立即同例比较成本、接受域、bytes 与作者工作，不等待全部扩展。完整目标 active。

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
