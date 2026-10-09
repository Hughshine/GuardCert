# 验证责任、证书边界与最难的验收

## 持续适用的责任表

2026-10-08 对照 narrative 新版本 `8ce9c8b`，已同步 PolCert／CGO 2017
原案例、顺序功能／效果与逐配置 whole-program delivery 要求；此前 guard library 的
分类／依赖契约与 source/model 方向和前提来源澄清继续适用。本表约束后续阶段，下面的日期记录保留各阶段当时的
交付范围。

验收来源与优先级见[原程序对齐计划](benchmark-alignment.md)。每条支持配置
都必须把实际 source、guard、candidate、fallback 和公开出口连接到对应
source `Csyntax.program` 的 Csem→Asm backward simulation；不是只提供
local 或 Loop→Loop 结果。Factory/site 生产 invocation、scope、placement、
progress、typing 与 private resources，源码用户不补 unproved semantic
callbacks。已有有限／open host 和 backend 可复用，按真实 progress 要求
选择；不能从终止执行的证据推出可能发散的替换正确。安装随每条功能扩展
交付，不能以 clause factoring 仍是设计问题为由延期。

[首轮原案例尝试](original-benchmark-first-attempt.md)进一步定位这条责任链：
原 62 项 harness 与 BT 能通过 baseline 编译／运行，但没有新 optimized target。
新增 double value instance 复用语言 memory footprint 的独立交换，optimizer
仍须保持真实访问依赖和每个 IEEE 表达式树。现有 forward expression bridge
消费 typed operand receipts；原源 decode、Mfloat64 地址／alignment／权限、
I64 控制与公开出口的实际 producer 尚缺。不能把这些前提移交给 marked C
用户，也不能用 generic `INSTR` 的实例化代替完整 source/candidate／guard／
factory 安装。本轮 kernel 与现有 host 不变；下一项验收是原 matmul 的整条链。

| 证明或证据 | 提供者 | 当前接口与验收含义 |
| --- | --- | --- |
| 局部 guarded 正确性 | Kernel | `guardify_refinement` / `guardify_preservation` 消费证书；refinement、preservation、equivalence 保留各自方向 |
| `C_opt`：假定成立时实际候选正确 | 优化器／domain 库 | Source/model/candidate 执行桥和已验证 candidate checker；不仅是数学模型的调度结论 |
| `C_derive`：入口事实推出模型／局部义务 | Domain 库 | 范围、稳定性、footprint、alias 等充分性；不是任意 source/candidate 的通用 assumption extractor |
| `C_guard`：实际检查安全且接受推出入口事实 | Language 服务与 domain producer | 原源许可实际读取，machine arithmetic、短路、private-state 运输；domain 选择可编码的充分条件 |
| `C_host`：实际分派满足局部 choice law | Language／IR adapter | `guard_host.select_exact`；private Boolean 或嵌套控制也可实现，不要求固定 `if` AST |
| Region guarantee | Domain factory，使用 language 定律 | 实际 source/guard/candidate 的执行、公开 temp/memory/trace/control 边界，以及所需 progress |
| Context requirement 与安装 | Language host；site checker 生产具体证据 | Scope、合法入口、资源、continuation、progress 和 backend；不是 kernel 自动获得 contextual closure |
| 有限次 rewrite 组合 | Kernel／composition 库，消费每步已安装证明 | 每步针对实际中间程序重新满足 domain、placement 和 freshness；不保证搜索算法终止或收益 |

`context_certificate.lift_refinement` / `rewrite_context.rewrite_lift` 是
host 提供的定理字段。具体 selected Clight host 以 `program_temps` 为保守
公开集合，消费 `projected_region_contract` 和实际 source progress；目前
没有自动最小 liveness 或通用 boundary clause algebra。

源码用户和新实例作者的工作量不同：支持族的源码用户给标注 C 和策略；
新语言作者证明 host/installation；新 transformation 作者提供前提、局部
对应及适合该 host 的 guarantee，或实现能生产它们的 checked factory。
框架消费一个定理前提不等于已经自动生产该前提。

Concrete-to-model decode、model transformation、model-to-Clight execution 和
public-exit 恢复分别标注方向与范围；polyhedral validator 不自动生产
Clight-to-Loop 桥。Static checker 给 syntax/shape/resources，runtime
conditions/captures/transport 给 dynamic facts，original source execution 是
语义证明起点而非 runtime pre-execution。最终 factory/installation 必须
discharge 适用前提；单向 decode 不叫独立双向 equivalence。

目前最难的链是**原源许可的部分状态 → 安全可执行条件 → 实际候选入口
→ 公开出口／continuation**。Canonical domain coverage、实际 scanner、
allocator、ranges/receipts producer、factory/compiler 与 native 已分别验收；
完整成本独立记录。Scanner 中私有 cursor/flag 可改变，memory 保持并 frame 公开状态；
它不因此成为要求完整 entry state 相等的 `readonly_condition`。

Clause factoring 的具体约束继续采用
[先前代码对照](narrative-kernel-host-review-2026-10-08.md)：finite contract
消费完成执行，open protocol 匹配可能无限的 source steps；可以复用 exit
relation，不能仅凭 exit weakening 推出含入口/scope/progress 的完整 contract
entailment。先证明实际复用再更改 API。

### Guard library 的契约责任

2026-10-08，[runtime empty alternative](affine-empty-runtime-installation.md)
落实带private effects的alternative责任：language library证明actual read
prefix的精确replay，以及接受的fast出口／拒绝的source replay entry到旧
opaque small-step projected contract的连接。Domain复用signed condition／
actual empty-source，factory自动生产prefix／capture／typed/fresh条件并实例化
该producer，再消费旧candidate和selected installation。15端点无新增公理；
RMW同408输入保留126candidate、新增58empty，zero-width保留60candidate、
新增56empty；kernel／host／validators与源码用户API不变。拒绝可能重复
prefix／capture，成本未测。不能把这项Clight服务称为任意Boolean OR或
跨host的boundary algebra，也不能从已有validator自动推出source/model桥。

2026-10-08，[signed header 条件客户端](affine-empty-signed-installation.md)
把具体condition编码与empty source／exit／capture／private choice／安装解耦。
Condition producer提供调用域内safe readonly certificate与同一accepted facts；
客户端消费它，factory从checked source自动实例化。既有generic interval encoder
已经支持signed；新producer改变profile并重新证明其range gate，不能沿用旧
非负范围证书。12新端点无新增公理，add同输入33→87、无损，极大profile
静态refusal复用旧builder；旧candidate／host／kernel保持。

2026-10-08，[共享 fallback 后继](affine-empty-plan-installation.md)进一步复用
既有domain条件／actual empty source与出口证明。Clight choice library负责
readonly alternative factoring、私有Boolean执行与公开投影；site factory
检查第三个typed private和condition／branch／live freshness，再接原安装host。
9新端点无新增公理，2,280／2,280逐输入输出和path保持；triangle原源loop
从32份到1份。Kernel和candidate checker均未改；signed编码和旧candidate
内部的runtime组合仍归各自producer／language责任。

2026-10-08，[header-only empty rewrite](affine-empty-installation.md)进一步
检验责任边界：domain的仿射endpoint事实只需header words；language构造
不执行leaf的actual source execution，并证明空outer／负child的精确公开出口。
Factory从original source/capture生产调用前提，接共用host/backend到Csem→Asm；
源码用户仍只给marked C／配置。该rewrite的局部正确性不需要调度C_opt，
kernel不改。29端点无新增公理，2,280／2,280及旧五族同binary通过。
该历史阶段的非负参数profile、tree复制fallback、缺少旧候选内部的runtime empty选择分别
属于编码、language lowering与factory组合的后继工作；不是kernel自动解决。

[分类与源码对照](verified-guard-library.md)覆盖 arithmetic、ranges/footprints、
separation、observation preservation 和 conditional control。它是 kernel
之上的服务目录；各项先分开记录 safe invocation requires 与 accepted ensures，
并列出 reads、private writes、public/memory/event/control frames 及 refused exit。
框架不会自动生产 source 的 load receipts 或把范围事实变成 allocation。

Domain 选择并证明充分条件，如 separation 或 value-preserving writes 到
同一 header observation relation；language 证明每条实际路径的读取许可、
机器执行、短路与 state transport。两种稳定性条件都不能单独许可提前 load。
纯条件的 alternative 可复用 branching；带私有写入的 alternative 还需要
第一项拒绝后的入口关系与第二项 safe domain 对接。Factory 继续把这些事实
接到原 C_opt、fallback 与公开出口，host/site 负责安装与 progress。

当前生成式 Clight scans 并不是已经验证的 callable runtime C library；
函数形式还须证明 call/state/link/backend 连接。Shared contract 抽取用实际
client 复用来验收，不能把新 record 或代码行数当作减少作者负担的证据。
本次组织工作不新增 theorem/native/cost 结果，不改变完整 goal 的验收范围。

## 阶段记录

2026-10-08 [Actual-row observation installation](affine-observation-installation.md)
验证 guard-library alternative 的具体责任。Domain 从 separation 与 zero-RMW
各自能力证明同一 reached-row header observation 保证；language whole-loop
transport 消费当前 header-match／word receipts，保持给定原执行的精确出口。
Factory 自动选择 scalar、检查 actual row 与 private resources；numeric
preparation 许可 alpha 测试，再复用 readonly branching 和 compact scan。
Data alias／actual candidate certificate／public restore 仍是独立义务。
新 builder／Csem→Asm 沿用既有 host/backend，kernel不改。

十一模块／29端点／2closed，无新增公理；六配置2,448／2,448输出/context
通过。同源408输入的两compiler接受122→126、无丢失；gain限于alpha0
的N/M重叠。新binary旧四族word400、recursive-affine480、private-loaded270、
zero-width672各自Asm/Clight通过。独立完整成本336 batches全输出通过；
separated-alpha0比旧guard快15.48%／8.26%，新增overlap接受比旧fallback慢，
全部16median高于source。不泛化到完整memory
equality、其他chunks或cross-host共享，也不以该实例替代完整OLO/general目标。

2026-10-08 [Zero-width installation](zero-width-installation.md)已把这些 producer
接到 actual wider-domain C_opt checker、candidate/backend/public restore、
fresh typed capture/result、original fallback和具体 region guarantee。新 builder
先于旧 registry，复用 selected host得到 Csem→Asm；kernel／host／底层
validators不变。十一模块／33端点，无新增公理。六配置2,016／2,016与同
binary word400／400、recursive affine480／480、private-loaded270／270通过。
源用户仍给标注 C 和策略；first-empty-child现有实际接受证据。N/M稳定性
不替代data依赖条件，broader／recursive loaded／完整成本／OLO仍属完整目标。

2026-10-08 [Zero-width stability](zero-width-stability.md)把 domain 的弱 ready
与 source row／物理 permissions 接到 language 的实际 N/M 短路检查、观察
保持和 original-to-cached transport。Readonly ordered preparation 自动生产
完整 input view/ranges；合并检查接受后保留给定原执行的精确 memory 与出口。
十模块／35端点，无新增公理。Kernel、host、底层 candidate checker 不变；
factory 仍须生产 capture/header 调用域、对实际更宽域候选重新检查，并接
compact plan／selected compiler。没有新 native 接受或成本结论，整目标继续。

2026-10-08 [Zero-width model bridges](zero-width-model-bridges.md)落实 narrative
的 proof direction/provenance 要求：actual guard 接受生产完整 typed view
和更宽 width 假设；domain source decoder 只从给定 actual source execution
恢复 Loop 和公开 exit；mapped/tiling wrappers 为新 assumed source/candidate
给出 C_opt soundness；language backend/restore 生产实际候选和公开出口。
五模块／17端点／7closed／1,400bindings／至多旧12globals，无新增公理。
Kernel、host 和底层 validators 保持；不把旧 first-positive certificate
推广使用。新的 loaded-source stability/cached-completion producer 和
factory/compiler/native 尚未连接，源码用户没有新增 semantic callback。
具体候选更宽域的 checker acceptance 尚未实跑，完整 goal 保持。

2026-10-08 [Leading-empty body licensing](leading-empty-body-licensing.md)
区分了三项责任：language 从原有限执行越过 empty child prefix，证明到
later leaf 前 memory／protected ports 保持；domain 用常数个 affine
endpoint 条件建立 first-reached／range 事实；实际 Clight readonly condition
接受后自动生产原入口 body-only 参数的 typing。没有先执行原 source 的
runtime 阶段，也没有新源码用户 callback。五模块／24端点／9closed，
至多旧六项 globals，无新增公理；kernel、host、candidate checker保持。
Factory/compiler尚未消费新服务，native接受域未扩大。下一证明责任是放宽
assumed model的first-positive域并重新取得C_opt，随后接actual source/model/
permissions/stability和安装，不能只修改运行时Boolean而沿用更强域的旧证书。

2026-10-08 [Conditional loaded-affine native pipeline](snapshot-polyhedral-native-pipeline.md)
验收source用户只给原marked C的路径：旧registry固定于Rocq入口，普通proposer
接真实nonrectangular model到Pluto/codegen，原checker和source/model/candidate
证明沿用。后继plan/tree correspondence与private-Boolean transport复用旧
language lowering，静态检查生产typed/fresh flag；kernel／host／candidate
checker不变。15端点／1,850bindings／旧42globals，无新增公理。六配置
1,584／1,584全输出与公开continuation，实际accept/refuse与empty outer/M-null
安全通过；同binary旧word400、recursive affine480、private-loaded270各自
Asm/Clight回归通过。原tree compiler SIGKILL与两次harness错误均保留。
这不是profitability结果，finite-completion、first-positive-child、旧alias
envelope与二维源族边界保持。下一难点是later reached body的许可producer，
不能把未到达RHS的可读性提前假定，也不能把library/cost边界交还源码用户。

2026-10-08 [Checked loaded-affine installation](affine-snapshot-installation.md)
填入 factory 与 guarantee 责任：原 AST 的普通 checker 自动生产 grammar/
shape/protected ports/cache membership；private capture checker 与 typed pool
生产 freshness/declarations。原源许可的 preparation/stability 自动生产
cached completion，并与给定原执行的实际出口对齐，再接原 alias/candidate
checks、source/model/candidate execution 与 public restore。Retained prefix/
suffix 的 finite-region contract注册到既有 selected host，Csem→Asm直接
消费共用语言定理；kernel、host 与 candidate checker不改。九模块／37端点／
17 closed／1,644 bindings／至多旧42 globals，无新增公理。源码用户不提供
semantic callback。提取配置、actual C/native、接受域与成本仍待独立验收；
finite-completion、first-positive-child、旧 envelope 边界保留。

2026-10-08 [N/M stability scan](affine-snapshot-stability-scan.md)补上
concrete condition 到 whole-loop transport：原 row receipts 生产 actual
N/M separation probes 的 safe domain；row 接受后 memory store law 保持
observations 并推进 prefix，拒绝跳过后续 rows。原 active-loop theorem
运输同时变化的 test/body，scan 接受自动导出 complete cached source 与
相同公开出口。三模块／11 端点／1,314 绑定／至多旧六项 globals，无新增
公理。Candidate checker、kernel 和 host 不变；factory 作者仍须
自动构造 checked source/static evidence，接 actual exit、alias/candidate
checks 与安装。尚无新 Csem→Asm/native/cost，finite-completion 和
first-positive-child 边界保持。

2026-10-08 [原 loaded setup 的 snapshot 阶段](affine-header-snapshots.md)
进一步填入 `C_guard` 的 producer 责任：从 actual unchanged source 生产
conditional raw-load receipts 与 numeric preparation word domains，再复用
既有 readonly arithmetic guard。Concrete loaded-row decoder 消费 current
observations，原 source prefix 生产 physical write permissions。七模块／
29 端点／1,332 绑定／至多旧六项 globals／无新增公理；没有新 factory、
Csem→Asm、native 或成本结论。Kernel/host/candidate checker 没有变化。

库作者仍须完成 actual point checks、observation preservation、whole-loop
transport 和 checked source factory。静态 header grammar、cached-body 形状、
cache membership 与 typed/fresh resources 应由 factory 生产；原 source
完成执行由 finite host/site 的 contract 使用，不能改写成框架终止保证。
源码用户仍不承担 semantic callback。First-positive-child 的接受域限制保留。

2026-10-08 [Private-loaded affine actual pipeline](selected-private-loaded-affine-pipeline.md)
进一步验证 guarantee／installation 的复用。旧二维库已负责 original-root
snapshot、bound 与 writes 的分离／稳定性、temp-affine-child source/model、
实际 mapped／tiling candidate、检查和公开运输；新普通 adapter 只把 checked
request 送入已有真实 Pluto／codegen，再把普通 evidence data 转回旧 proposal。
它不生产新的 semantic certificate。新 builder 以 normalization 运输旧 region
contract，新 Csem→Asm 端点直接应用共用语言 theorem，无 kernel／host 变化。

两模块 63 行、4 端点、1,810 绑定、至多旧 42 globals、无新增公理；三个
legacy modules 的 imports-only namespace port 独立重建。源码用户仍只给
marked C 和策略。810／810 新 family 执行、同 binary word 400／400 和
recursive-affine 480／480 回归通过，不是新成本或作者时间测量。旧 envelope
条件的 same-root 限制与 first-empty-child 回退须作为接受域缺口报告。
下一义务是条件 child `*M` 的原源许可／stability 与一般域桥；不能把三
builder 静态分派当作 recursive affine／loaded-word 联合对应已经完成。

2026-10-08 [Actual rank-three codegen](compact-affine-codegen.md)进一步检验
checked algorithm 的复用边界。普通约束压缩返回原 certificates／既有 LCF
运算；`ExactCs.fromCs` 检查全部原约束，消费 forward guarantee 后产生 exact
canonicalization。此 equivalence 只属于该 checked 路径，不能转称其他
abstract-domain `add` 调用都 exact。实际 codegen／完整候选验证与旧 guard／
builder／语言 installation／Csem→Asm 全部接通；没有新 Rocq 模块或源码
semantic callback。1,440／1,440 全输出与公开 continuation、同 binary
loaded-word 400／400 回归通过。单次 9.588 秒／90 秒 deadline 对照是编译
诊断，不是收益评测。

下一难点仍是原源部分状态的许可：actual loaded `*N` 和 affine header
`i+*M` 必须共同产生稳定 snapshot、no-wrap／reached-point 与 candidate
入口事实。Kernel 不知道 load／pointer／affine 语义；domain 生产充分性与
源／模型对应，language 生产安全执行与 frame／transport，factory 与 site
分别交付 guarantee 和 placement／progress。现有静态 builder composition
不生产这个联合源证明。First-path 空 child 的接受域缺口保留。

较早的二维 private-loaded-root／temp-affine-child 路径已有自己的 snapshot、
footprint／stability、候选和语言安装证明；其 request 接口应先评估复用。
这不等于新 recursive affine／loaded-word 模型已经合并，也不许可在原源
未到达时提前读取 child `*M`。按具体源／语义边界区分已有证明与新义务。

2026-10-08 [Signed affine bound proposals](signed-affine-bound-proposals.md)
检验 narrative 的另一种复用：普通候选算法改用有符号包络，原完整 checker
重新验证 actual source／candidate；原条件编码、certified builder、语言
installation 与 Csem→Asm 端点复用。新 interval 算法不是单独已证的条件
服务或 `C_derive`，不增加源码 callback、Rocq 模块或 kernel 义务。真实
二层流水线对 -1／-2 起点实际接受，1,152／1,152 全输出与公开 continuation
通过，同 compiler 的 loaded-word 400／400 回归通过。三层 codegen 和
联合 loaded／nonrect 模型仍未完成；没有新收益或作者时间测量。

2026-10-08 [共享 selected affine compiler](selected-affine-pipeline.md)进一步
落实 domain guarantee 与语言 installation 的分界。`certified_region_builder`
由已证明的 domain factory 注册：实际 source/pool 的普通检查返回 target 时，
交付 `projected_region_contract`。语言库证明静态 or_else、table soundness
和一次通用 selected Csem→Asm；site 仍检查 annotation、原源 progress、
scope／private resources。源码用户不提供该 proof record 或任意 OCaml
semantic callback。Word 和 recursive affine 两实例共享此 host，保留各自
源许可、候选 checker、实际 guard 和公开恢复，不合并语义前提。

新的小范围 scheduler model 是普通提案；final checker 对原 request/
bounds 的接受给旧 source certificate，不信任 proposer 的范围编码或 bound
adaptation。负坐标 proposal 被拒绝及三层 codegen 长运行说明前提必须传到
真实 model/生成过程；kernel composition 无法修复这些具体算法缺口。
二层非负 profile 的 native／Clight 链和同 binary 的 loaded 回归已通过，
无新公理；新的全局证明是一项共用语言证明，而非自动 contextual closure。
Finite progress、公开 continuation 和各次 site obligations 继续单独验收。

2026-10-08 [loop-linear canonical 服务](linear-canonical-alias-service.md)进一步
分离 `C_derive` 与 `C_guard`。域证明只检查循环系数，允许不同常数和稳定
参数系数；实际执行仍用完整地址模板。公共 Clight 适配器从 source/setup
生产 ranges、读取许可、observations 和 actual check execution/frames，导出
精确 canonical Boolean；它不决定该 Boolean 是否足以证明 nonalias。新
服务消费域充分性，再交付现有 accepted entry fact，复用 factory、loaded
contract 和 selected compiler。该适配器仍消费完成 source execution，
不生产 progress／placement／installation，也不是 kernel 的 predicate compiler。

16 端点、9 closed、零新增公理；常规 1,000／1,000、移位 180／180 和不同
循环系数旧扫描 180／180 C/Asm/Clight 验收通过。稳定参数系数的覆盖目前有
域定理与 closed computation，尚无相应新 native 案例。四模块 521 行不是
作者时间；新服务客户端 114 行与共享适配器 166 行分别记录。新的独立完整成本 810 batches 通过全输出检查；接受路径仍为 source 的
7.52／17.01 倍，cap／child-empty 的回归保留。不能据检查数下降或相对
旧服务的节省推断盈利。现有 cap 可配置；大 profile／一般 affine
源与完整 OLO 能力继续属于 goal。

2026-10-08 [去重 scan 服务](deduplicated-alias-scan-service.md)落实第三算法
的责任分工：domain 生产严格模板成员保持／Boolean 规范精确；language
adapter 证明剩余 source-licensed 读取、actual execution、memory／public／
ports frame；原 typed allocator 和 builder 自动构造证书。Common factory、
loaded guarantee／requirement 和 compiler 定理继续消费同一接口，Csem→Asm
专门端点一行实例化，没有复制安装证明或更改 kernel／host。

三模块 308 行，11 端点／7 closed，保持旧 42 globals、零新增公理。
正常 1,000／1,000 和非 uniform 180／180 native／Clight 全输出通过。
工作诊断与 linked bytes 独立验收，完整 CPU 2,430 batches 的接受成本仍
为 source 的 5.37–5.62／11.96–14.54 倍；相对原 canonical 有降低，同时
保留回退的回归。不能将类型化接口或 test-count 降低当作已证明的作者
时间／收益结论。完成执行仍是
scan 的前提，progress／placement／context installation 留在语言 host。
完整 OLO／一般 affine 功能继续在 goal；此为同 host 的第三服务实例。

以下保留前阶段当时范围。

2026-10-08 [Source-licensed scan services](source-licensed-scan-services.md)把
实际 Clight 执行、source/read/caller frame 和 accepted entry fact 固定为
语言接口，不把旧 Boolean equality 强加给未来充分条件。Domain 在此实例
给 layout／restricted nonalias fact 和原 C_opt checker；两个 service
authors 的 source/setup→许可／执行／充分性证明由 checked builders 构造。
Common factory 不展开 scanner semantics，就完成 candidate/fallback/public
exit；同一 loaded contract／selected compiler 在两实例上复用。

完整 factory computation 等式核对冻结 pair／canonical 前驱；19 端点、
1,414 绑定、旧 42-global baseline、零新增公理。提取 compiler 两策略各
通过 1,000 Asm／1,000 Clight 全输出矩阵。已证明 builder 与普通不受信任
source/candidate data 区分；driver 只能选已注册的两实现，未开放任意 OCaml
semantic callback。Source progress／context installation 留在原 host。
这是同 host 两算法的复用；不同 host 的 clauses／entailment 未实现。
下一项用第三个廉价条件服务检验实际作者负担和完整成本。完整 goal 保持。

本次重读 narrative 后，第三个服务的验收进一步固定在
[当前计划](current-work-plan.md)：新增 domain／language 的检查证明和
checked builder，复用 common factory、loaded contract 及 Csem→Asm
端点。`source_licensed_scan.licensed_scan_execution` 消费 source 的完成
执行、ready 和 ports agreement；它不生产 source progress、placement 或
installation 证明。其 accepted fact 是充分条件，不要求所有服务保留旧
Boolean 或接受域。实际源码用户与新服务作者的义务、复用端点、接受域和
完整成本分别记录；本次没有新增证明／运行结果。

以下保留前阶段当时范围。

2026-10-08 [Canonical 完整 compiler](canonical-alias-compiler.md)落实了上一
encoder 的内部义务：checked allocator 自动给四向量 typed/fresh resources，
原 setup/source 自动给 ranges/receipts；eligible／old 两实际扫描都返回原
alias Boolean。新 actual exit 复用原 candidate-at-exit／source-at-exit／
公开恢复，生产原 projected guarantee，再由原 selected host 安装。
七模块 23 端点、10 closed、1,410 绑定、旧 42-global baseline、无新增公理。
相同 1,000／1,000 native/Clight 全输出矩阵，以及不同 maps 的 180／180
旧 scan 实际安装通过。新 Csem→Asm 入口已提取；源码 callback 未新增。

这次复用没有改变 kernel、candidate checker 或 host contract。额外 scan
资源仍是语言／factory 的责任：二维九 slots 相对旧五 slots，可能改变
有限 pool 的安装接受域。安全与 Boolean exactness 的证明不能代替
[完整调用成本](canonical-alias-complete-cost.md)：新 2,430 batches 全输出
保持，2×3／8×8 接受为 source 的 6.34–7.24／14.29–20.17 倍；相对 memo
明显降低但全部输入仍慢于 source，观测 regression 保留。成本也不能代替
一般 affine 功能和完整 OLO 接受域。继续实现可复用的条件服务并测作者负担；不把复制
七个接线模块本身当作抽象接口已经足够轻的证据。Clause factoring 保持
实际 host 复用驱动的设计问题。完整 goal 保持。

以下保留前阶段当时范围。

2026-10-08 [实际 canonical scanner](canonical-alias-scanner.md)关闭 language
encoder 的 bounds/coordinates/pointer tests/flag 执行义务，保留 memory 和
公开 frame；14 端点、4 closed、最多 6 旧 globals、692 绑定、零新增公理。
Domain specification 与 kernel/candidate/host 不变；新 factory 必须自动从
原 setup 生产 ranges/receipts、fresh typed resources，运输 actual exit 并
接原 guarantee/installation。当前没有新 compiler/native/cost，低层执行
定理的前提不替代 producer 接线。完整 goal 保持。

以下保留前阶段当时范围。

2026-10-08 [Canonical alias 域服务](canonical-alias-condition.md)已生产严格
uniform-template eligibility、差值域 coverage、实际 CompCert modular pointer
alias 判断的精确对应和 accepted→原 restricted nonalias。20 端点无新增公理，
source-model 许可由原 source execution 推出，不要求 caller resolve callback。
这是 domain guarantee；Clight scanner 的 safe actual execution、private/public
transport 和 factory 安装仍未交付。下一步必须接这条真实执行链，沿用原
header/setup/candidate/host，不能用 Boolean spec 替代 encoder 或 native/cost。
kernel API 保持；支持族源码用户仍给 marked C/策略。完整 goal 保持。

以下保留前阶段当时范围。

2026-10-08 [完整调用成本](word-nested-store-complete-cost.md)记录 2,430 个
未插桩 assembly batches 的配对结果和全部完整输出验证。Readonly probe
服务减少 setup，但新版本在普通接受输入上仍为 source 的 11.45–11.61 倍，
cap 输入为 186.58–226.66 倍；部分 fallback 也有 regression。不能把局部
test-count 定理或 code size 当作完整成本收益。

下一最难位置是便宜而安全的 alias 前提编码：domain 库须证明 checked
canonical point pairs 覆盖当前所有访问对、actual address correspondence 和
accepted→restricted nonalias；Clight 服务须从原源许可 canonical 比较，
证明机器循环/算术、flag/fresh cursor、actual-exit/public transport。Factory
自动产生资源、scope 和新 region guarantee，复用 candidate/host。Kernel
不知 pointer/affine 语义，源码用户不补 hidden same-block 或 execution callback。
差值扫描只是待证明设计；没有当前实现或复杂度结论。语言 pointer ordering
的定义性边界保持。完整 OLO/一般 affine 功能与作者负担仍在 active goal。

以下保留前阶段当时范围。

2026-10-08 [Narrative 对照](narrative-kernel-host-review-2026-10-08.md)按当前代码
区分 kernel 的局部组合、语言的安装定理和 domain/site 的 guarantee/placement。
Finite projected contract 与 open protocol 共享 temp/memory 关系，但 progress
分别是有限完成和逐步模拟。出口 TempAgree weakening 本身不证明含入口/scope
的完整 contract entailment；clauses 的依赖与方向需另证。Clause algebra 未实现。

[Readonly probe 后继](word-nested-store-probe-memo.md)检验可复用服务：Clight
expression equality/readonly determinacy 许可路径事实，服务证明精确结果和
test 工作不增加；domain 沿用原 setup 充分性/candidate 对应，factory 运输
新的 actual execution 到原类 projected guarantee，language host 沿用原
scope/progress/placement/private/backend 定理。没有语义 callback 或新 kernel。
18 端点无新增公理，1,000 Asm/1,000 Clight outputs/paths 保持；额外配对
Clight setup 6,564→3,228，普通函数 1,442→1,344 bytes。计数不是 CPU 收益。

下一最难位置仍是可用的紧凑 entry condition 与完整成本：当前 header/alias
扫描和 cap 8 未改，不能用 setup 的节省掩盖这些成本。安全、充分性、actual
exit/public transport 分别由语言/domain 服务生产；候选/host 继续复用。
General affine source/scalar、OLO 功能/接受域/作者负担继续在完整 goal。

以下保留前阶段当时范围。

2026-10-08 [双 loaded shared setup](word-nested-store-shared-setup.md)展示实际
证明复用：domain factory 保持原 condition/C_opt，仅选择 checked typed flag
并组合既有 check-plan/private/public transport；语言 host 继续处理原源
progress、scope、placement 和 backend。没有源码 callback 或新 kernel/host。
11 端点无新增公理，同一 1,000 Asm/1,000 Clight outputs/paths 保持；普通
2×3 的 linked function bytes 2,750→1,442、root-source copies 36→4。
尺寸变化不能替代动态 guard 工作和完整成本。

下一最难位置是条件 residualization 与语言可表达性：前缀事实只能消除
已被安全读取且仍有效的 probe，不能提前读取未定义 child/RHS。通用
pointer-order interval 在不同 CompCert block 上可能无定义；共同基址的
现有 envelope 可复用，其他条件必须补语言 primitive/共同对象等可证明
evidence，不能把这项责任变成源码作者的静默假定。Kernel 消费证书，语言
负责安全/运输，domain 负责充分性与 model/candidate 对应；guarantee/
requirement clause algebra 保持开放。实际 compiler/接受域/guard 工作/
完整配对成本、一般 affine source 和 OLO 可用性仍继续验收。

以下保留前阶段当时范围。

2026-10-08 [双 loaded 实际 C 流水线](word-nested-store-native-pipeline.md)复用
前一完整 domain guarantee、candidate checker 与语言 selected host，新增
proved administrative normalization 以适配真实 frontend；语言 host 仍
检查原 AST 的 progress/placement/freshness。普通数据 proposer 自动从
marked C 生成 metadata；真实 rank-2 Pluto/codegen 只提出 Loop，完整 checker
负责最终有效性。Kernel/host contract 无变化，没有源码 semantic callback。
新 7 端点审计保持旧 globals；1,000 Asm/1,000 独立 Clight 调用覆盖真实候选、
两层 fallback、条件读取、重复 region 和 continuation。此为两轴 loaded
矩形源族的安装证据，不是一般域或高性能证据。

下一最难位置转到紧凑充分条件：domain 从原源观察/足够条件构造 entry
condition；language 证明其安全及 actual guard-exit/public 运输；kernel
继续消费证书；既有 candidate/host 定理继续连接局部与全局。分别验收
条件接受域、guard 工作、代码增长、完整成本/收益和作者负担，以 OLO 2017
功能讨论能力为约束。不能为缩短检查而偷读 source 未许可的 child/RHS，
也不能靠证明 guard 恒拒绝声称优化可用。当前 scan/cap/fallback 仍保守。
Fetched narrative 仍为 `12419c1` 且正文一致；guarantee/requirement clause
algebra 未擅自实现。一般参数化 affine source/scalar 保持在 active goal。

以下保留前阶段当时范围。

2026-10-08 [双 loaded 候选与整程序证明](word-nested-store-affine-compiler.md)将
domain 的原源→cached/model→实际候选对应接成 region guarantee，再由语言
host 检查原源 progress、scope、typed declarations、placement 和 context
requirement，导出 Csem→Asm。Kernel 不增加语言或 polyhedral 知识。实际
header-guard 出口许可内层候选；空域直接绕开其参数准备，两层 refusal 分别
运行原 loaded 或已证明对应的 cached source。14 端点／6 闭合／1,380 绑定，
保持旧 42-global baseline，零新增公理。源码用户 semantic callback 未新增。

下一最难位置是证明入口与真实 C 流水线的一致接线：自动 metadata、规范化
wrapper/reset/loaded expression、两轴真实 Pluto/prepared codegen、提取后的
compiler installation 与 native 空域/接受/回退/context。已量化 proposer 的
整程序定理不代替这些运行证据，旧 temp-bound native 不自动覆盖新族。
Narrative fetch 仍为 `12419c1`，kernel 的局部截止和 host 的 guarantee/
requirement 边界保持；clause algebra 不冒充已实现接口。支持族作者不手填
语义证明，新语言/domain 作者仍负责新增证明。Compact/OLO 的条件安全、
充分性、运输、接受域及完整成本仍约束 active goal。

以下保留前阶段当时范围。

2026-10-08 [双 loaded data factory](word-nested-store-data-factory.md)落实三方
责任的可计算入口：语言 typed allocator/scope/rename/progress 定律由数据
checker 实例化，domain 提案经实际 source/body/model 检查生产内部 package，
完整 header rewrite 定理自动消费其静态证据。34 端点／29 闭合／最多 6 项
旧 globals／1,280 绑定，零新增公理。Kernel、host contract 未改；源码用户
不提供 execution 或 simulation callback。

下一最难连接仍是接受入口的部分状态到真实候选：空域缺失 child cache
须跳过准备，活跃接受将实际 guard-exit cached execution 接完整候选服务，
两层 fallback/public transport 后导出 region guarantee。语言 host 提供
context requirement、placement、scope、declarations 和安装 simulation；
factory 的原源 progress 不单独代表整程序正确性。该族自动 C metadata
frontend、selected compiler/native 和成本仍待完成，不能以数据例冒充已接
完整 optimizer。Narrative 可见 `12419c1` 内容与 main 相同，guarantee/requirement
clause 化仍开放；compact/OLO 完整验收继续约束 active goal。

以下保留前阶段当时范围。

2026-10-08 [完整 nested loaded guard/rewrite](word-store-nested-guard.md)从原 source
执行生产 conditional captures/gates，关闭前一双方 ready 的入口假定。语言
服务证明 outer 空域不读取 child/cache/数组、安全联合 scan、实际 cached
出口和原 AST fallback 的 frame；domain 用原 prefix 与接受生产缓存对应。
两模块／20 端点独立审计保持旧 globals，无新增公理、kernel 或 host contract。

下一困难连接是接受入口的部分状态：空域可以缺少 child cache，候选准备
必须同样跳过缺失参数；活跃接受再运输缓存/dimension/scalar 到 source/model
与真实 candidate。Factory/site 须生产原 loaded AST 的 progress、typed pool、
scope、guarantee 与 placement，不能用 cached AST 的 progress 冒充原源证据。
现有递归 source factory 和已连接 polyhedral pipeline 可复用，但本阶段没有
新的 selected compiler/C→Asm/native/cost。源码用户不补 semantic callback，
region guarantee/context requirement 和紧凑条件/OLO 完整验收仍约束 active goal。

以下保留前阶段当时范围。

2026-10-08 [双 loaded axis 的联合 scan/cached 出口](word-store-nested-scan.md)
把三方责任推进到实际 nested source：语言服务提供当前原 store 的许可、
joint-header 地址检查、安全双短路 loop、memory/live frame 与实际出口运输；
domain 通过当前点/行接受推进原 prefix，全部接受后导出 cached nest 执行。
入口锚定 header-law 的 successor 复用原 receipt/advance，不增加 kernel
语义知识。源码用户 callback API 未新增；新族自动 factory 尚待接线。

下一最难位置是 conditional capture/gates：outer 不活跃时不能读取未定义
child header。当前 theorem 要求两份已捕获 ready，不由这个前提代替 producer。
随后生产 source/model/candidate 对应、region guarantee 和 placement/resource
evidence；语言 host 的 progress/boundary/installation 负责整程序连接。公共
边界随 site/context 而定；guarantee/requirement 分解与 clause algebra 仍开放。
本次 narrative fetch 仍为 `12419c1`，正文与 main 一致；没有新增 native、
完整 loaded compiler 或成本结论。实际 polyhedral pipeline、紧凑条件和 OLO
完整成本/功能/可用性验收继续约束 active goal。

以下保留前阶段当时范围。

2026-10-08 [完整原源许可 guard 与 cached 分派](word-store-sequence-scan.md)
让三方责任落到真实执行：Clight 服务提供 capture 的第一次读取许可、地址
temp 的运输、gate／短路 cursor 执行、memory/public frame 和实际出口运输；
domain 以原 loaded source prefix 生产逐点 domain，接受后保持 header、覆盖
整个单轴 cached 域并产出 cached execution。完整 cached/original dispatch
已有局部正常执行定理，源码用户不提供 SOURCE／simulation callback。Kernel
及既有 host contract 不改；当前仍是语言/domain 库，scope／rename／私有 typed
资源的自动生产和安装尚须接 data factory。35 端点的审计保持旧 42-global
基线，无新增公理；真实空域与第二 store/header alias 证明不等于新增 native。

下一最难位置由一条 axis 转为完整 loaded nest 的多 header／条件读取：先前
接受的 writes 必须许可下一源码 test，并在全接受时建立原源→cached/model→
actual candidate 的对应。随后分别生产 region guarantee 与 placement/resource
evidence，由语言 host 提供 progress／boundary／whole-program installation。
Guarantee/requirement clause 化仍是开放设计。Narrative fetch 仍为 `12419c1`；
真实 polyhedral 集成、紧凑充分条件与 OLO 完整成本/可用性验收继续约束 goal。

以下保留前阶段当时范围。

2026-10-08 [Store-sequence loaded prefix](word-store-sequence-prefix.md)保持
kernel／语言／domain 的三方边界：框架消费 readonly certificate；语言服务
组合实际逐条 store receipts、word 地址／permission 运输、安全 pointer
comparison 与 flag 执行；domain 将原 loaded source prefix 接成逐点 domain，
接受后保持 header 并推进后继读取。AST checker 生产语言静态 body 义务。
后续 RHS 在真实中间内存求值，权限回运不能替代值保持；cached-source 执行
不作为该检查的许可前提。单一 axis 的 prefix 不自动给出完整 nest 或全局
等价，kernel 和已有 host contract 未改。

下一最难连接是完整原 loaded nest 的多 header／条件读取、全接受的 cached
对应及实际检查出口运输，再由同族 factory 生产 typed resources／scope／
region guarantee，消费已有 candidate／selected host 和真实 polyhedral
pipeline。支持族的源码用户仍应只提供 marked C／数据；当前库参数不冒充
已经交付的自动 loaded factory。紧凑条件、安全／充分性／运输、接受域与
完整成本继续单独验收。[本次 narrative 对照](narrative-store-sequence-review-2026-10-08.md)
远端仍为 `12419c1`，正文无新差异；未读取未推送内容，也未把 context
contract clauses 的开放讨论当成已实现 API。

以下保留前阶段当时范围。

2026-10-08 [多数组实际 C 流水线](multi-array-affine-native-pipeline.md)复用已证明
data factory 和 selected compiler，接自动 source metadata／真实 Pluto／
prepared codegen。优化 policy 只提出数据，完整 checker 提供条件下的实际
source/candidate 对应；语言 host 负责 frame、progress、scope、fresh declarations、
occurrence installation 和完整 simulation，kernel 仍止于局部证书组合。源码
用户只给标注 C／选项。768 Asm／768 独立 Clight 调用、五实际安装 sites／配置、
两层回退／重复 region／continuation 已验收。这里的正确性由前一量化定理覆盖，
并非 native producer 自带语义 callback 或新的通用 context lifting。

Narrative 复核仍为 `12419c1`，正文无新差异。接下来最困难的是 loaded 两-store
原源每条 store 的 header 值保持与后继读取许可；source permissions 不能替代
值保持，也不能用未建立的 cached 完整执行许可其生产。紧凑条件替换需要语言
安全／实际出口运输、domain 充分性，并复用适用 candidate／host 证明；code size、
runtime work、接受域和完整成本分别验收。这个 temp-bound slice 已闭合，完整
OLO 能力及一般 affine source 目标保持；本次没有成本或收益证据。

下文保留各前置阶段当时的证明／实验边界。

2026-10-08 [泛化 versioned compiler](multi-array-affine-versioned-compiler.md)关闭
actual scan exit 到 source/setup/restricted locator、candidate／restore／原 AST
fallback 的连接。Domain data factory 消费既有候选 checker 并生产 projected
guarantee；Clight language host 负责 source progress、private declarations、
occurrence-sensitive placement、context simulation 与 Csem→Asm。Kernel 和
既有 host contract 未改。**新的整程序定理不能代替此族的实际 C 驱动安装与
运行验收；下一项直接接 marked C／自动 metadata／真实 polyhedral codegen。**
两-store loaded 原源的逐步观察保持与下一读取许可仍是最困难的语义连接，
不能以 cached-source 完成执行许可该缓存的生产。Scalar gate、general domains、
紧凑条件／cost 和 OLO 可用性保持 active。本次 narrative 仍为 `12419c1`，
两正文无新差异；没有按文档边界新增 kernel API 或通用 context lifting。

2026-10-08 [实际 affine access scan](multi-array-affine-access-scan.md)区分语言
的地址编码／原源 permission transport／循环执行／public frame，与 domain
的实际模板／coverage／接受充分性。同一 package／typed allocation 生产
检查许可，无源码用户 semantic callback 或入口 NonAlias。Kernel／host
定义保持；最难的下一连接是 original locator／source/model 到 actual scan
exit，接候选、公开恢复、projected guarantee 与 selected installation。
**泛化扫描未新增 compiler／native／cost；coordinate-only scalar 仍是保守
拒绝边界，loaded header 与原源 prefix 保持尚未闭合。**Narrative `12419c1`
与 main 两正文一致，其三方责任继续作为工作计划约束。

2026-10-08 [数据 source factory](multi-array-data-factory.md)从实际 AST 和普通
assignment metadata 生产 static source／shape／freshness／progress 与 checked
box，接完整 setup 和实际源模型；typed allocator 生产 private declarations
成员／freshness 及实际 scan AST 的 frame。Kernel、host 定义保持。最难的下一
连接是用同一 package 的原源执行许可泛化 scan，证明 coverage／接受充分性，
运输到真实出口并接 candidate／restore 与 selected installation。**Source
progress 或 typed slots 各自已生产，不代表原固定名 guarded statement 已泛化
安装；不向源码用户索要 model 或 simulation callback。**旧两-statement
proposer 的错误分类只导致安全 refusal，新 factory 独立检查 reset／child。

2026-10-08 [任意 caller 边界](multi-array-public-boundary.md)落实 narrative 的
region guarantee／context requirement 区分：语言提供实际写集、frame、执行
运输与现有 small-step bridge；domain 接完整条件／checked candidate／restore；
新 producer 静态检查 private/live 冲突并导出既有 projected region contract。
Kernel 没有变化，也没有另建 contract algebra。**下一困难位置是 factory 从
源数据和 typed pool 生产 allocation／progress／placement，然后完成该族的
selected 安装；loaded 两次 store 的 header 保持仍需原源 prefix 证据。**
任意 caller-live 证明已闭合，source／private names 仍固定；不把局部保证称作
整程序优化，也不让源码使用者补缺失的 semantic callback。

以下记录保留各阶段当时范围；当前最先验收的安装责任见上段。

2026-10-08 [两数组完整 condition](multi-array-complete-guard.md)将语言 source
definedness／short-circuit／checked arithmetic 与 domain 的多访问 coverage／
profile 推导接上，复用 framework 的 `readonly_condition_entails` 暴露数学 setup
前提；kernel 不变。完整局部 statement 不再要求入口 caller 假定 numeric／
layout／box／profile 或 NonAlias。**下一最难连接是固定 ports 到任意 program-live
temps 的 frame、fresh typed factory／progress／placement，以及 loaded 原源中两
store 的 header 保持；由 factory 生产 region guarantee 后才消费 selected host。**
当前构造器只返回 local statement，不提供新 whole-program 或成本结论。

2026-10-08 [actual scan-exit 连接](multi-array-scan-exit.md)将语言 dimension／
restricted locator／source execution frame 与 domain 的 checked candidate／
restore 接在同一实际检查出口。Alias 接受从扫描生产 separation，拒绝执行
原 AST；两条分支保持原 final memory 和所请求的公开出口。11 端点独立审计
通过，无新增公理、kernel 或 host contract。**下一难点移到完整 setup condition
生产、typed data factory 及 loaded 原源中两条 store 对全部 header 的 prefix
保持，最后将该同族 region guarantee 交给已有 selected host。**该局部 alias
choice 定理仍显式要求 numeric／layout／box／profile，尚未证明这些拒绝路径的
完整 guard；新多数组整程序能力和成本未完成。再次核对 narrative `12419c1`
正文与 main 一致，kernel／语言／domain 的三方责任保持。

2026-10-08 [静态 runtime pair scan](multi-array-runtime-pair-scan.md)将语言双矩形
循环／public frame／实际 tensor 指针比较，与 domain 的 checked 两数组 footprint
及原源访问许可接上。15 端点独立审计通过，无新增公理或 kernel 改动。同一逻辑
数组内的不同坐标由 layout injectivity 分离，跨数组由接受比较分离，同一 cell 的
有意依赖不被要求分离。**下一难点仍是 entry→actual scan exit 的模型／locator
运输和候选执行，以及两条 store 的 loaded-header prefix 保持；随后由 factory
提供语言 host 所消费的 region／site 证据。**该扫描只覆盖 canonical temp-bound
源，不以它的完整 footprint 许可尚未证明 cached 对应的 loaded 原源；整程序新
安装和成本仍未完成。

当前责任边界以 [narrative 源码对齐复核](topdown/implementation-alignment-2026-10-07.md)
为准：generic context record 消费 host 的 lifting 定律，实际 Clight 安装另证明
progress／scope／freshness 与出口关系。下一多数组 guard 须静态生成 AST，从原源
许可证明安全，以接受证明动态 coverage／充分性，并运输到实际检查出口；这些
由语言库与 domain producer 分担，不交给源码使用者补语义 callback。Exact／
projected／open host 已共享部分 state/memory 条款，但 progress 协议确实不同，
尚无证据要求重构 kernel 或引入自由组合的 contract algebra。以下保持各阶段记录。

2026-10-07 [多数组源许可](multi-array-source-permissions.md)将语言 observation／permission 定律与 domain source family 接上：实际 first leaf 许可 used pointers、几何 suffix 和 RHS 参数，trace 上的每次 load／store 提供读写访问并通过前序 stores 回运 entry；tensor address encoder 消费它们取得已有 Clight 比较 primitive 的地址证书。具体分配／初始化 witness 证明入口可有权限但值为 Vundef，不能用 permission transport 前移 RHS 计算。32 端点审计通过，10 闭合、最多 6 项旧 globals，无新增公理。Kernel、host 与 compiler theorem 均未改。**仍最难的是 source-prefix progression 和静态 guard 生成：reference footprint 是入口依赖的语义 witness，必须由 runtime scan／symbolic envelope 证明覆盖；loaded 源必须逐次建立两条 store 对 header 的保持，才能把原源转换成 cached rectangle，不能以该转换尚未证明的执行许可自身。**该 domain 证据随后组成 region guarantee 交给语言 host。

2026-10-07 [完整多数组 tensor 源循环后继](multi-array-tensor-source.md)落实了逐点 temps 与固定 entry location view 的局部连接，并从真实 counted Clight nest 推导原 Loop、实际候选执行和公开 iterator exit 恢复。语言 memory 库的 location/action/sequence frame 只要求实际 write/read cells 一致；domain 的 pointer-set checker 和 coordinate box 提供相应具体条件。Counter reset 可以改变无关 raw entries，不需要整份 view 相等。前一 [body/candidate 桥](multi-array-tensor-body.md)仍保留实际 alias 和逐条中间内存，domain 只在 actual source footprint 上消费 NonAlias。Kernel 与 selected host 未变。**最难的后继仍是 factory 从原源许可生成 availability 和安全 cross-array alias condition，逐次保持所有 captured header，运输到 actual guard exit，再将 region guarantee 交给 host 安装。**写入后才定义的读取不能直接前移到 entry guard；权限许可与值定义性／forwarding 是不同语言定律。新局部定理的显式 semantic 前提尚未由完整 guard 生产，不能称为已安装的 multi-array guarded compiler，也不能交给源码用户填写。Host contract clauses 仍是开放设计问题。

2026-10-07 [单位坐标／positive-offset 后继](unit-tile-and-positive-offset.md)继续复用 responsibility boundary：producer 提出 singleton／operand completion 或 mapped reindex，既有 domain factory 验证实际 candidate；language 提供实际 capture receipt 与 word-add presumption 定律、许可／状态运输及原有 host。完整单位矩阵 2,352 Asm／1,792 Clight、八种 probe 安装及 `+1` 的 1,215 Asm／540 Clight 检查已通过。五整数端点闭合，三 receipt 端点使用四项既有 globals；未新增 kernel、caller callback、runtime encoder 或 compiler theorem。下一最难连接是同一 loaded/Horner 路径的多 operation、多 array、真实跨迭代依赖，以及每次读取／写入的 source-prefix 许可与 guard-entry 模型连接；其他路径已有服务不能合称当前支持。

2026-10-07 [tight-candidate 后继](tight-loaded-word-candidates.md)展示了责任分层的实际复用：优化实现只改 untrusted bound／guard proposal，既有 domain factory 重检 actual Loop，语言 host 仍提供 placement／progress／frames／Csem→Asm。同一 compiler theorem 已量化 proposer；没有新 kernel／Rocq 模块或语义 callback。784 Asm／336 Clight 检查通过，unit tiles 的中间成功没有绕过最终 shape gate。配对成本和实际 Ir 分别验证候选枚举问题及改进，但不宣称 source 收益，也不将机器指令数当 CPU cycles。

2026-10-07 [zero条件的完整安装](zero-loaded-word-installation.md)已接原源首点许可→actual receipt值保持→cached／helper／canonical及完整check出口→actual candidate→local contract→selected Csem→Asm。`tensor_preparation_certificate`是语言层内部服务，data factory生产其字段，优化使用者仍只提供描述／scalar／模型与候选数据。Kernel不负责词或指针安全，也不因此获得任意contextual closure；host继续独立检查progress、placement与fresh allocation。21端点保持42-global基线；560 Asm与224独立Clight分派通过，零值alias接受域扩大。下一难点是nonzero条件的安全观察许可、候选完整成本和收益策略；word观测保持不冒充byte／other-chunk／whole-memory equality。

2026-10-07 [新的值保持condition与成本](loaded-word-condition-cost.md)将三方责任具体化：框架继续消费readonly_condition；Clight语言提供成功原RMW的scalar许可、checked控制／word观测保持及纯条件编码；domain仍需生产其accepted-state到cached／canonical执行的推导，host在收到local contract后才负责安装。局部C_encode不升级为compiler证书。已安装旧路径的720配对成本暴露明显退化；不得从guard work计数归因全部退化，仍须改进候选lowering和profitability策略。

2026-10-07 [loaded-word factory](loaded-word-family-factory.md)已把原先语言／domain定理的静态字段变成AST、WORD、scope、freshness、typed-pool和canonical model的数据检查输出，actual candidate checker后生产局部保证，并消费现有selected host接Csem→Asm。前端行政skip和零index由语言服务证明；框架kernel保持。使用者提供标注和策略，不手填semantic callbacks。通用编译器定理与具体native producer成功由不同证据绑定：v3已验收真实调度／分块、动态接受／回退与完整上下文，420未插桩Asm及168独立Clight分派通过。下一难点是同族compact condition的安全与编码证明、接受域和实际guard／整程序成本；非端点数。

2026-10-07 [loaded word driver](tensor-loaded-word-driver.md)已将语言capture、
receipt／helper frame、完整scan和Boolean materialization，与domain canonical
tensor／完整numeric-layout guard／实际候选checker连接起来；候选从真实完整
check出口执行。新的具体Clight局部region保证可供语言host消费；最小kernel和
原source AST fallback保持，无新增公理。它尚不是新的materialized kernel-rule
package或loaded编译器入口。最难后继变为factory从实际AST／typed pool生产
静态资源和canonical package／accepted-entry证据，再消费已有progress／placement
安装定理，并验收同一loaded／runtime-Horner C到Asm。源码使用者不应手填这些
语义字段；语言／domain实现者和checker承担责任。当前无新native或成本结论。

2026-10-07 [完整word outer扫描](tensor-word-outer.md)已由语言服务完成全nested
检查和实际scan出口的cached执行运输。Domain header adapter从actual capture
receipt推导两header求值、cache定义性和observer scope，生成语法只用静态地址
templates；fixture不再提供这组语义callback。41端点独立审计通过，无新增公理，
kernel保持。下一困难是条件式capture／profile接线、canonical tensor／完整guard
出口参数和真实候选／public exit，再由family factory交付local与site证据接安装。
这些不是kernel自动取得的性质；当前仍无新增loaded compiler／C／Asm／cost。

2026-10-07 [本次narrative责任核对](narrative-responsibility-check-2026-10-07.md)
明确 `C_host` 的局部choice定律与整程序安装是不同证明；最小kernel、语言库、
domain实例及具体site的证据生产责任分别记录。当前实际tiling路径已接通，
loaded／dynamic组合的已审计成果到完整column／component及current-row step；
outer草稿尚未计入交付。最难后继仍是原源许可的完整prefix链、cached/model到
actual guard-exit的运输，以及family factory消费真实候选并接安装。以下各段保留
当时的责任与验收范围，不将早期“scheduler未连接”当作当前流水线状态。

2026-10-07 [selected-region后继](selected-polyhedral-regions.md)实现了位置身份
问题：语言host在chosen label下才允许selector改写，证明未选子树保持及完整
小步／Csem→Asm连接；native frontend负责pragma配对、fresh名字与manifest运输，
属于既有parser／Csyntax信任边界，annotation仍不是语义证书。Domain复用原tensor
模型／guard／candidate checker，尚未接实际scheduler与prepared codegen。13端点
审计及648汇编／216Clight／14frontend cases通过；kernel保持，没有新site语义
callback。Shared host simulation目前保留单独实例，未声称减少证明代码／作者工时。
最难下一项是生成Loop的实际执行／progress与checked entry连接，不只调用一个
Opt_prepared端点；实际OpenScop exporter也须补齐。

2026-10-07 narrative `12419c1` [最新接入复核](narrative-pipeline-review-2026-10-07.md)
将annotated real polyhedral pipeline列为下一集成项。Kernel继续只组合局部
证书；语言／frontend保留标注site身份、核对实际AST与合法边界、提供安装定律；
domain实例化条件提取、真实scheduler／phase验证／codegen及生成候选的执行桥。
使用者标注源码并给phase／tile选项，annotation不提供语义前提，不要求手写
target Loop。关键缺口是原源许可→模型假设→生成Loop→actual guard-exit入口和
public exit／progress的连接，以及防止按AST相等的安装误改同形未标注site。
当前native仍是直接Loop候选提案＋真实提取／验证，尚未调用完整流水线。

2026-10-07 当前：[word component scan](word-component-scan.md)把首点推进为
完整literal第三层。语言提供exact word重命名／求值、实际pointer check／private
loop及cached transport定律；domain将原源prefix、source/scan坐标frame、capture
receipts接成逐点domain，接受后生产观察保持并推进真实源，完整接受才导出cached
source。Kernel未变，whole-program安装继续属于语言host与具体site保证；新family
的data factory／全inner-outer覆盖／模型候选与入口运输仍待接通。
40端点独立审计和actual五store／scan fixtures已通过。
[Narrative澄清复核](narrative-review-2026-10-07.md)将这些责任与证明优先顺序纳入
当前计划；紧凑条件仍须分别证明安全、接受所需义务和入口运输，再复用C_opt／host。

2026-10-07 最新：[loaded tensor 首点服务](tensor-header-point.md)落实“检查
许可不能依赖待检查前提”：语言库在确切word语义下运输变量乘积，从实际store
取得guard-entry权限，并证明actual check及接受后的raw observation保持；domain
从原loaded source生产条件式capture、首点和同入口接线。40端点审计通过。
现有kernel／host均未修改，后继全循环prefix、cached model／candidate运输与
安装仍由domain／语言host承担。该family的新data factory尚未交付，theorem的
静态语法／freshness参数仍需checker生产；不把首点接口称完整data-only使用体验。

2026-10-07 最新：[literal-bound接入](tensor-literal-bound.md)按
[narrative逐项核对](narrative-literal-bound-check-2026-10-07.md)完成语言helper
初始化／public frame、domain source/model及checked-entry运输、materialized
kernel certificate和expression host／Csem→Asm。208端点审计、提取、1,152汇编／
432独立Clight调用通过；private helper不假设原入口定义，拒绝体是原literal AST。
使用者仍只提出数据，不填SOURCE／ENCODE／helper-word语义callback。三方责任
与四条逻辑链保持，kernel未变；新语言和domain服务是实际执行producer，不是
泛化框架自动得出的语义知识。Loaded bounds＋动态layout组合、最新入口成本和
比较作者工作尚待验收。以下保留各阶段当时边界。

2026-10-07 最新：[两种坐标次序](tensor-coordinate-order.md)已在相同Rocq proof
report下通过实际数据提案，不新增SOURCE／BOX／binding／exit callback。新原生
矩阵和[独立成本](tensor-coordinate-cost.md)证明这个具体接口使用及声明输入的
执行结果；不能作为任意source grammar或比较作者工时的完成证据。
下一literal-bound扩展的责任明确落在语言准备／私有frame、domain source/model
入口运输，以及实际expression-progress安装接线；不向kernel增加泛化规则，
也不让site作者用待证语义callback代替这些producer。

2026-10-07 当前：[tensor 责任清单](tensor-proof-ownership.md)逐项记录已有family
的一次使用与扩展family／首次语言host的差别。39新查询端点分为10语言服务、
14domain factory／rule、5compiler接线和10fixtures；源码LOC和endpoint counts
仅为复用清单，不是作者工时或相对其他framework的负担优势。
九字段metadata和candidate/witness经factory生产实际证据，没有每个site新增
SOURCE／BOX等语义callback；更广source／domain仍需新的对应和条件证明。
[实际成本](tensor-region-cost.md)独立验收guard work／bytes／完整调用，当前行
连续源的重排没有净收益；[OLO对照](olo-tensor-comparison.md)明确loaded／literal
与动态layout组合仍需交付。原kernel／语言host保持，完整目标active。

2026-10-07 当前：[tensor factory／compiler](tensor-region-compiler.md)已由实际 AST
数据核对生产静态 source、shape、namespace 和用值证据。Domain 复用 full guard、
真实源／候选／出口对应；新语言 readonly adapter 实际调用 kernel preservation，
语言 host 独立核对原源 progress、scope 与 typed private resources，连接 Csem→Asm。
前端行政 skip 的执行等价属于语言服务，无须修改 kernel 或候选证明。181端点
审计、216 assembly／108 Clight calls 通过。没有新增使用者 SOURCE／BOX／bindings
语义 callback；另一种 source class 仍由 domain 提供对应证明。
[Narrative 核对](narrative-implementation-check-2026-10-07.md)明确四条逻辑链并非
四份用户手填 record；finite completion 不替代 host progress，choice law 不替代
region 安装。下一项比较已闭合子集的条件成本、接受域和作者责任；更多 source／
alias／loaded stability 与完整 BT 继续按完整目标推进。以下保留前阶段边界。

2026-10-07 当前：[tensor 坐标条件](tensor-coordinate-guard.md)继续落实 narrative：
domain 条件库生成 affine extrema 并证明全部活动坐标覆盖；Clight 库交付实际
profile gate、signed32 安全算术和 readonly certificate。原源许可的 full guard
接受直接生产 BOX、bindings、pointer/dimension view，完整 candidate bridge
内部生产 Loop SOURCE 并复用原 checker／公开 iterator restoration。Framework
最小 kernel 保持。C_derive／C_guard 和局部 C_opt 已接通；新的 C_host 仍缺实际
region factory、progress、private resources／placement。优化方还需给 metadata
和源结构的静态证书，尚未由 data checker 自动生产。142 端点／13 项提取通过，
不执行生成 Clight，无新完整 C/native。最难位置已移到从输入 AST 生产局部证书
及全程序安装；不能用 finite-normal-completion D 代替 reachable-state progress。
详见 [checkpoint](research-checkpoint-2026-10-07-tensor-box.md)。

2026-10-07 当前：[动态 tensor backend](dynamic-tensor-backend.md)按 narrative 的
三方责任接通实际 lowering 与原 affine／tiling checker。语言库生产维度 word、
真实指令／循环执行和 protected temp frame；domain 消费布局 nonalias 及 verified
candidate certificate，交付候选实际执行，无新候选语义 callback。66 端点审计和
七项提取运行通过，最小 kernel 保持。四条链中 C_guard 的 D 明确要求维度已有
Vint，C_derive 仍缺实际原源读取许可／坐标覆盖，C_opt 的 source 端仍是 Loop
模型，新 C_host 安装未发生。最难的下一项是原 C 活动路径和 Horner 地址到模型
的 producer／entry transport，随后实际出口与 progress／placement；它们属于
语言／domain／site 责任。详见 [澄清吸收和验收顺序](research-checkpoint-2026-10-07-tensor-backend.md)。

2026-10-07 最新：[动态布局服务](dynamic-tensor-layout.md)继续按照 narrative 划分。
Domain 提供 mixed-radix 单射与布局到 footprint 的局部推导；Clight 库交付真实
word／division／pointer／load/store 及 readonly 检查定律；现有依赖契约消费物理
nonalias，kernel 和语言 host 未变。33 端点审计通过，没有新全程序编译能力。
原源读取许可／坐标覆盖／layout temp 保持、候选 lowering／公开出口和 placement
仍由实际 optimizer/site 接入生产。标准 condition 的 D 暂要求所有维度已定义；
单独的首维拒绝定理允许后续未初始化，不自动解决一般 source-derived D。
多维库不是 universal precondition inference，也没有 proof burden 收益证据。

2026-10-07 最新：[入口参数同值条件](nested-invariant-word.md)复核了 narrative
三方责任的实际含义。Clight 语言库证明 affine word 的纯求值/frame 和 actual
full-int32 store effect；domain 从原源 prepared/domain receipt 生产定义性与
同值 header 保持，连接原源到缓存模型和 guard-exit frame；实际比较交付 C_guard。
候选 C_opt、kernel、语言 installation host 复用。新 data-only factory 没有 value／
definedness／effect callback。35 端点审计、提取和新的 120 assembly／60 Clight calls
通过；没有定量作者工作比较、成本或新 machine probes。当前子集仍是 uniform
loop-invariant affine value，不是任意 effect 或普遍的条件推导。详见
[本轮 checkpoint](research-checkpoint-2026-10-07-nested-invariant.md)。

2026-10-07 后继：[五赋值公开出口](nested-compact-exit.md)连接当前 accepted
uniform nested 模型与实际 candidate 出口。语言库证明幂等 control BODY 的真实
循环执行及固定 temp patch 定律；domain 从 guard 接受／模型执行生产实际
int32 words、root 活跃和 child positive，证明精确 source exit 并运输 cache
frame。Memory candidate 验证及 lowering 定律复用，guard/kernel/host 不变。
这属于 C_opt 的执行对应，不是 C_guard 或 C_derive 的新条件。最难的位置是
“每层确实执行过”的来源与检查后入口 cache/public frame；不能一律将空循环
的 child counter 设为 upper。Checked factory 没有新增语义回调。42 端点审计、
实际数组／上下文矩阵和九个 machine probes 已通过。[配对成本](nested-compact-cost.md)
30 轮完成，同值 interchange 下降但仍慢于 source，非同值路径仍明显变慢；
guard 工作保持，不能把全部差值归为纯出口恢复成本。

2026-10-07 最新：[单份扫描](nested-stability-shared.md)沿原证书接口复用 candidate／
host。语言新服务只在两项均已初始化为 int32 Boolean words 时证明 eager `Oand`；
domain 从实际 cache bindings 建立其输入，失败不改变旧 scan 入口。它不属于最小
kernel，也不能用于仍依赖前项许可后项读取的条件。23 端点审计沿既有 baseline。
Word=15 的实际 C profile 自动消费相同 descriptor／checker，无新增使用者语义
回调；九个较大域汇编 probes 区分 source／交换／tiling。后继
[已知 word 的 numeric facts](nested-numeric-word-facts.md)由数据 checker 导出实际
numeric/domain 前提，四个新定理闭合，不扩大 kernel，不修改 runtime guard。
此前将 numeric 称作逐点成本有误；它是 first-path／参数区间检查。实际逐点工作
来自 stability／alias scans。完整成本验收和紧凑 footprint 条件应针对这些成本，
并保持实际 captures/helpers/model-entry 的许可和运输；作者责任比较仍待交付。

2026-10-07 最新：[source-only reproduction](nested-frontend-reproduction.md)已从
锁定源码重建既有 compiler／运行路径，独立基线查询替代历史报告输入；kernel
与证明责任划分不变。[constant-word observation](constant-word-observation.md)
由语言库证明 typed `Mem.store` 保持和 actual Clight BODY checker soundness。
这是 fixed-address memory guarantee，不能替代 pointer-binding frame、读许可、
prefix／model 对应或候选正确性。Domain 后继 [same-word producer](nested-word-model.md)
已生产实际 subloop 保持、cached source／canonical 模型和两次比较的 Clight check，
接受后明确模型入口到 actual check exit 的 ports frame。它复用旧 source-derived
capture／numeric／helper receipts；不是新的 kernel 功能。后继
[same-word compiler](nested-stability-compiler.md)已完成实际 physical guard、
multi adapter、typed factory 和完整 Csem→Asm entry。新 guard certificate 直接
消费原 `ncs_multi_local_certificate`，经原 kernel 和语言 host 安装；域实现承担
实际 source/model 及 model-entry→check-exit frame。19 端点／597 依赖独立审计、
提取、完整数组和四个真实汇编 alias 路径探针通过，没有新增使用者语义回调。
同输入 old/new 对照分别记录局部检查工作、接受和代码增长；完整 timing、
更广条件与作者工作量仍待验收。最困难的证明环节仍是安全 capture、实际模型
对应及入口运输，不能用两次 Boolean 比较替代。

2026-10-07 后继：[nested frontend BODY／contexts](nested-frontend-coverage.md)在
同一 compiler 上扩展了实际读写、dependence、重复 sites 与程序上下文验证。
更强 child-count∈[1,2) profile 使 chain 的重排被同一 checker 接受，runtime guard
在前提外保留原 AST。这个使用过程保持三方责任：优化方提出候选和 profile；
domain checker／producer 证明条件正确性及入口到模型义务的覆盖；语言库解释
安全 capture、检查、实际状态运输和 region 安装；kernel 消费既有证书。
三方是证明归属，四个 certificate links 是逻辑环节，不增加四份用户手填 record。

重新 fetch narrative `271f6fc` 后确认 main 正文一致。下一项紧凑条件工作必须
分别提交安全、accepts⇒所需义务和入口状态运输的证据，复用现有 C_opt／host；
整程序安装继续由语言实例与具体 region／site 证据共同完成。当前没有 generic
WP、最优 guard、任意 contract-clause 组合或第二 IR 实现；成本／作者负担待测。

以下为先前固定阶段；其后继待办以本段及最新 checkpoint 为准。

2026-10-07 最新实运行：[actual nested frontend](nested-frontend-native.md)已在既有
Figure 2 适配源实际安装并运行 interchange／tiling；zero-index root 和 prefixed
resets 的执行对应由语言库证明，fallback 保留原 AST。新 Csem→Asm entry 已提取；
75 full assembly calls、16 Clight dispatch calls 与 6 machine probes 单列并通过。
Kernel 未改，三方责任／四条证书链保持。下面旧阶段与原 16-call `not-supported`
报告固定保留其当时范围；当前能力以新 native 报告为准，仍无 compact 条件／
成本／完整 BT layout／作者工作验收，完整目标 active。

2026-10-07 最新后继：[nested guarded candidate／compiler](nested-constant-multi.md)
已连接实际 canonical source→alias guard→candidate→kernel preservation→projected region
contract→typed factory／语言 host→Csem→Asm。Model anchor 及实际 checked-entry frame
由执行 receipt 生产，没有 source/model 语义回调；kernel 不变。三层原 AST 的 host
progress 支持有 fixture。后文阶段记录保留当时边界；新入口的 extraction／实际 C
识别和非空数组非 identity 优化运行仍待验收，原 Figure 2 16-call report 不变。
Narrative 重新 fetch 到 `271f6fc`，正文与 main 一致；三方责任和四条证书链按新文档核对。

这是当前活动目标的一部分，按用户的补充要求维护。研究叙事沿用 `topdown/research-positioning` 的 [paper narrative](topdown/paper-narrative.md)，10 月 7 日重新 fetch 并读完 `271f6fc`，main 正文一致。该稿是方向；本文区分已经实现的设施、使用者还需提交的证明和后续验收。完整多面体目标仍未完成。

最新澄清已采纳：最小 semantic kernel 止于局部 guarded correctness；只读前台、条件组合、prefix scan、simplification 和 assumption derivation 是核上的库。完整程序安装属于 language/IR host，generic lifting record 只是组合入口。这里的“框架责任”包含可复用库，不等于这些服务全部属于最小 kernel。此边界不要求重排文件；只有真实 optimizer／host 暴露无法表达的语义义务时才考虑修改 kernel。

[当前源码核对](narrative-implementation-check-2026-10-06.md)已更新到 `fa8cbd8` 及本轮后继，
并记录 [实际 BODY joint scan](constant-body-joint-scan.md) 和 inner loop 的连接。语言库提供
observer expression receipts、真实 pointer comparison、private Boolean 积累和
store-load 保持；domain 从已到达的原 `<5` BODY 许可全部写地址比较，证明完整
子域覆盖和接受后保持所有 observations，填入 inner-prefix preservation／advance。
30 端点审计保持，kernel 不变。[Inner loop 后继](constant-joint-inner-scan.md)已将
检查 producer 接到真实短路循环，并从整行接受直接生产全 column 的 preservation
和 outer-prefix advance。固定入口的 header 定律足够，不要求任意无关入口的 cache
对应。[Outer 后继](constant-joint-outer-scan.md)现已接通真实扫描和全部 rows
preservation，导出同出口／memory 的整段双缓存源。14 端点／565 依赖审计保持，
无新增语义 BODY／PRESERVE 回调。[Canonical 后继](nested-constant-model.md)已证明实际三层
source transport 和 checked-package Loop 内存解码，静态 leaf/frame 输入在
该实例内部生产。[原源 numeric 后继](nested-constant-numeric.md)现已从首次实际
leaf 和 checked 参数使用生产定义性，运行 ordered capture／双 gate，接受后
生产逐点 DOMAIN／SOURCE_WORDS；新服务不要求调用者预设这些事实。
24 端点审计通过。[Checked entry 后继](nested-constant-site.md)已生产原 AST／
scope／namespace 的静态证据，并由实际检查接受生产当前入口的 observers 和
初始 prefix；两项具体 header 定律复用实际 raw receipts。代码对 observer ghost
fields 不敏感，有完整 AST 等式；入口 ROW0 通过 runtime gate 检查而非 context
语义前提。37 端点审计通过。[完整 physical guard 后继](nested-constant-physical.md)
已执行 helper 准备并填入全部 outer inputs；接受生产真实 canonical/Loop source
执行，明确 model entry 到 actual guard exit 的 frame。39 端点审计通过。语言
服务原有实现被 domain 实例消费；kernel 不变。安全域为原源 silent normal
completion，candidate 跨入口、dependency/alias guard 与 host progress/divergence
安装仍须完成；完整 header-stability guard 不等于完整 guarded candidate rule。
`ENCODE`／`PRESERVE` 等参数本身仍不是能力，须逐个
记录其 producer；这次没有把未完成的整段 guard／factory 计作已经自动取得。

验收继续按 `226ba94` 的 proof-first 顺序；compact 条件、实际检查成本、有用
接受域和实例作者工作是最终要求。`271f6fc` 的并行写作已落实到
[LNCS 稿件](../paper/README.md)，每个相关实现阶段同步正文及证据。
以下后继段落保留各阶段的固定能力边界；当前缺口以上述核对及工作计划为准。

[最新 numeric producer](research-checkpoint-2026-10-06-loaded-affine-numeric.md)已按该限制实现：语言从原 header 提供安全 capture／temp 运输与真实 first body；domain 将 receipt 接到旧递归 headers／已用参数及 numeric/profile 编码；当前 certificate 库负责 primitive safety、defined dispatch 和全部完成检查的 soundness。静态 site checker 绑定原 loaded AST 和 cache freshness。25 个新端点通过，kernel 不变。Prepared-entry snapshot 是当前读值，由 producer 取得；不是未来稳定性。扫描 coverage、字节级观察保持、conditional candidate 和实际语言安装仍是后继义务，不能从这张 numeric certificate 推出。

[body prefix／缓存源桥](research-checkpoint-2026-10-06-loaded-affine-body.md)进一步划清复用责任：语言统一从 actual structured body 证明权限运输和 protected-temp frame，prefix library 组合 domain 的逐 body check，语言再从已证明的观察保持取得完整缓存源执行。递归 affine adapter 复用 checked package，增加 loaded/body pointer register freshness 核对；domain 仍须生产实际 body 的全部访问许可、覆盖和 byte separation，并构造 `BODY_CHECK`。34 个端点及 alias 源／拒绝／具体 allocation fixtures 通过；不是新的完整 recursive physical scan 或 compiler。

[body domain 阶段](research-checkpoint-2026-10-06-loaded-affine-body-domain.md)已生产上述实际访问许可与写 coverage：原 first-body receipt 提供参数 words，当前完整 body 提供递归 Loop 执行，语言权限运输把实际点 capabilities 带回 guard entry；领域地址适配许可 private cursor 的实际比较。点写分离经真实写 trace 推出 body preservation，reads 可以 alias bound。25 端点审计通过，kernel／旧 host 不变。领域库仍须证明完整扫描覆盖与检查执行／接受结果；语言 materialized host 负责其 private frame、结果和 root 短路实现，之后完整程序安装继续由现行 Clight host 承担。单点比较域和写 footprint 不算已经完成该扫描或 compiler。

非矩形 pointer 阶段的具体归属见 [接入设计](affine-pointer-domain-next.md)：kernel 保持不变；语言提供 stable frame 的 counted-loop decode、实际 first-body 到达和公开游标恢复；domain 提供实际 ragged 点集、pointer body 模型对应、访问覆盖与充分条件推导。candidate checker 仍独立证明域／重排合法性。[完整条件](research-checkpoint-2026-10-06-affine-pointer-alias.md) 从真实 source prefix／有限正常源执行生产 D；[新 compiler](clight-affine-inner-pointer-compiler.md) 已进一步组装两套 candidate ranges、独立 certificate、实际 lowering／restore 和 local contract，消费已有 progress／placement host 接到 Csem→Asm，不归作 framework 自动发现优化前提。

[完整 scan 后继](research-checkpoint-2026-10-06-loaded-affine-scan.md)已关闭前段的检查执行与接受结果义务：语言提供实际 Mint32 地址比较和 root 拒绝短路；领域库用当前 body 的真实许可实例化递归 child scan，并在 body 接受后推进实际源前缀。静态描述器将 capture、numeric、runtime gate 和全部 scan 合成一段代码，没有逐 body 语义回调；现行 certificate 库以原 source completion 为 D，给出安全、分派、全部完成检查的 soundness 和 public frame。接受导出完整缓存源执行与同一最终 memory。38 端点审计及真实自别名拒绝／同 block 接受通过，kernel 和现行 host 不变。优化方仍须连接候选 checker；完整程序安装、typed allocation、提取和真实 C 是后续语言／使用者验收，不从这张稳定性证书推断已完成。


[候选／compiler 后继](research-checkpoint-2026-10-06-loaded-affine-multi.md)关闭上一段当时未连接的
candidate 与完整编译证明：语言构造器支持 kernel 已有的 arbitrary entry relations，携带新 cache；
domain 从稳定性接受生产真实 cached execution，再运行旧多数组 alias，取得旧 candidate validator／backend
的实际执行与出口。checked factory 接受数据提案，语言的既有 loaded-region host 独立核对原源 progress
和 private placement。32 端点审计、新 Csem→Asm 与旧两条 42-assumption 回归通过，旧对象绑定保持。
最难关闭的是 cached completion 只能是 stability 的结果而不能是 guard safety 的假设；整个连接没有新增
kernel 能力。该阶段当时尚未验收 frontend／提取／新 native；后继结果如下，成本和作者负担仍待验收。

[可运行后继](research-checkpoint-2026-10-06-loaded-affine-multi-native.md)关闭上述运行缺口：
不受信任 frontend 只提出 source metadata、cache 和 candidate；checked factory 仍绑定实际 source AST。
语言层保留完整 typed allocation，候选资源池剔除受保护 cache 所在 pair；domain 的原 disjointness
checker 与候选证明继续负责安全，无新 kernel 接口。六配置 624 次 C→assembly 调用、208 次
Clight 路径调用和 21 个未修改汇编探针确认非空递归重排、多数组、两次 rewrite 及原 loaded fallback。
独立证明报告绑定资源修复后的 factory，前一报告不改写。下一项是 compact guard 的安全、接受与
入口运输，不能仅凭包络的数学正确性或 runtime 成功推断这些证明已经完成。

narrative 本轮更新为 `226ba94`：先闭合约定范围的证明链，然后改进条件推导／生成；scan 是中间实现。
自动化／可用性是最终要求。代码大小、运行检查成本和接受域分开评估，具体同例对照仍待完成。

[后继 guard 简化](research-checkpoint-2026-10-06-loaded-affine-reduced.md)把接受事实的复用落到当前
domain library：`affine_first_path_flag_frame` 根据 header dependencies 运输事实，未来 child controls
无需一致；语言的 protected-temp entry relation 提供输入 frame。`affine_multi_alias_only_execution`
在已证 numeric=true／result=true 下执行实际 residual scan。优化方继续提供原 metadata／candidate，
不新增每个实例的语义回调；factory、候选 P、local rule、host 和 kernel 不变。
此为具体 domain 的 residualization，不称通用 assumption extraction 或完整 guard minimizer。
35 端点、当前新 native／路径通过；旧 native proof/object binding 保持历史。
工作量探针证明 point／point-pair comparisons 没有减少，Figure 2 的组合源也未安装优化。
后续职责与难点见 [具体覆盖差距](olo-figure2-coverage.md)。

## 1. 三方各自证明什么

“框架提供 conditional correctness 接口”不表示框架替优化作者证明任意候选正确。“语言提供语义”也不表示每个优化作者都要重新证明语言的 if、load 和上下文定律。

| 责任 | 需要提供／证明 | 可以复用的交付 | 不由这一方自动解决 |
| --- | --- | --- | --- |
| 语言无关框架 | 最小 kernel 消费证书、证明局部 guarded rewrite；上层库提供条件组合／短路／安全后处理，并消费 host 安装证书组合有限次 rewrite | 参数化生成／简化算法的正确性；readonly 前台；消费语言安装定理的通用组合 | 哪个优化成立、任意语义命题的检查代码、具体语言的 guard 或上下文定律 |
| 语言／IR 实例 | 实际执行与观察；原子测试的机器语义和定义性；具体分派；私有资源与状态运输；effect／frame；合法位置／出口／小步匹配；后端连接 | 一次证明并供多条规则调用的原语、direct/shared 实现和 host；例如真实 `Mem.load/store`、temp agreement 与 CompCert simulation | 某个程序的足迹完整性、某候选的依赖保持、某处入口为什么具备所需事实 |
| 优化实现者，含 domain library | 寻找片段、提出实际候选／模型义务 A；候选条件正确性；入口条件 B 对 A 的覆盖；实例专属源／模型／候选对应和作用域证据 | 经验证的 candidate checker、受限投影／范围／足迹算法及证书；这些可以在一个领域内再复用 | 未证明的 oracle 答案不会因接入框架而获得正确性；没有一般 `extract_assumptions(S,T)` |

框架的组合证明以已经证明的语言定律为参数。优化实现者既可以直接提交证明，也可以提交不受信任候选、条件和 witness，由已验证 checker 产生证书。候选生产器和搜索启发式无需可信；成功输出仍必须绑定**实际** source、candidate、condition 和安装位置。语言、domain、核心的证明可以由同一开发者写，但接口和成本归属保持分开。

语言库可以提供“实际字节足迹分离 ⇒ load 穿过 store 保持”的定理；规则作者证明本次 body 的访问属于这些足迹，并满足权限／chunk 条件。核消费这个证据，不了解指针，也不允许只把 `p!=q` 当成任意字节区间分离。

最新 topdown 补充也已采纳：抽象接口应能由 SSA／CFG 或汇编实例解释，Clight 继续是主验收。CFG 实例另证明 live-out／phi／控制出口；汇编实例另证明 scratch registers、flags、memory 和分支控制。若实际检查改变 flags，语言不能只说逻辑 condition 是只读：必须证明这些变化私有且不影响分支，或给出保存／恢复与真实状态运输。第二 IR 是可选的表达力证据，当前没有宣称已经实现，不把它加入主功能的强制验收。

Clight 的 readonly tree／单 Boolean realization 与循环式私有 footprint 扫描有不同的检查状态。扫描后的游标可能依赖 memory 和拒绝位置；语言无关 host 已允许实际 checked state 和入口关系。10 月 6 日的 [公共 private-scan compiler](clight-private-check-migration.md) 已完成这条实例化，不将它描述成任意 stateful 检查的通用合成器。

本阶段分工可以在源码中核对：[Safety](../prototype/interface/ClightPrivateScanSafety.v) 和 [Host](../prototype/interface/ClightPrivateScanHost.v) 由语言解释实际求值、有限循环续行、结果解码与任意完成分支的 exact dispatch；[Preservation](../prototype/interface/ClightPrivateScanPreservation.v) 提供公开观察、分支 temp 运输，并调用既有 kernel 的 `guardify_preservation` 和小步安装。domain 的 [Certificate](../prototype/interface/ClightParamPointerCertificate.v) 提供实际 source-derived D 下的扫描安全、protected frame 和 `accepts⇒P(original)`；候选对应和依赖核对继续由优化方的旧数学证书承担。source／candidate 的实际表和 private pool 接到了 Csem→Asm，并完成提取和原生验证。

`check_safe` 使用覆盖已到达 `eval_expr`、if 测试和有限 loop 续行的归纳判断；它不是完成见证的改名。实际 bounded scan 的既有执行与确定性可构造该判断，再由语言定理推出可用性。保护集同时覆盖公开入口与前提所依赖的 header、参数和 pointer binding，语言无需知道这些维度的具体意义。局部保持接口观察完成的 silent normal region，完整程序结论是 backward simulation；没有新增任意无限 pointer fallback 宿主。38 个端点和实际运行的证据见 [阶段记录](research-checkpoint-2026-10-06-private-scan-compiler.md)。

## 2. 四张证书与一个安全域

下面四项是逻辑环节，与上述三方责任不是一一对应，也不要求每个使用者手填
四份 record。库与 checker 可以共同生产一个环节的证据。这里 `C_host` 表示
实际 guarded choice／checked-state 运输；region 安装与具体 rewrite site 的合法性
仍在后续独立验证，不能把分派 law 当作整程序定理。

对真实 source S、candidate T，区分局部／模型义务 A、入口语义条件 B、实际 guard G，以及 G 可以有定义地执行的域 D：

```text
源路径／placement 证据 ──► D
                         │
                   C_guard: 在 D 中安全、可用；G accepts ⇒ B
                         │
                   C_derive: 在 D 中 B ⇒ A
                         │
                   C_opt: 在 D 且 A 中 T 对应 S
                         │
                   C_host: 实际分派与状态运输
                         │
                   语言安装定理＋实例 region／site 证据
                         │
                   guarded program ──► CompCert 后端
```

D 不能预先包含待检查的 no-alias／稳定性事实。它说明当前哪些观察可安全取得；后续观察可以依赖已完成检查的正结果。false／unknown 只触发回退，不承诺 B 的否定。语义充分条件可以保守加强，因而 `C_derive` 不要求最弱条件或逻辑等价。

| 证书 | 主要生产者 | 当前可核对的接口／证据 |
| --- | --- | --- |
| `C_opt` | 规则／优化实现者或已验证候选 checker | [conditional_equivalence](../prototype/interface/GuardedRewrite.v)、局部状态还原；完整循环也可使用 [open_region_protocol](../theories/ClightOpenRegionContract.v)，须提交实际执行的匹配 |
| `C_derive` | 优化／domain library | [readonly_condition_entails](../prototype/interface/GuardedRewrite.v) 消费推导证明；[盒状 affine 包络](affine-box-condition-derivation.md) 提供受限符号算法及实际宽度使用者，不是通用投影算法 |
| `C_guard` | 框架上层库＋语言原语＋实例域证据 | [只读 tree 合成](../prototype/interface/ClightReadonlyTreeSynthesis.v)、[loaded tree](../prototype/interface/ClightReadonlyLoadedTreeSynthesis.v)、[依赖 prefix scan](../prototype/interface/ReadonlyPrefixScan.v)、[实际 private-scan host](../prototype/interface/ClightPrivateScanHost.v)；实例仍证明 coverage、原语安全和 source 支持 |
| `C_host` 与后续安装 | 语言实例证明 choice／运输定律及安装；优化／site 提供 region 与 placement witness | [select_exact](../prototype/interface/GuardInterface.v) 与 [实际 realization](clight-guard-realization.md) 解释局部分派；[direct](../prototype/interface/ClightReadonlyProjectedCompiler.v)、[shared](../prototype/interface/ClightSharedProjectedCompiler.v) 和 [open host](../theories/ClightOpenRegionProof.v) 另证具体安装；完整 Csem→Asm 结论是 backward simulation |

这些是逻辑责任，不强迫每个使用者填四个重复的 record。可以将证书封装在一个已验证库中；验收仍逐项回答它们来自哪里。不能把 normal-completion 的 big-step 观察接口说成已经观察了全部无限行为，也不能把实际 forward 小步安装证明改称任意目标执行的双向等价。

证书的方向也要和宿主一致。核已经分别提供 refinement 与 preservation；`readonly_projected_clight_rule` 要求双向局部等价，但 private-region 安装实际消费的是源执行到候选执行的一边。旧 [encoded_private_rule](../theories/ClightPrivateRule.v) 及 [named candidate compiler](../adapters/compcert-memory/GuardMemoryNamedCompiler.v) 主要交付条件性 source-to-candidate 保持，并且局部端点量化实际 program 的 globalenv。10 月 6 日新增 [readonly_preserving_clight_rule](../prototype/interface/ClightReadonlyPreservation.v)，直接消费这一保持证书；双向规则和保持规则共用实际安装证明。真实 [named affine／tiling 使用者](clight-polyhedral-preservation.md) 已经连接候选／依赖核对、只读合成、direct/shared 分派与 Csem→Asm，没有要求旧 checker 提供未证明的反方向。统一 realization 复用分派／运输，optimizer 仍承担实际模型对应和入口覆盖。

## 3. 用当前完整循环逐项落实

实际例子是 [unsigned memory-bound 缓存](clight-guarded-circular-case.md)：

```c
for (; i != *bound; ++i) *out = i + 2U;
```

候选先私有缓存 `*bound`，随后用 cache 作相同循环的测试。这里允许 unsigned wrap；不是把所有循环都强加 no-overflow。

1. **优化方的 A／局部证明。** 非空时 out 与 bound 的实际 word 单元分离，store 保持 bound load；候选／源每步对应并保持公开 i、内存和外围 continuation。[CircularTransport](../prototype/interface/ClightCircularTransport.v) 和 [CircularSimulation](../prototype/interface/ClightCircularSimulation.v) 承担具体规则的这部分，不能称为任意循环自动化。
2. **入口 B 与编码。** B 是活动头部加当前 word 分离；这一例 B 接近 A，推导很短。它不替代多面体实例中“入口 B 覆盖所有迭代处义务”的全称覆盖问题。
3. **D／guard 的安全。** 先进行源头部本就要进行的 bound 读取；只有活动时才比较 out/bound。比较依据来自实际源首次 store 的有限前缀，[circular_domain_from_prefix](../prototype/interface/ClightCircularGuard.v)。不用整个源循环完成，也不执行 ghost 权限查询。生成器消费已认证原子，接受才取得单元分离。
4. **语言与宿主。** 私有 cache 写入位于已选择候选内部；direct guard 本身只读。[open_region_protocol](../theories/ClightOpenRegionContract.v) 保留完整 source fallback 的逐步执行。非空 alias 源和 guarded 目标均有真实 Clight 无限执行证明；小步进展只约束零步匹配，未加 source 无条件终止假设。语言库复用作用域、temp／memory 运输和全程序 simulation。
5. **输入绑定。** 实际 C frontend 的 body `Ssequence Sskip`、signed `1` 自增常量必须与 matcher 和执行模型一致。模型定理、完整程序 theorem、实际选中编译和 native 回归是不同证据，均不能省略。

这个例子检验语言宿主和有条件读取／稳定性机制，不是完整多面体 optimizer。真实 affine／tiling 迁移还须消费外部候选、依赖核对和本节没有自动解决的 `B⇒A`。

## 4. 最难的地方和怎样验收

| 难点 | 不能用什么替代 | 必须交付的证据与责任 |
| --- | --- | --- |
| 入口 B 覆盖全部局部 A | 枚举上限、扫描 fuel、逻辑 implication 字段、永远拒绝 | domain 算法的源实例覆盖；循环控制、机器值与数学域对应；非空接受域与保守拒绝。优化／domain 方证明，核复用后续编码 |
| guard 自身安全 | 假设 P 后证明检查无错误；用数学整数计算机器条件；先 preload 尚未定义的参数 | 语言原语的机器算术／指针定律；按源活动和已接受事实组织依赖读取；检查自身溢出、空路径、alias、权限边界反例。语言库＋实例 D 证据 |
| 候选模型与真实执行一致 | 只验调度矩阵、不验证实际 body／地址；把另一配置的能力算入当前 pass | 实际候选／依赖 validator 消费；源／候选 C AST 和执行对应；no-wrap、footprint、layout、公开游标出口。优化方，复用语言运输设施 |
| 保持有限／无限行为和公开上下文 | 仅 completed-run 等价；native 超时；把 cache 当不存在 | 正常出口／frame、私有 state 关系、局部小步匹配及宿主 forward simulation，明确内部 call／return／label 限制；最终 Csem→Asm 端点。规则 witness＋语言宿主 |
| 降低作者负担且有实际价值 | 增加 record／端点／相似模板；只量 Clight 打印字节 | 至少两条规则消费同一 condition／realization；记录专属 obligations 与证明代码；同源 direct/shared 对照和同版 CompCert 原生成本。核／adapter 复用、domain 接入、测量分别报告 |

第一行与第三行是主多面体使用者的核心难点；第二行是条件处理设施必须真正解决的难点；第四行是不可被抽象 if 隐去的语言实例工作。10 月 6 日的第一项迁移复用矩形范围与 named memory 的全实例对应，第二项 [参数化仿射内层源](clight-parametric-preservation.md) 复用已有端点覆盖、机器范围 lowering 和不同布局／偏移／多读取的 body 对应，并运行实际 schedule generation 后重新核对候选。二者都消费仿射／分块依赖核对器，通过公共保持、分派和安装接入。此次没有新增一般 B⇒A 推导算法，实际参数化 pointer footprint 随后经公共 private-scan 路线迁移；一般深度 affine 源与该 pointer package 的组合仍待扩展。都纳入 [当前计划](current-work-plan.md)，不以完成其中一行宣布全部目标完成。

随后新增的 [符号包络使用者](affine-box-condition-derivation.md) 明确分开三项新工作：domain 库证明系数符号推导覆盖任意有限维盒内的全部点，Clight 库证明 modular 仿射求值及最终 signed 比较范围，优化使用者证明接受建立所有行宽义务并接到旧局部证书。语言检查替换服务保留原 D／P／candidate，复用已有 reachable-test 安全、分派与安装证明。实际 compiler 替换宽度树，尚未替换 pointer scan。其困难观察边界是 `p+k` capability 不蕴含原始 p weak-valid，不能在没有源前缀证据时插入 base 比较；下一项 alias 条件推导必须同时取得这一观察许可和全实例足迹覆盖。

## 5. 研究主张与持续维护

[源观察支持的 alias 包络](source-observed-affine-separation.md) 进一步关闭了受限片段上的这两项证明：语言库从真实保留的 source load prefix 导出地址有效性，并安装 prefix 后的局部条件；domain 库将任意点包络接到实际 source footprint 与 modular 物理单元。readonly shortcut 复用同一 candidate C_opt、原 scan 和 kernel 组合。[新完整 compiler](clight-observed-pointer-compiler.md) 已实现 normalized AST 定位、三类实际 checker 的适配、提取和机器路径验收；原生矩阵由独立报告绑定。一般 affine pointer 源继续待扩展。这组服务的 proof audit 与前一阶段 compiler/native 报告分开，不从源码或端点数量主张性能或作者负担收益。

这次接入还暴露了 `C_host` 的具体责任：局部 `(loads;loop);suffix` contract 不能自动满足旧选择器只针对根部 loop 的 source progress。Clight 库新增 [序列 contract 运输](../prototype/interface/ClightSequenceContracts.v) 与 [序列 placement checker](../prototype/interface/ClightSequenceProgressSelector.v)，组合已有 framed 小步协议，保持正常后缀的真实 memory effect。domain 适配器核对源 AST、scope 和原候选证书后调用这些语言服务；kernel 不认识 loads、loops 或 pointers，也不增加 source progress 假设。最难义务中，安全许可和全部 footprint 覆盖已在受限模型关闭，宿主通过实际序列协议关闭；一般控制出口、一般多面体域和作者负担收益仍未由本例证明。

[共享 fallback 的实际接入](clight-shared-pointer-shortcut.md) 已按同一边界实现：语言库证明 direct tree 的真实正常执行运输到共享 AST，保持 trace／temps／memory；domain 将已有 matcher／三类 checker 的最后一步参数化，复用 D／P／candidate 与 coverage，核心组合定理未变。新的 compile_realized_observed_pointer_correct 对两个 lowering 值都给出 Csem→Asm 结论。79 端点审计及提取、两个完整十五配置矩阵和二十个机器路径探针全部通过；每种模式 5,640 次配置内调用，全本轮新编译，十五份 direct Clight 摘要保持冻结基线。见 [阶段记录](research-checkpoint-2026-10-06-shared-pointer.md)。一个真实二维配置的 scan AST 13→1，linked 函数 11,750→1,566 字节。这是有实际编译产物支持的语言服务复用和代码规模结果，没有扩大 condition／源域，也不是计时或总证明负担减少的证据。候选与对称 base 比较的冗余继续保留。

整体叙事是“小的语言无关 verified optimistic transformation 框架＋有实质算法与条件正确性证明的 CompCert 循环实例”。kernel 的组合定理较短，这不要求框架承担优化发现；贡献必须由实际可复用的证据处理服务、语言宿主和困难 optimizer 的接入共同证明。更广泛 conditional rewrite 作为接口实例；未实现的 vectorization、layout specialization 等不计 evaluated 能力。

每次 P1／P2／P3 验收记录三方新写了什么、复用了什么、哪张证书尚缺。和 OLO／CoreJIT／Chamois／Peek 做同例对照后再判断增量；未取得的文献／artifact 能力保留未知。[10 月 6 日一手补核](related-work-interface-check-2026-10-06.md) 已确认 Chamois oracle 的 CFG／invariant 输出和实际 CFG expansion 模拟，以及 Peek 的局部证明、normalization 与 liveness 宿主；这些已有服务不能单独算作 GuardCert 增量。性能、证明负担和新颖性各有独立证据，不能从正确性计数互相推导。

新的 [非矩形 source preparation](research-checkpoint-2026-10-06-affine-pointer-source.md) 进一步按这一责任划分实现：框架上层库的 `sequence_readonly_conditions` 负责有依赖条件的组合；语言服务 `readonly_completed_tree_condition` 利用真实表达式确定性，把有限完成路径证据包装为 reachable-test 安全、完成及接受 sound；domain 负责 normalized 源／操作／范围 checker、header 和第一轮 body 的参数证据、范围／宽度阶段以及源 Loop／公开出口对应。该阶段先连接同一 package／入口的算术条件与源对应，随后继续组装其他证书。D 明确要求有限正常源完成，不据此声称处理无限源或依赖加载参数。

[前一完整 source guard](research-checkpoint-2026-10-06-affine-pointer-alias.md) 关闭 prefix receipt 和该实例物理 non-alias。静态 column cap 的 affine 代入由 domain 数学库证明，实际比较继续使用语言的 modular 求值／signed 范围定理，框架上层库提供已有 sequencing。`affine_inner_pointer_source_guard_execution` 将接受、实际源 Loop 与精确公开出口绑定同一入口；`source_prefix_domain` 是有限入口 producer。该阶段当时未完成候选和安装，其历史报告不扩称全程序证据。

[后继完整接入](clight-affine-inner-pointer-compiler.md) 已把独立 `C_opt`、两套范围与实际 candidate/restore 绑定到同一 source package。guard 消费 上层库 readonly sequencing，局部分派和 source-prefix contract 消费已有语言服务，table 的程序 simulation 复用旧 host；具体新源形状由实际 progress fixture 核对。103 端点审计、提取、六个原生配置共 486 次调用和五个机器写入顺序探针通过。这里新增的是 domain 实例连接与不受信任候选整理，语言/核心的原定律未改；没有性能或 proof burden 收益结论。

后继 [分块接入](research-checkpoint-2026-10-06-affine-pointer-tiling.md) 关闭同一受限 pointer 源的 quotient witness／实际 candidate 对应：domain 用旧独立 tiling checker 产生与 mapped 相同的 `C_opt`，两条路径共用条件、lowering、restore 和 local contract，kernel／语言 host 未改。109 端点审计、提取、十一配置共 891 次调用及七个机器路径通过。tile 控制数从 caps 在编译时取得；不增加通用运行时 floor/ceil 语义，也不据此主张 proof burden 收益。

最难义务继续落实到下一项：多个依赖 preload 的读序与稳定性，以及一般深层 affine 源/出口。生成器的数学测试可能无法安全编码，故未证明的整理输出只能经完整 checker 再取得证书。框架不将候选整理视为自动条件推导；原 `C_derive` 和 `C_guard` 仍各自有实际证明。

[Loaded pointer 局部规则](research-checkpoint-2026-10-06-affine-loaded-pointer.md) 进一步检验这个顺序。语言从实际 retained preload 取得值观察，沿 loaded headers／rows 运输执行；domain 从第一次真实活动 body 取得 scalar 定义性，随后由接受范围和已验证写足迹排除 bound 单元。load 保持由实际 stores 推出，不写进 D。框架复用域限制与 `sequence_readonly_conditions`，将新的 preliminary 接到原候选条件；独立 package 和 actual lowering 仍由优化方提供。

该局部阶段的 `alp_observed_candidate_contract` 保持实际 prefix、公开出口与完整 memory，当时安装还缺 loaded nested source progress／matcher；31 端点 proof audit 不计为新 full compiler 或原生证据。三角实例以源已有 public n 缓存 p[0]；generic 运输允许任意观察 pointer，具体 exclusion rule 核对同一 write buffer 的静态逻辑单元。

[后继 placement](research-checkpoint-2026-10-06-loaded-placement.md) 将一个困难区分落实到实际协议：`C_host` 对原 loaded loop 的进展不依赖优化待检查的 bound 稳定性。语言的 strict nested 协议要求 body 每步保护 iterator，用机器最大值保证成功 increment 下降；syntax checker／sequence host 消费该协议。body 改变 bound 单元的 fixture 也通过进展检查。Domain 仍独立负责接受时的全部写足迹排除、源缓存运输和候选证书，kernel 未修改。

该阶段的固定 optimizer profile 已将原 mapped／tiling／schedule checker、实际 guard／restore／fallback、prefix/suffix 和 table host 组合到新的 Csem→Asm 定理。语言 progress 支持任意标识符，但优化 matcher 仍绑定 fixture 标识符；因此没有把一般 frontend 接受、提取或原生结果算作完成。下一验收必须实际推广 source adapter 并验证完整 C 的非空接受。多个依赖 preload、private snapshot 和一般 bound-pointer guard 继续待证；完整目标 active。


[最新 context-lifting 评审](topdown/context-lifting.md)的 [Clight 源码核对](clight-boundary-contract-review.md)进一步区分语言库定理与每次 placement 证据。`projected_region_contract` 和 `open_region_exit` 都复用 temp agreement 与 memory equivalence，但 completed-run host 还需要独立 source-progress 协议；open host 直接匹配每一步及到达的出口。不能将前者削弱为完成路径后声称支持任意 divergence，也不能因字段相似自由互换两类契约。当前全程序 live 集合保守包括全部源 temps，没有实现 context 最小 requirement 推断。

[参数化 loaded compiler](research-checkpoint-2026-10-06-affine-loaded-compiler.md)已经实际落实三方分工：语言从任意 prefix 位置生产值 receipt，复用不假设 bound 稳定性的 progress／table host；domain 通过 checked package 的真实 header/body 生产 preparation evidence，范围接受后才证明全部 writes 排除 bound，并运输到原候选证书；框架上层库用域限制和原 readonly sequencing 组合检查。源 snapshot、loaded fallback、quiet suffix、不同 normalized identifiers 与 candidate/restore 都进入真实 C 编译及机器验收。新 evidence 接口由 loaded 入口消费；旧 cached 入口仍用其原证明，不把两条实例的相似证明说成已经共享同一实现。

当前最难的下一义务是不同名 bound buffer 与写缓冲区之间的动态物理分离，随后是依赖读序／private cache 的 original-entry 事实与上下文运输。静态逻辑单元排除没有证明不同 base 的实际无 alias；仅 `bound != destination` 也不足。kernel 的抽象 `lift_refinement` 字段不解决这些问题。

[源顺序稳定性服务](research-checkpoint-2026-10-06-affine-loaded-stability.md)进一步分开这些责任：语言证明实际 store 的权限运输、已到达 loaded header 的整行执行取得和成功后续行；domain 从真实 row decode 取得每个 write receipt，生成不修改公开坐标的仿射地址表达式，并将其等号检查接到物理 byte separation／load 保持。当前行的全部检查已消费上层 `ReadonlyPrefixScan` 库；不同 memory blocks 的安全等号比较和 alias 后停止有真实 Clight proof fixtures。最小 kernel 未修改。

该阶段仍缺 checked source package 到逐行扫描实例的完整连接，以及候选／whole-program compiler 安装。`loaded_rows_prefix_spec` 的 `ROW_CHECK`、`DECODE` 和 `PRESERVE` 是有类型的使用者证明参数；`memory_affine_row_domain` 的参数／范围／receipt 字段要由实例交付，不能把接口字段算作已经解决。新的 row probe 定理和旧 compiler 回归各有审计边界；这次不新增原生能力、private snapshot 或 proof burden 收益主张。


[独立 bound pointer 的后继证明连接](research-checkpoint-2026-10-06-affine-dynamic-loaded.md)已关闭上述实例参数：checked package 的访问编码／范围／word、真实 row decode 和实际 store receipts 共同构造每次到达的 row 安全域；足够 fuel 覆盖全部活动点，完整 guard 接受后才得到 bound 保持。新 matcher 允许独立 bound pointer，原三类 candidate checker 与 language host 接到新的 Csem→Asm theorem。这里没有把这些领域证明交给 kernel。

下一困难位置是实际 guard lowering：嵌套 tree 在成功出口复制后续 scan，column cap=3 的实际 fixture 已显示 7／35／147 个测试随 outer fuel=1／2／3 增长。共享 fallback 不等于共享 scan continuation。需要保留顺序结构，并证明 private 状态、短路、安全和分派，再完成提取／真实 C 运行；当前只有 compiler proof，没有新增独立 pointer 原生能力。multiple dependent preload／private snapshot 的入口事实和上下文运输继续待证。

[顺序 plan 后继阶段](research-checkpoint-2026-10-06-affine-planned-loaded.md)已完成这一 lowering 和运行验收。语言库提供 plan/tree 精确运行对应、实际 private Boolean 代码、先写后读、原入口 branch 运输和公开 frame；资源反射 checker 把 freshness／structured branch 条件变成静态拒绝。domain 接入证明实际 affine plan 等于原完整条件，从而复用之前的检查安全、coverage、bound 保持、候选正确性。原 matcher、candidate checker 和语言 table host 接到新的 compiler theorem及实际提取入口，没有修改 minimal kernel，也没有重证 `C_opt`。

新正常 branch 运输仍有具体边界：E0／Out_normal，structured 分支，不接受 calls／labels／returns／switch；whole-program host 继续承担独立 progress，不从局部正常等价自动获得 contextual closure。六配置 222 调用、十三个机器路径验证实际安装、接受、拒绝和 bound 改写后的出口；默认 64×64 cap 亦已运行。当前最难的下一义务是缺失 public snapshot 时的 private 读取安全、original-entry 事实和私有状态运输，以及多个依赖读取。按 cap 展开的 guard 仍有代码成本，性能、一般深层域和同例 proof burden 尚未完成。

[private snapshot 后继](research-checkpoint-2026-10-06-affine-private-loaded.md)落实了单个 direct header 读取：语言 `private_source_preparation_contract` 把原执行运输到实际入口，安全构造 prepared execution，消费扩展 scope 的契约后投影回原 public scope；私有初值无需一致。`loaded_header_snapshot_read` 从实际首次 header 提供 nonvolatile Mint32 许可，零次 body 也有这个 header，不预置未来稳定性。源 selector 提供 flattening／frameability，freshness 静态核对；domain adapter 仅委托整个原 planned-loaded factory，原 `C_derive`、`C_guard`、`C_opt` 保持。host 的 progress 与 rewrite key 都作用于真正原 source，prepared source 只是内部证明和验证接口。

两个无 bound 快照的实际 C 域通过提取、444 次新入口调用、74 次旧入口对照和 28 个机器探针（含两个旧入口对照）；公开 marker=123 保持，读取 bound 的 fresh temp 没有泄露进 public scope。五个新 `.v` 与 140 端点审计通过，无新增公理，完整 compiler 沿原 42 项基线。该结果不代表任意 preload 安全：仍要求 body-pointer receipts；下一困难是多个依赖读取和 Mint64／Mint32 等不同 chunk 的 byte footprint 保持。现有 preparation 桥不自动提供这些 domain 证据；默认展开 guard 的代码成本和 P4 仍未解决，kernel 截止保持。

[依赖 header 服务](research-checkpoint-2026-10-06-dependent-header.md)继续沿此边界：语言证明实际双读取／captures／public preparation、可运行 byte-separation 条件、全部观察保持后的 prefix 和缓存执行运输；domain 将该条件接到已存在的 affine 地址编码、reached-write receipts 与真正 physical write sequence。当前已证明一个 point 接受后保持 pointer cell 和 bound cell 的实际 load；完整 checked-package row／outer scan 的 decode、范围和覆盖仍是未接入的实例义务。源 progress 独立证明，只用实际成功的 signed header 与保护 iterator 的 body；允许 memory observation 改变不等于已证明缓存优化合法。

51 个新增审计端点均在原 CompCert 基线内，kernel 与原 candidate checker 未修改。泛型缓存运输所要求的 body decode／观察保持，以及 host 的 typed private pool、placement／source key 和 program installation 不能由局部接口自动取得。尚无新 dependent compiler／extraction／native 端点；现有 body 仍是 Mint32 operations，progress selector 接受 pointer store 不增加 optimizer 的 body 表达力。

[完整局部实例链](research-checkpoint-2026-10-06-dependent-joint.md)已填入上述 checked-package 参数：domain 提供真正 reached-row decode、全部 write receipts、坐标范围和内外 caps 的 coverage；语言库运输权限、双观察 header／root temp frame 和实际缓存执行；上层条件库组合 preparation、joint scan 与 candidate guard。首次实际 header/body 的类型证据也已接到同一 preparation evidence；现有 candidate certificate 证明实际候选执行，局部接受／拒绝保持 memory 和 live temps。七模块／29 端点审计通过，没有把这些实例证据归为 kernel 自动提供。

未完成责任集中在实际接入：source selector／factory、safe captures 后入口 producer、不同类型的 private pool、progress／scope／placement 和 whole-program host；这些不由“局部 correctness”自动推出。本轮没有 new factory／compiler／extraction／native 结果，原 private-loaded 42 项完整 compiler 基线的回归与新六项局部端点分别记录。

[实际 dependent compiler 后继](research-checkpoint-2026-10-06-dependent-compiler.md)已关闭这组接入责任：语言 preparation 桥以实际原 header 许可有序 captures，入口 adapter 生产 typed pointer／bound／body receipts，并将扩展 scope 契约收回原公开 scope；domain 将 exact original AST、checked cached model、完整双观察 condition 的顺序 plan 和原三类 candidate checker 绑定。语言 host 分配 typed fresh pool，实际消费原源进展、位置／scope 和整程序 simulation。新 Csem→Asm 定理、40 端点审计、提取及两种实际 C 域 444 调用／28 store-order 探针通过，无新增公理；没有把 language host 的安装计作 kernel 自动提供。

难点现在转到实际 guard 成本与更一般的源：默认 caps 的函数约有 20,700 个 if，尚未循环化或给出性能收益；body 仍只消费 Mint32 operations 和源已有 pointer receipts。合法 pointer-store body、一般深层 affine 域、不同 body base 的 alias 接受及同例 proof burden 保持未完成。每个后继任务仍需注明新语言定律、domain 专属证据和真正复用的上层库，不能因局部证书已组合就省略实际源码／context 的义务。narrative `7d94d81` 的 kernel 截止有效，本阶段没有修改它。

[短路 cursor scan](research-checkpoint-2026-10-06-cursor-scan.md)进一步将这一成本工作拆成可复用的实际服务：Clight 库证明 cursor specialization 的表达式／lvalue／decision 运输，实际初始化、拒绝即退出和 signed increment，以及 check-plan body 的 private/public frame；domain 证明符号列地址和两种 chunk 探针对应原常量列 probe，完整 row spec 等于原已认证条件。实际 reached-row domain 给出可用检查，再取得真实有限执行和 primitive safety；实际接受通过 quiet determinacy 接到旧 row observation-preservation theorem。kernel 没有新增责任。

七模块／34 端点审计通过，每个新增端点最多六项原 CompCert 假设；旧 compiler 回归保持 42 项。row 域、freshness 和 public read scope 在此服务接口中仍是调用者证据，outer-prefix 推进和全 rows 覆盖尚未接实际循环；不能把这些有类型的义务或旧 compiler/native 回归说成新 factory 已完成。后继须由 checked package／typed pool／语言 host 实际生产并消费这些证据，再提取和验收成本。narrative 最新澄清与本地正文已再次核对一致，没有因此重排文件或修改最小 kernel。

[完整 cursor compiler](research-checkpoint-2026-10-06-cursor-dependent-compiler.md)已关闭该具体 package 的这些调用义务。Clight 库提供双 cursor 执行、private/public frame 和前置／扫描／后置的实际短路分派；domain 将其精确绑定原完整条件和已有 source-prefix coverage。有限资源 checker 从实际模板证明输入不与 cursors 冲突，factory／语言 pool 生产并消费证据；原 preparation、候选证书、source progress 与 whole-program host 保持。guard cursors 与候选 counters 分开，需要 21 个 typed private slots；这属于真实状态运输义务，不是新 kernel 能力或最小资源证明。

43 新端点、提取、两个 C 域共 444 调用、28 store-order 与 18 guard comparison 探针通过。后者在实际机器指令上核对源点顺序和拒绝后停止。默认 caps 的展开代码增长已在这两个 compiler 使用者中关闭，Clight／linked 函数大小分别报告；没有性能、一般多面体覆盖或作者负担收益结论。当前仍是 silent normal region、实际 body-pointer receipts 和 Mint32 operations 的具体 host/domain 范围。kernel 截止、语言安装与 optimizer/site evidence 的边界继续按 narrative `7d94d81` 明确保留。


[Deep affine 的当前接口接入](research-checkpoint-2026-10-06-materialized-affine.md)进一步检验这条边界：已有 guard 正常返回并在 private temp 中写/read Boolean，不能直接作为 result-fresh／break-refusal scan。新的 Clight library 提供实际执行、primitive safety、defined dispatch、全部完成执行 sound 和原入口／checked-entry 运输；domain 提供原源 quiet／writes、实际 guard execution、足迹／范围及 conditional candidate-local。两类实际 factory 消费同一语言服务，kernel 使用 `guardify_preservation`，原 table host 另证程序安装。六个新模块／26 端点、提取、5,118 次 assembly 调用和四组独立 Clight 插桩通过；没有把旧递归 IR、旧 source/candidate checker 或库参数算作新功能。

本实例的 source domain 仍是有限正常完成；actual select 的有限执行分解不要求所选分支完成，但该 host 不因此获得任意 divergence 定理。Stable-temp 深层域与两层 loaded/dependent 源尚未组合；新 alias scan 复用旧多指针能力，typed pointer stores／general source domains、P4 和同例责任／负担比较仍待交付。共享 proof 对象重编后的旧 cursor 精确摘要验证失败另记，当前 proof regression 不改写旧 frozen/native 报告。

[Expression-header 服务](expression-header-services.md)的最新切口延续 narrative `226ba94`：
语言库提供真实 signed header 求值、safe private capture、actual body receipt、generic source
prefix 与接受后的缓存源运输；raw memory observation 和 computed cache 不再合成一个值。
Affine client 核对原 AST／类型／private scope，复用旧递归 numeric checker，证明第一阶段
检查可用与接受后的 cached-word math domain。最小 kernel 与 candidate validator 保持。

剩余 domain 责任是由 actual body receipts 解码写 trace、给出每一轮观察覆盖／许可，并证明
实际 readonly body check 接受 ⇒ 观察保持；library 的 HEADER／PRESERVE／coverage 参数不
自动完成这些证明。语言 host 仍须生产 typed allocation、entry transport、source progress、
scope／placement 与全程序安装。43 端点审计、新空域／回绕检查及具体 alias 源执行只验证
上述服务和第一 numeric client；没有新完整 guarded rule／factory／compiler/native 能力。


[Loaded＋offset 后继](loaded-offset-affine.md)已用 actual body receipt 填入上述 prefix 服务：
raw load 与 computed upper 不再要求相等；body 检查由真实到达权限许可，接受后保持原观察，
再导出 cached-source 执行。新 domain producer 提供 guard soundness、candidate P 和 entry
transport，signed-expression 语言 host 提供安装。generic kernel、旧候选 validator／backend
均保持；新 Csem→Asm 与提取运行有独立验收。主使用者当前只自动提出 loaded-plus-constant
根，不能把一般 signed-expression 库的证明参数算作已经自动支持的语法。


[第二 loaded header 的新服务](nested-header-services.md)继续遵守上述分工：语言从原 outer
和 child headers 提供 conditional captures、actual child receipts、temp 运输和 indexed read
定律；prefix 库携带全 observation list，单 row 的 preservation 成立才推进 outer。语言再导出
双 cached-source execution，structured stores 的权限运输复用现有定律，优化方不用额外交任意
memory-effect 回调。Affine 库从 captured words 许可旧 numeric probe，不借完整缓存源执行。

48 端点审计和原 compiler／native 绑定保持，kernel 不变。joint physical scan 的许可／覆盖／
接受⇒preservation、原 nested syntax 到 canonical model 的 projected transport，以及新 factory
和语言安装仍需实际接入。点比较和相邻 word 的真实 Clight 接受证明不算新完整 optimizer；
整程序责任没有搬入 kernel。先闭合这些连接，再按 narrative `226ba94` 验收 compact 条件和
实际 guard 工作／接受域／计时，最终仍需自动化与作者负担证据。
