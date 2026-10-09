# Verified guard library：服务分类与依赖契约

2026-10-08，对照 `topdown/research-positioning@c4b1395` 的澄清。
读者是准备增加条件服务或 transformation 的库作者。本记录从现有 Rocq
定义整理调用前提、成功事实和组合边界。

最新 [signed header 服务](affine-empty-signed-installation.md)复用generic
signed interval analyzer／range guard／lowering。旧非负限制来自client profile，
不是generic encoder。新的condition client消费同一readonly facts契约，复用
原源／capture／公开出口／安装；factory自动生产前提，源码用户API不变。
12新端点无新增公理，2,280／2,280同源输入add接受33→87、无丢失；极大
profile静态拒绝后旧builder另有190／190，旧五族2,638／2,638保持。参数仍有
profile界，mixed negative/active domains及旧candidate运行时组合未接。

此前 [共享 fallback](affine-empty-plan-installation.md)复用同一 empty 条件与
source/capture/exit证书，language library将readonly alternative降低到私有
Boolean与一份原源循环。Factory检查第三个typed private及resources；
selected Csem→Asm已接，9新端点无新增公理。2,280／2,280全输出及逐输入
path与冻结旧版一致，triangle fallback从32份到1份。条件仍是finite tree，
不是通用线性尺寸或收益证明；signed参数与旧candidate运行时组合仍待实现。

此前 [header-only empty rewrite](affine-empty-installation.md)将control／
conditional observation与affine endpoint编码接到actual source、负child
公开出口和selected Csem→Asm。All-empty入口不需要body words／array／alias
许可，empty outer不读M；factory从原执行自动生产实际header调用域。旧registry
静态优先，同binary旧五族保持。29端点无新增公理，2,280／2,280全输出通过。
该服务的非负参数profile和展开tree是明确限制；signed参数、compact lowering
及与旧candidate的runtime选择仍需实现，不以此宣称完整OLO能力或收益。

此前安装态见 [actual-row observation](affine-observation-installation.md)：
separation 和 zero-RMW 已分别建立 caller 所需的同一 header-match row 保证。
Factory 自动选取 alpha、检查 original row；它的类型/读取许可来自先成功的
numeric preparation。Readonly alternative、compact plan、actual candidate
和 selected Csem→Asm 全部接通。六配置2,448／2,448与同binary旧四族通过；
同源408输入的接受122→126、无丢失。能力限定为定义好的Mint32字观察保持，
该服务的完整成本336 batches全输出通过，全部16median仍高于source；
减少scan与增加接受不等于盈利。其他chunk／scalar、compact条件及general
loaded affine仍需各自验收。

此前 [zero-width installation](zero-width-installation.md)：ordered
first-or-second-reached许可、范围、N/M scan、data alias和candidate ranges
已接 actual checker／factory／compact plan／selected Csem→Asm。First-empty
现有实际接受；六配置2,016／2,016和同binary旧族回归通过。该 alias服务只需
typed ready与observed pointer receipts，不再额外要求cached completion；
factory仍自动生产适用的原源／capture前提。Broader／value-preserving条件、
recursive loaded和完整成本继续。以下记录保留各子阶段当时的范围。

后继
[原 loaded setup 阶段](affine-header-snapshots.md)已补上下面标明的新证明；
后继 [N/M stability scan](affine-snapshot-stability-scan.md)进一步生产实际
row/prefix 条件，并连接接受到 complete cached source；后继
[checked installation](affine-snapshot-installation.md)已接静态 producer、实际
candidate/fallback、source factory与共用 Csem→Asm。后继
[native pipeline](snapshot-polyhedral-native-pipeline.md)以相同condition规格的
compact plan完成实际原C／Pluto／CompCert与1,584／1,584输出/continuation验收；
完整成本、first-empty-child接受及broader alias仍待工作。

后继 [later-body 许可与紧凑条件](leading-empty-body-licensing.md)已证明 empty
prefix 保持入口 memory、原 later leaf 生产 body words，以及 affine endpoint
条件的编码／readonly 接受证书。它在 arithmetic、range 和 conditional
observation 三类之间运输调用前提，尚未接 factory/compiler；安装态的
first-positive 限制、candidate 模型域与 native 接受域保持。

后继 [zero-width 模型桥](zero-width-model-bridges.md)已把该 condition 的接受
接到完整 typed view、nonnegative width 和新 assumed-model certificate。
它复用 condition 编码与 validators，新增的是 domain 充分性/对应和实际
candidate lowering/public restore；kernel 不变。候选必须在新域重新检查，
全空模型不许可 body-only reads。Factory、stability 和安装态接受域仍待连接。

后继 [zero-width stability](zero-width-stability.md)已完成 ordered client：
first-reached input 许可 → geometry ranges/弱 ready → actual N/M probes →
观察保持 → cached-source transport，合并检查保留给定原执行的精确出口和
memory。它复用 prefix/composition/language primitives，证明 scan AST 与旧版
相同；十模块／35端点，无新增公理。仍需 wider-domain actual checker、
factory/compiler/native；全 guard 成本不由 scan AST equality 推出。

## 服务按建立的事实分类

分类不是互斥的：一个实际扫描可能同时需要 arithmetic、footprint 和
control 定律。也不要把这些类别规定成所有优化必须经过的固定阶段。

| 类别 | 成功所建立的事实 | 当前实现与明确边界 |
| --- | --- | --- |
| Arithmetic / representation | 被检查的机器计算符合所需数学值，或满足所需机器字关系 | [ClightNoWrap.v](../theories/ClightNoWrap.v) 的 `no_wrap_lowering_correct`、`no_wrap_flag_encodes_obligation` 是 unsigned increment 的具体 encoding/lowering；[ClightAffinePreparationEvidence.v](../prototype/interface/ClightAffinePreparationEvidence.v) 的 `affine_evidence_preparation_condition` 组合 header/range/width/body-range 检查。不能泛化成任意算术的 no-wrap compiler，也不要求所有 rewrite 都排除 wrapping。 |
| Ranges / footprints | 所需 reached-point 参数、索引或访问由 checked range / footprint 覆盖 | [ClightAffinePreparedFootprints.v](../prototype/interface/ClightAffinePreparedFootprints.v) 的 `affine_prepared_write_probes_ready` 同时消费范围、实际写 receipts 和 source package；[ClightTensorBackendGuard.v](../prototype/interface/ClightTensorBackendGuard.v) 的 `tensor_backend_guard_condition` 给 layout 事实。范围或 layout 不单独证明 allocation / load definedness。 |
| Memory separation | 指定访问、写入或观察之间的物理位置分离 | [ClightObservedWordProbe.v](../prototype/interface/ClightObservedWordProbe.v) 的 `observed_word_cell_check_sound` 需要 Mint32 chunk、alignment 和 capability；[ClightMultiTensorScanService.v](../prototype/interface/ClightMultiTensorScanService.v) 的 pair/canonical 服务建立 footprint-restricted `locations_nonalias`。不声称整个 memory 全局 nonalias。 |
| Value / observation preservation | 后续执行保持特定观察，即使允许重叠 | [ClightZeroRmwObservation.v](../prototype/interface/ClightZeroRmwObservation.v) 的 `checked_zero_rmw_control_execution` 在 checked control 与 `alpha=0` 下保持已有 defined Mint32 words；[ClightZeroRmwCondition.v](../prototype/interface/ClightZeroRmwCondition.v) 的 `checked_zero_rmw_condition_preserves_observers` 运输 word observers。它没有证明完整 memory、其他 chunks、pointer fragments 或 traces 相等。 |
| Control / conditional observation | 某一路径许可后续读取，或不活动路径跳过读取 | [ClightAffineHeaderSnapshots.v](../prototype/interface/ClightAffineHeaderSnapshots.v) 的 `affine_setup_capture_execution` 许可原 `K=i+*M` 的 raw-child capture；[ClightAffineSnapshotSourceInputs.v](../prototype/interface/ClightAffineSnapshotSourceInputs.v) 自动生产 original domain。Current observations用于 reached body decoder；[新 factory](affine-snapshot-installation.md)生产静态/private前提，[native pipeline](snapshot-polyhedral-native-pipeline.md)已验收原 C／实际 candidate／compiler，包含 empty outer 跳过不可读 M。 |

例如 zero-RMW 服务先调用 control 服务取得原 source 的 scalar 许可，再运行
arithmetic equality 条件，最后由 domain 的 effect 定律得到 observation
preservation。它不是另一种 nonalias 算法。另一方面，同一数组的 layout
injectivity 与两个数组之间的 separation 也不能互相替代。

## 每项服务必须说明的契约

采用同一份审阅格式，先不增加一个覆盖所有服务的 Rocq record：

```text
inputs: ordinary checked descriptors / actual code / resources
requires(original, current): safe invocation prerequisites
run(current) -> (answer, checked): actual language execution
ensures(original, checked, answer): entry facts and state relations
accepted: sufficient fact for the caller's obligation
refused: safe branch continuation, with no inferred negation
effects: reads, private writes, public/memory/event/control frame
producer: who establishes requires from the actual source/site
scope: completion, progress and observation coverage of this theorem
```

实际zero-RMW复用还有一项domain适配责任：它的已有输出
`mint32_words_preserved`只覆盖原本defined的Mint32 words；当前affine
`affine_snapshot_point_preservation`对任意point before/after要求原始load
equality。新client应显式利用transport中的header-match／word-valued
不变量来运输观察，再连接source/model/candidate，而不能直接把两项契约
视为相同。[Actual-row observation](affine-observation-installation.md)已实现
这一适配：两个 producer 分别证明 caller 的 reached-row 保证，source→cached
桥消费该保证，再复用 source/model/candidate 与整程序安装。它没有新通用
kernel record，也没有把旧point契约强行扩写为word服务的结论。

`requires` 中的事实不能被包装成检查自身的成功结果。比如“load 返回
Vint”是读取的前提或原源的 receipt；只把它写入 `ready` 并没有证明它会
由调用者获得。Domain 建立的数学 range 也必须先经过 language 的 arithmetic
correspondence，才能许可实际 guard 中的机器计算。

结果可能锚定在 original entry，运行却从已有 private capture 的 current
state 开始。每项契约须明确这个区别，并记录读 ports 的一致性和 accepted /
refused 两种实际出口。不能默认前一个检查完成后完整 state 仍相等。

读取清单应区分三种信息：temp read ports、memory observations，以及带路径
前提的实际 load receipts。`check_plan_reads` / `statement_temps` 是 temp
集合，不是 memory read footprint。上述共用 records 尚未携带统一的精确、
带路径 memory-read 元数据；各服务的 receipt / safety 定理承担这部分义务。

### 现有契约能复用到哪里

| 契约 | Safe invocation 的来源 | 实际出口与成功事实 |
| --- | --- | --- |
| `readonly_condition H D P G` | 作者证明 `D` 下安全和 available；调用者生产 `D` | 每次检查都保持声明的完整 entry state，接受推出 `P`；拒绝不推出 `not P`。Host 另证 choice 的事件/控制语义。 |
| `guard_certificate H D P Ryes Rno G` | Language 解释 safety，作者给安全、available 和 soundness | 分别给 accepted/refused entry relations；允许私有 state 改变。Availability 是存在一次 check execution，不是通用终止定理。 |
| `source_licensed_scan source ports public ready fact` | 原 source 的 `E0 / Out_normal` 完成执行、`ready(original)`、original/current 的 ports 一致 | 实际 statement 有限完成、memory 不变、source temps/public/ports 保持，私有 flag 返回 Boolean，接受推出 `fact(original)`；拒绝也有这些 frames。 |
| `nested_expression_capture_execution` | 原 source 完成、类型/quiet/frameable/freshness 条件，以及 child 不依赖 reset 的 column | 实际 root capture，active 时 child capture；memory 不变和公开运输。返回原 expression receipts，不含未来 stability 或 no-wrap。 |
| `zero_rmw_condition_encoding` | `register_domain alpha` 和 checked source control | 实际 readonly `alpha==0` 接受后，每次已给出的 source execution 保持 defined Mint32 words；source 是否完成以及 scalar 为什么可读是另外的前提。 |

前两项定义分别见 [GuardedRewrite.v](../prototype/interface/GuardedRewrite.v)
与 [GuardInterface.v](../prototype/interface/GuardInterface.v)；scan 的实际边界
见 [ClightSourceLicensedScan.v](../prototype/interface/ClightSourceLicensedScan.v)。
这些契约已经服务不同层次，不能为了统一外观强制 scanner 满足完整 state
equality。也不宜直接把 finite source completion 契约当作 open/diverging
context 的服务。Progress、合法入口/出口、scope 与 installation 仍属于
语言 host 和具体 site。

## 组合复用与待补义务

| 模式 | 已有定律 | 新服务仍须交付的内容 |
| --- | --- | --- |
| Ordered dependent checks | [ReadonlyConditionComposition.v](../prototype/interface/ReadonlyConditionComposition.v) 的 `sequence_readonly_conditions`；第二项在 `D /\ Pfirst` 下证明 | 第一项的成功事实确实建立第二项安全前提；纯条件保持同一 entry。私有 state 改变时，另证事实和读 ports 到 actual exit 的运输。 |
| Short-circuit / conditional branches | [ReadonlyBranching.v](../prototype/interface/ReadonlyBranching.v) 的 `branch_readonly_conditions` 和两侧 classifier facts；[ClightStagedCheck.v](../prototype/interface/ClightStagedCheck.v) 的 `staged_check_code_execution` | 每条实际路径的安全性。普通充分条件的 false 只有拒绝含义；activity 的 false 若用于跳过 source read，必须有 inactive fact 的证明。 |
| Conditional capture | `nested_expression_capture_execution` 和 capture frames；`affine_snapshot_capture_source_inputs` 生产 actual setup 的 original domain | Checked source/capture factory自动生产静态形状、fresh typed caches与 guard-exit连接，actual C/native已通过；初次捕获不含未来 stability。 |
| Prefix checks | `observed_header_prefix_receipt` / `observed_header_prefix_advance`；`observed_body_prefix_receipt` / `observed_body_prefix_advance` 接收 current observations | Concrete row receipts、N/M短路 scan与 accepted cached completion已接 actual factory/compiler/native。Private-Boolean plan保留原condition；失败后不继续未许可probes。动态扫描仍逐点，完整成本和broader接受域待验收。 |
| Alternative sufficient conditions | `readonly_condition_entails` + readonly branching 可构造接受同一事实的两个纯条件分支；既有 zero-RMW driver 有具体实例 | 对“第一项拒绝后试第二项”的私有状态版本，须证明第二项在第一项实际 refused exit 安全，且结果运输到同一 original-entry obligation。当前没有一个统一的 private-service alternative combinator。 |

纯条件的 alternative 可以让第一项接受时返回 true，拒绝时尝试第二项；
`condition_classifier` 的 refused fact 是 `True`，不是第一前提的否定。
因此第二项必须在原 domain 下安全，或者另有独立证书提供更强调用事实。
对于有私有 effects 的服务，类似组合还需 explicit refused-entry transport，
不得仅对两个 mathematical predicates 做 `or`。

Header stability 是检验这种复用的具体义务：

```text
licensed original observation
  + checked separation from relevant writes  -> observation preserved
  + checked value-preserving writes         -> observation preserved
```

两条路径应各自建立同一 observation relation 后，复用后续 source/cache
transport、候选和安装证明。`checked_zero_rmw_condition_preserves_observers`
已有 value-preserving 路径，但它的适用 source/control、chunk 和入口域不能
省去；也不能从 header stability 自动推出 candidate 所需全部 data-dependence
条件。[ClightTensorZeroRmwDriver.v](../prototype/interface/ClightTensorZeroRmwDriver.v)
的 `lwd_zero_captured_execution` 已在正域 scalar 许可后，选择 zero shortcut
或历史 scan。这是具体 reuse 证据，尚未证明它可直接适配当前 affine child。

## 当前 loaded-affine 任务的依赖顺序

具体原 source 是 `i<*N; K=i+*M` 的 loop setup，而不是预先无条件读取 `*M`
的另一个程序。用以下顺序审阅正在推进的原源桥：

1. Language 从原首个 root comparison 得到 `*N` receipt，运行 fresh private
   root capture。Root inactive 时跳过 `*M`，沿用该路径的原源行为。
2. Root active 时，原 reached setup 与 child comparison 许可 header 中的
   `*M` word。即使 child 为空，也要分开证明 header load 与尚未到达的
   leaf/RHS 的许可。缓存的是 raw loaded word；替换表达式先保持实际机器字
   语义，另由 domain 检查所需 mathematical/no-wrap 对应。
3. Numeric/range/domain preparation 消费这些实际 receipts。Footprint probes
   还需原 reached accesses 的 capability / alignment；不能从循环包络推断
   allocation，不能用 cached source completion 作为未经生产的调用前提。
4. Header/body decoder 消费 current observations；成功的 stability 条件运输
   `*N`、`*M` 到原 source 的下一段，再许可其检查。现有 header-prefix 的
   `DECODE` 不消费 observations，针对旧 temp-only setup 足够；新 loaded
   setup 已由后继 `ClightObservedBodyPrefix` 和 concrete snapshot row decoder
   补上这项边界。`affine_snapshot_scan_condition` 已生产实际 N/M stability
   条件，`affine_snapshot_scan_accepted_cached_source` 把接受接到 cached
   completion；后继 factory已自动生产静态前提并对齐具体原执行出口，接到
   actual candidate/fallback和共用 compiler proof。后继实际原C/native已通过，
   private Boolean lowering保留原condition规格；接受域和完整成本另行验收。
5. Domain 把接受事实接到真实 source/model/candidate 的 `C_opt` / `C_derive`；
   factory 接 actual guard exit、fallback 和公开恢复，复用现有 selected
   host / Csem→Asm。每个 site 继续生产 placement、resources 和 progress。

以此记录每个新增证明的 requires / ensures / frame / refusal，优先复用已有
arithmetic、capture、observer 和 candidate 定律。新 header snapshot 阶段
已独立审计 7 模块／29 端点，无新增公理；它不提供新 factory/native 证据。
First-empty-child、broader alias、一般
recursive loaded domain 和 OLO 原例仍需完整 factory/compiler/native 验收。

## 接口抽取与交付标准

先为当前 actual-header 桥与既有 zero/separation 两路径建立契约对照；当两
个实际 client 消费同一事实与入口运输时，才抽取 shared language adapter
或组合定律。服务实现放在 minimal kernel 之上：domain 负责充分条件和
源/模型对应，language 负责安全执行与 frames，factory/site 负责接入既有
guarantee/installation。源码用户继续只提供支持族的 marked C 与策略。

当前复用载体是实际 Clight statement templates 和已验证的生成器/扫描器。
若后续选择 callable C/Clight routines，需补 actual call semantics、参数/
返回值、memory/public/event frames、符号/程序链接，以及 compiler simulation
的连接；现有 inline scanner proof 不自动证明一次函数调用。是否 inline 或
call 用实际复用和完整成本决定，本阶段不先建一个 runtime C library。

每个后继服务分别验收安全、成功充分性、refused exit、真实 builder/安装、
接受域、guard 工作、code size 和完整调用成本。精确 Boolean correspondence
是某些实例的额外性质，共用接口只需接受充分性。库组织本身不替代紧凑
条件的推导或成本评估，也不延后当前 loaded-affine pipeline 的主任务。
