# Narrative 澄清：验证责任与下一验收

本次重新 fetch 并完整阅读 `origin/topdown/research-positioning` 的
[paper-narrative.md](topdown/paper-narrative.md) 和
[context-lifting.md](topdown/context-lifting.md)。远端为
`12419c1e1e3da450bf378742a2fb4e204e51e060`，这两个正文与 main 一致。
下面将澄清落实到当前实现和工作计划；本记录不新增证明、编译器能力或实验结果。

本记录对应 main `6b91b27` 的核对时刻。后继的[完整word扫描](tensor-word-outer.md)
现已独立审计 full outer、nested cached源和实际scan出口运输；下面关于outer
草稿的描述保留核对当时范围。完整loaded／dynamic compiler仍未安装。

## 最小接口的责任

框架消费实际 source、candidate、check 的证书，组合出局部 guarded correctness。
它不从任意程序对自动发现前提，也不解释 C 表达式、多面体或指针。
条件编译、推导和简化可以是可复用库，但各自仍须交付证明。

| 提供者 | 应当证明或生产什么 | 当前可核对的边界 |
| --- | --- | --- |
| 最小 kernel | 由检查证书和两条分支的行为证书导出局部 refinement 或 preservation。 | `GuardInterface.v` 的 `guardify_refinement`、`guardify_preservation`；两个方向是独立契约。 |
| 语言／IR 库 | 实际求值与检查安全、choice 语义、private 状态运输、frame、控制和安装定律。 | `guard_host.select_exact`；Clight 的 projected/open region 契约及 selected host。 |
| 优化／domain 库 | 实际源到模型、充分前提、局部义务到入口条件、具体条件编码接线、候选及公开出口对应。 | Tensor source/guard 服务、实际 affine/tiling checker、generated-candidate factory。 |
| 具体 site 的证据生产者 | 从实际程序核对选中位置、scope、typed freshness、合法进入／退出及支持的 progress。 | Selected-region 遍历、private pool 和 progress checker；annotation 本身不提供语义证据。 |

最后一行不是要求源码使用者手写上下文证明。语言提供一次性安装定理，
domain factory 和 site checker 对支持的输入生产该定理所需的具体证据。
不受信任策略可以提出位置、条件或候选数据；接受它们的 checker 才提供保证。

四条逻辑链 `C_opt`、`C_derive`、`C_guard`、`C_host` 用来指出证据来源，
不规定使用者必须填写四份 record。尤其需要区分两个语言责任：
`C_host` 是具体 guarded choice 的分派定律；完整程序安装还要消费 region
guarantee 和实际 context/site 的要求。`context_certificate.lift_refinement`
是 host 提供的定理字段，不是 kernel 自动取得的上下文闭包证明。

## 三种使用者的工作不同

对已支持的 source family，源码使用者标注区域并给出 phase、tile 等选项。
当前实际多面体路径自动产生候选，factory 核对 AST、metadata 和 witness，
语言 host 核对资源与位置，然后继续编译。使用者不为每个 site 提供
`SOURCE`、`ENCODE` 或 simulation callback；静态拒绝保留源，动态拒绝走原源。

增加一个 transformation/source family 时，domain 实现者需要交付新的
源／模型对应、前提充分性和条件编码证明，或将候选交给适用的 verified checker。
已有求值、frame、短路及安装服务可以复用。新增语法字段或一个带语义假设的
泛型 theorem，并不等于该 family 已有可用的数据接口。

首次实例化语言时，语言作者需要证明其检查、choice、观察关系和安装定律。
只读条件可以使用私有 cache/cursor/flag；这些状态变化必须由入口和出口关系覆盖。
换一个语言不意味着要重新证明 kernel 的组合定理，也不意味着自动取得安装证明。

## 当前最难的连接

目标源在同一个片段中组合 loaded bounds、literal component loop 和动态 Horner
地址。Header 与数据可能 alias；因此机器求值成功、header 稳定、数学 no-wrap
和模型合法性是不同事实。下一阶段按下面的依赖顺序验收：

1. **原源许可检查。** 从原源实际执行取得条件式 capture 和已到达的访问许可。
   空路径或前项拒绝时，不要求执行未来的 load；不能假定整个 cached 源已经可执行。
2. **接受推进前缀。** 本点检查接受并证明两个 raw header 保持后，才能取得下一
   原源前缀。完整接受再导出整个 nested cached 源。当前已审计成果到
   [完整 column/component 和 current-row step](tensor-word-column.md)；outer
   草稿尚未形成独立审计的阶段结果，不能计入已交付能力。
3. **机器状态连接模型。** 缓存源、literal 准备、numeric/no-wrap/layout 条件必须
   连到同一次完整 guard 的实际出口。Word 算术允许精确建模 wrap，并不因此证明
   数学整数模型成立；virtual/model entry 的执行也不能直接替代 checked state 的执行。
4. **真实候选与完整程序。** 将上述源对应接入实际 scheduler/codegen 的最终候选
   checker，证明候选进展、memory 和公开出口，再由 family factory 交付 region
   契约及 site 证据，复用 selected Clight host 和 Csem→Asm。

实际 codegen 的 raw 输出与安装的 adapted candidate 仍是两份不同证据。
当前最终 checker 核对后者，没有 raw→adapted 等价性定理。完成 full scan
本身也不关闭整个 loaded/dynamic optimizer 的验收。

## 局部保证怎样供上下文使用

当前 selected host 消费 `PrivateRegion.projected_region_contract`：从实际源的
silent normal completion 构造目标的实际小步执行，保持所选 live temporaries
和 `memory_equivalent`。安装另消费原源 progress、scope、freshness 和合法位置。
因此局部终止执行对应与整程序 simulation 是两项证明。

当前 compiler 使用 `program_temps` 作为保守的 live 集合；这不是最小 liveness
分析，也不是已经实现的任意 site-relative contract。一个较弱的 frame 要供真实
continuation 使用，仍须证明它足够覆盖 continuation 的观察。

Open host 的小步协议可以在不退出时继续匹配源步骤；它与只比较完成出口的契约
不同。State/frame、memory、trace、control、progress、private resources 可否进一步
拆成可复用条款，继续作为语言库设计问题。条款间存在依赖，暂不新增任意组合的
contract algebra，也不重排最小 kernel。

## 纳入计划的决定

完整 goal 保持 active。下一集成验收仍是同一个 loaded/dynamic C 输入经过
capture、完整 stability 检查、模型与实际 guard-exit 运输、真实候选、原源 fallback、
selected 安装和 assembly；覆盖接受、alias/profile 拒绝、条件式空域、未标注区域、
多 site 和 continuation 可见状态。分离的样例或更多查询端点不能替代它。

该约定 slice 闭合后，再用有证书的紧凑充分条件改善检查。替换条件须证明安全、
acceptance soundness 和入口运输，尽量复用候选与 host 的证书。Code size、
逐点工作、接受域、完整运行成本和每个实例的人工责任分别记录；cursor 循环只
解决代码增长。论文继续围绕这些可复用服务和实际责任写作，贡献定位需要直接
比较已有系统，不能仅凭局部组合定理宣称新颖性。
