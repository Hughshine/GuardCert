# 循环式私有检查：公共接口迁移的证明缺口

2026-10-06。本文记录私有检查的迁移义务和当前证明进展，新的公共 pointer pass 尚未完成。旧 pointer 扫描和对应 compiler 已有证明；参数化 readonly 使用者的真实迁移见 [ClightParametricCompiler](../prototype/interface/ClightParametricCompiler.v)。当前 15 个扫描／分派端点的证据见 [阶段记录](research-checkpoint-2026-10-06-private-scan.md)。

## 实际输入和目标

考虑一个由实际源 package 定义的指针循环：嵌套域使用稳定寄存器矩形 bounds，body 通过多个 pointer 进行参数化仿射访问。它与本次迁移的 `j<U(i,parameters)` 非矩形 readonly 源是两种 source package。候选 checker 在抽象单元分离的条件下证明重排成立。domain library 从该 source 的真实访问构造 footprint，入口检查依次验证活动 header、参数范围，再遍历访问对与坐标，比较实际地址。拒绝时保留 source。

现有 [memory_param_axis_pointer_guard_statement](../adapters/compcert-memory/GuardMemoryParamAxisGuard.v) 就是实际检查代码：它写私有左右计数器与 flag，保持 memory 和声明的公开 temps。它使用的 [runtime_domain](../adapters/compcert-memory/GuardMemoryParamPointerProjectedCandidate.v) 要求源访问的 capability；source 的正常执行提供该证据，没有预先假设待检查的 non-alias。检查的是受限真实足迹，不是任意 allocation 的所有单元。

目标仍由核心 [guard_host](../prototype/interface/GuardInterface.v) 表达：

```text
checks G original accepted checked
select_exact: actual select ⇔ check followed by the chosen branch at checked
accepted: P(original) and accepted_entry(original,checked)
refused: refused_entry(original,checked)
```

核心已经允许私有检查状态。需要扩展的是具体 Clight 实现和与旧证书的桥接。

## 四个不能省略的义务

| 义务 | 已有证据 | 新迁移必须补的证明 | 归属 |
| --- | --- | --- | --- |
| 真正表示检查后状态 | 旧 `memory_projected_check_execution` 是真实 `exec_stmt`，包含 after temps、相同 memory、公开 agreement；normal 表示接受，break 表示拒绝。新 prefix 保留实际 scan after temps，再物化一个 result | 公共 host 的 `checks` 仍需固定这个实际关系，不能改成 `bool→initial temps` 的固定函数；result 初始化也是状态变化 | Clight 语言实例；domain 声明所用私有资源 |
| 任意检查执行都正确 | [projected_check_witness_all](../prototype/interface/ClightPrivateCheckFacts.v) 复用确定性；[原入口 facts](../prototype/interface/ClightParamPointerEntryFacts.v) 和 [prefix bridge](../prototype/interface/ClightParamPointerScanBridge.v) 已覆盖真实 scan／prefix 的全部完成执行 | 已得到 protected frame 和 `accepts⇒P(original)`；完整 `guard_certificate` 还需消费实际 host、检查安全／可用性解释和状态关系 | 语言库提供确定性／解码设施，domain 提交实际 footprint 对应、安全与完成见证 |
| 前提锚在什么状态 | 旧结论是 `P(checked)`；新 `param_pointer_presumption_temp_frame` 已证明 protected agreement 下的双向稳定，接受可运输回 original | 该实际 package 的入口锚点已关闭。新 source／footprint 若有额外观察，仍须提供依赖覆盖与 frame；仅有调用者 live agreement 不够 | domain 提交 P 的依赖与 coverage；语言提供 temp／memory frame 定律 |
| 实际分派与宿主 | 新 [private_scan_select_exact](../prototype/interface/ClightPrivateScan.v) 对所有入口、任意实际分支的 trace／outcome 证明双向 statement 分解；`private_scan_prefix_dispatch` 给出真实小步前缀 | 实际 statement 分派已关闭。仍需公共 host 实例、source／candidate 分支运输、scope／private pool、完整 Csem→Asm 与提取；完成式 lemma 不自动提供无限行为观察 | Clight 语言实例／host；优化方给局部候选与边界 witness |

`quiet_statement` 允许 `break` 与 `continue`，也允许这里的结构化循环；它排除 call、return、label、goto。不能因检查返回 break 就宣称确定性库不可复用。另一方面，quiet 仅支持完成执行的确定性，并不独自证明检查一定结束、安全或覆盖无限 source fallback。

`select_exact` 本身量化所有入口与该 host 的所有 code，不以 D 为前提。因此在 source-derived D 下构造一个完成检查见证，还不能独自证明这个语言定律。实际 check 类型或实现库还须约束检查的 memory／公开 frame、可解码出口，以及真正的控制行为；D 则用于证明安全与可用。反向分解实际 wrapper 执行时，也必须建立这些事实，不能因为 `checks` 的定义包含 frame 就视为已证。

旧 wrapper 的 switch／loop 包住了 candidate 和 source：候选的 break／continue 若被 wrapper 吸收，可能改变其控制含义。新 Boolean wrapper 已实现并证明：`result=0；一次性 loop 包围 raw check；normal 后 result=1；break 退出；if result`。分支在 loop 外，因此 exact 端点允许任意分支的完成出口，包含 break／continue／return；没有要求分支 quiet 或正常完成。raw check 则使用已证明的受限语法，无 call／return／goto／continue 或内存写。实际参数化 pointer scan 已实例化这项语法证明。

`ClightParamPointerScanBridge` 另证明 result 的初始写入可通过真实 scan 的 temp transport 运输。result 对 raw 所有读写 temps 及 protected 集 fresh；wrapper 后的 frame 保护原入口前提的依赖。compiler 安装还须核对它对 source、candidate 和公开观察 fresh，不能把这一资源义务从语言库转嫁成一个新的任意分支等价定理。

## 接口选择与实现顺序

现有 readonly 前台与 direct/shared 使用者保持。私有检查将消费一般 `guard_certificate`／`preservation_certificate`，逻辑 condition 不观察私有写入。已完成真实 witness 到所有完成执行、原入口前提稳定、result 初始化、statement exact dispatch 与小步 prefix。可用 `make interface-private-check-proof` 重现；15 个端点、392 个实际依赖和 805 份源摘要，无新增全局公理。公共 host／guard certificate、分支运输与 compiler 安装尚未完成。

下一项先实例化实际 host 和检查安全／观察范围，构造公共 guard certificate。其检查关系绑定实际 prefix 和 checked state，分别消费 D 下的完成见证、所有执行的原入口 sound 和 protected frame；不得仅给 check_safe 换成一个更弱的名字来省略语义义务。再将旧局部 candidate 证书从检查后状态运输到实际 source／target 安装位置，核对名字分配与 source progress，接 CompCert 后端并运行真实 pointer fixtures。

这一阶段首先覆盖旧指针路线的正常有限 region。小步 dispatch 前缀可以独立于分支是否完成证明；这不意味着有限 macro host 已支持任意无限指针 source。完整无限回退需要对应的 open-region 协议，和 readonly unsigned 循环已有的小步路线分别验收。

编译和审计当前 facts 已通过，后续验收依次是：构造已证明的公共证书；安装真实 pointer candidate；提取编译器；在 disjoint／alias、空源、参数范围、提前拒绝、地址回绕和私有 cursor 不同的入口运行对照；确认实际接受路径与公开出口；最后记录旧 compiler 与公共 compiler 分别复用了什么。不存在源 capability 时应回退或静态拒绝，不把危险的先行读取隐藏到 D 中。

## 与论文责任链的关系

`C_opt` 仍来自实际 pointer body／candidate checker；`C_derive` 证明足迹和所有实例的覆盖；`C_guard` 证明原子比较的机器定义性、扫描进展与接受结论；`C_host` 证明真实状态、分派、边界与上下文。三方责任和验收顺序见 [framework-responsibilities.md](framework-responsibilities.md) 与 [current-work-plan.md](current-work-plan.md)。此次定位没有把 universal assumption extraction 或一般语言的 stateful check 合成交给 kernel。
