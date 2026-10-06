# 循环式私有检查：公共接口迁移的证明缺口

2026-10-06。本文是下一项实现规格，不是已经完成的新 pass。现有 pointer 扫描和对应 compiler 在旧路线中已有证明；参数化 readonly 使用者的真实迁移见 [ClightParametricCompiler](../prototype/interface/ClightParametricCompiler.v)。这里说明为何不能把旧扫描简单改名后接入同一个 tree realization。

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
| 真正表示检查后状态 | 旧 `memory_projected_check_execution` 是真实 `exec_stmt`，包含 after temps、相同 memory、公开 agreement；normal 表示接受，break 表示拒绝 | 用关系描述 `original→checked`；不能把扫描游标限制为 `bool→initial temps` 的固定函数 | Clight 语言实例；domain 声明所用私有资源 |
| 任意检查执行都正确 | 旧 `memory_param_axis_pointer_guard_execution` 给出一个完成的执行及接受后前提；新增 [projected_check_witness_all](../prototype/interface/ClightPrivateCheckFacts.v) 复用确定性／解码，[param_axis_pointer_guard_all_executions](../prototype/interface/ClightParamPointerCheckFacts.v) 已证明实际 scan 的 quiet 语法并实例化 | 已关闭该实际 scan 的所有完成执行接受结论，前提仍锚在 checked；完整 `guard_certificate` 的原入口结论和实际 host 尚待接入，不能把这四个局部端点计作 pointer pass 完成 | 语言库提供确定性／解码设施，domain 提交安全与可完成见证及实际 syntax 证明 |
| 前提锚在什么状态 | 旧接受结论是 `P(checked)`；公共证书要求 `P(original)` | 证明 header、bound／parameter／scalar context、pointer bindings 和受限 footprint 对检查的 private writes 稳定，或显式提交更一般的 representation transport。只有 `temp_agree live` 时，live 必须覆盖这些观察依赖 | domain 提交 P 的依赖与 coverage；语言提供 temp／memory frame 定律 |
| 实际分派与宿主 | 旧 [memory_sequential_guarded_projected_execution](../adapters/compcert-memory/GuardMemoryProjectedCondition.v) 提供检查＋正常分支到真实 wrapper 执行的引入方向 | 证明公共 `select_exact` 的两边；复用或重证真实 wrapper 控制流。只得到引入方向不能改称 exact。后续还需 source／candidate 的分支运输、作用域／私有分配、完整 Csem→Asm 与提取运行 | Clight 语言实例／host；优化方给局部候选与边界 witness |

`quiet_statement` 允许 `break` 与 `continue`，也允许这里的结构化循环；它排除 call、return、label、goto。不能因检查返回 break 就宣称确定性库不可复用。另一方面，quiet 仅支持完成执行的确定性，并不独自证明检查一定结束、安全或覆盖无限 source fallback。

`select_exact` 本身量化所有入口与该 host 的所有 code，不以 D 为前提。因此在 source-derived D 下构造一个完成检查见证，还不能独自证明这个语言定律。实际 check 类型或实现库还须约束检查的 memory／公开 frame、可解码出口，以及真正的控制行为；D 则用于证明安全与可用。反向分解实际 wrapper 执行时，也必须建立这些事实，不能因为 `checks` 的定义包含 frame 就视为已证。

旧 wrapper 的 switch／loop 还包住了 candidate 和 source：候选的 break／continue 若被 wrapper 吸收，可能改变其控制含义。它已有正常分支的引入证明；若拿来实例化面向任意 code 的公共 host，必须处理这个区别，或明确限制 host 的 code／观察范围。下面的新 Boolean wrapper 把分支放在检查 wrapper 外，能避免这种额外控制耦合；其 exact 证明和实际分配／运输仍需完成。这些限制属于语言实例，不能靠每个优化者重新补一个 abstract if 定理来隐藏。

## 接口选择与实现顺序

先保留现有 readonly 前台与 direct/shared 使用者。新增 private-check 使用者消费一般 `guard_certificate`／`preservation_certificate`，不改变只读 condition 的语义。对扫描使用者，首个 proof milestone 是“真实完成见证＋quiet 确定性 ⇒ 所有完成检查执行的解码与结论”，随后证明原入口的前提稳定。语言 lemma 和真实参数化 pointer scan 实例化均已编译并单独审计，可用 `make interface-private-check-proof` 重现；四个端点、388 个实际依赖和 801 份源摘要，无新增全局公理。公共 guard certificate／exact host／compiler 安装尚未完成。这些步骤均须绑定真实 scan，不能只加入待实例化的 record。

分派先评估旧 wrapper 能否提供 exact 定律；避免在尚未关闭这个义务时重写所有 scans。若采用“result=0；一次性 loop 包围 raw check；normal 后 result=1；break 退出；if result”的新实现，需要把 result 分配的初始写入也纳入状态运输。result 必须对 raw check、两个分支和公开观察均 fresh；仅证明它对 candidate fresh 不够。不得要求调用者把 raw check 的执行当作纯 Boolean。

这一阶段首先覆盖旧指针路线的正常有限 region。小步 dispatch 前缀可以独立于分支是否完成证明；这不意味着有限 macro host 已支持任意无限指针 source。完整无限回退需要对应的 open-region 协议，和 readonly unsigned 循环已有的小步路线分别验收。

实际验收依次是：编译和审计 check facts；构造一个已证明的公共证书；安装真实 pointer candidate；提取编译器；在 disjoint／alias、空源、参数范围、提前拒绝、地址回绕和私有 cursor 不同的入口运行对照；确认实际接受路径与公开出口；最后记录旧 compiler 与公共 compiler 分别复用了什么。不存在源 capability 时应回退或静态拒绝，不把危险的先行读取隐藏到 D 中。

## 与论文责任链的关系

`C_opt` 仍来自实际 pointer body／candidate checker；`C_derive` 证明足迹和所有实例的覆盖；`C_guard` 证明原子比较的机器定义性、扫描进展与接受结论；`C_host` 证明真实状态、分派、边界与上下文。三方责任和验收顺序见 [framework-responsibilities.md](framework-responsibilities.md) 与 [current-work-plan.md](current-work-plan.md)。此次定位没有把 universal assumption extraction 或一般语言的 stateful check 合成交给 kernel。
