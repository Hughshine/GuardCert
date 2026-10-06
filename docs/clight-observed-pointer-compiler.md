# 源观察 alias 包络的完整编译入口

本实现接续 [片段包络证明](source-observed-affine-separation.md)。新入口是 [compile_preserving_observed_pointer](../prototype/interface/ClightObservedPointerCompiler.v)：实际 Csyntax 经过 CompCert 的 SimplExpr／SimplLocals 后，定位真实源读取、循环和安静后缀，生成已核对替换表，再由 private-region 宿主与 CompCert backend 产生 Asm。`compile_preserving_observed_pointer_correct` 的结论是 Csem→Asm backward simulation。

审计、运行路径、报告摘要、超时和未完成项见 [本阶段记录](research-checkpoint-2026-10-06-observed-compiler.md)。

## 使用与证书边界

优化 proposer 沿用原 `pointer_preserving_request` 和 `PointerMappedProposal`／`PointerTilingProposal`／`PointerScheduleProposal`。它提交不受信任 Loop、仿射 reindex 或 schedule；新入口仍消费原依赖 checker 的正确性证书，不通过 C 层模型之外的另一个 validator。当前原生适配器也沿用 `GuardPrivateScanCandidate.propose`。

[ObservedPointerSyntax](../prototype/interface/ClightObservedPointerSyntax.v) 展开真实 `Ssequence`／`Sskip`，识别最前面连续的普通 signed int32 load，再提出一个循环和剩余后缀。类型／属性完整的 AST equality 绑定重组前后的全部语句；原 load 保留，suffix 保留所有 effect。缺少 pointer 覆盖、prefix 输出破坏 pointer binding、循环前另有修改，均不能产生这个快捷条件。未取得新证书的普通循环仍可走已证明的原扫描入口。

后缀可以含普通 store、temp 更新及受支持的嵌套循环，但这个有限片段接口要求它安静、正常退出；calls、returns、labels 等由外围程序宿主处理。如果定位结果包含这些控制形式，本服务拒绝该组合片段，不把完成执行的 contract 当成任意控制上下文的证明。

例如 [完整 C fixture](../examples/native_interface_observed_pointer.c) 的 `observed_flat2` 保留 `rp=*p; rq=*q`，循环写 `p[32+16*i+j+t]`、读 `q[127+16*i+j+t]`，随后输出公开游标／源读取值并修改 `p[0]` 与 `q[0]`。同 base 且包络分离时快捷接受；重叠或不同 base 时保留原 scan。缺 q 观察的 `observed_missing2` 与读取后修改 q 的 `observed_clobber2` 只能使用原扫描。`observed_linear1` 和 `observed_three3` 分别使用一维、三维真实源；它们通过相同接口，而不是单独的整数模型。具体 scope 仍是原受限矩形 pointer package、稳定寄存器 counts 和非负入口参数范围，不是一般 polyhedron。

## 三方验证责任

| 提供者 | 本轮工作与复用 |
| --- | --- |
| 语言无关框架 | kernel 未修改；接受、拒绝和候选保持继续消费同一 `guardify_preservation`，有限 rewrite 的组合定理复用 |
| Clight 语言实例 | [SequenceContracts](../prototype/interface/ClightSequenceContracts.v) 运输实际序列重组和 scope，以 public temp agreement／memory equivalence 保持后缀；[SequenceProgressSelector](../prototype/interface/ClightSequenceProgressSelector.v) 组合已有 framed protocols，证明前缀＋循环＋后缀的 placement progress。private names、globalenv、continuation 和后端 simulation 复用 |
| 优化／domain 实现者 | [ObservedPointerCandidates](../prototype/interface/ClightObservedPointerCandidates.v) 把三类候选接到原 checker 与新 prefix receipt／alias 包络，并把 checked profile、实际 source AST 和新 target 绑定。`C_opt`、源模型对应及全部访问的 `C_derive` 继续使用已证明 domain 库 |

最有难度的连接没有由抽象 if 替代：观察许可来自实际源读取，B 覆盖所有 A 来自原 source footprint 定理与仿射包络，真实 placement 来自语言 progress protocol。第一版接入的运行验收发现，旧 placement classifier 只接受根部是循环的 region，因而安静的 prefix／suffix 组合虽然有 contract，仍被保守拒绝。修正使用已有 sequence/framed 协议；没有对 source progress 新增假设，也没有放宽 host 的语义要求。

## 复现

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-observed-pointer-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-observed-pointer-runtime-paths
```

第一项审计实际依赖、假设和源摘要，提取新 compiler，比较完整数组、公开游标、prefix 值与外围 effect。第二项对实际 linked instructions 和硬件观察点做路径验收。proof audit、extraction stamp、native report 与路径报告分别绑定；这些功能检查不计性能证据。

本阶段十五个配置各执行同一组 376 次完整调用（共 5,640 次）和十个机器路径探针全部通过；审计 67 个端点，没有额外全局公理，继承 CompCert 35 项与原 PolCert/VPL 七项基线。详细来源与摘要在 [阶段记录](research-checkpoint-2026-10-06-observed-compiler.md)。

首轮矩阵的前八个配置通过，`tile-2-3` 超过原脚本 600 秒编译预算；日志保留在 `build/interface-observed-pointer/native.log`，不能把这轮 partial report 当作全矩阵通过。新脚本给此入口显式的 1800 秒诊断预算，超时仍失败并写 `compile-timeout.json`。`--reuse-passed-report` 只用于恢复有完整源码、compiler／proof、proposal 和二进制摘要的已通过产物，重新执行全部调用并重新核对 AST／输出；报告标明各配置是本轮编译还是旧产物重执行，保留原 driver 摘要。默认命令重新编译全部配置，恢复不构成 clean rebuild 证据。

本阶段的直接 tree lowering 会在多个拒绝叶子复制原 scan AST。`observed_flat2` 的 interchange 配置出现 13 份 scan；接受路径也保留两个方向的访问对，所以要比较 base 两次。这些是实际 AST／指令路径的事实，不是时间测量。下一项复用已有的 [共享 fallback 设施](../theories/ClightSharedRegion.v) 或 [实际 realization](../prototype/interface/ClightGuardRealization.v)，证明新的实际 lowering，再处理对称访问对的冗余；不能在计时中用手工删减的代码替代 proved entry。一般 affine pointer 域、多个依赖 preload、同版原 CompCert 对照和作者证明负担仍在 [完整计划](current-work-plan.md)。

## 下一项的明确证明切口

先使用不增加 scratch 的 `shared_guarded_statement Q candidate original_scan`：它以 switch 捕获拒绝、以单次 loop 捕获候选完成后的 continue，只保留一份 scan；候选仍可能在多个接受叶子重复。语言证明可以由 `readonly_tree_execution_exact` 从已完成 direct tree 执行取得相同入口的 decision path 和选中分支，再由 `shared_guarded_statement_execution` 构造真实共享 AST 执行，保持原 trace、temps、memory 与正常出口。此服务只覆盖有限 silent normal fragment，不宣称实现任意控制出口下的 abstract host。

优化适配器继续消费 `checked_pointer_scan_rule_witness`，将原 candidate／scan 和新共享 AST 绑定；不重新验证 schedule 或证明 B⇒A。source-prefix receipt、quiet suffix、序列 placement、public scope 与后端保持复用，框架 kernel 无变化。验收必须是新的实际 compiler entry／提取及同一组输入，不停在语言 helper。若随后共享候选和回退两个出口，应另取得 materialized Boolean 的 freshness／状态运输证据，不能直接复用原 scan result 并假定它对 scan body fresh。

快捷条件目前只在实际原始 pointer 相等、offset 包络分离时接受；不同分配或不同 base 即便实际无 alias，也继续原扫描。源 load receipt 解决定义性，不提供任意数组的布局 metadata。扩大这项接受域需要另一个可执行条件算法／语言原语和 soundness，不从 `p!=q` 推出区间分离。这是条件表达力与实际成本的后续边界。

## 后继：共用的 direct／shared compiler factory

上述阶段的 proof／native／超时记录固定于 `00b9dbf`；其脚本和报告已归档，原二进制保留。[共享回退使用者](clight-shared-pointer-shortcut.md) 现已实现前节的证明切口，并把既有 source matcher、三类候选管线和保持定理参数化最后 realization；旧入口是 `shared=false` 的兼容别名。新实际入口 `compile_realized_observed_pointer` 对 direct／shared 都有 Csem→Asm 正确性，使用独立编译器和报告目录。新语言服务只覆盖有限 silent normal region，不扩大条件接受域、源域或宿主控制出口。审计／提取、两个完整十五配置矩阵和二十个机器路径探针全部通过，见 [新阶段记录](research-checkpoint-2026-10-06-shared-pointer.md)；不能将上一阶段 stamp 算作当前修改源码的绑定。
