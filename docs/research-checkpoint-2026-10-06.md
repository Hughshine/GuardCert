# 2026-10-06：首个真实多面体使用者迁入主接口

GuardCert 的主只读接口现在能消费真实的仿射／分块候选核对结果，并复用原有数组执行对应、范围／alias 证书和公开出口证明。提取后的编译器支持 direct/shared 两种 guard 实现，完整 Csem→Asm 定理已经通过。此次完成的是 named canonical rectangle 使用者的迁移；完整多面体目标继续进行。

研究方向继续遵循 [topdown paper narrative](topdown/paper-narrative.md)：小的语言无关框架与实质 CompCert 优化实例共同构成论证。框架、语言实例、优化／domain 方的验证责任见[责任矩阵](framework-responsibilities.md)，下一项验收见[当前计划](current-work-plan.md)。这些方向和验收是活动目标的持续组成部分。

## 具体实现了什么

旧 `encoded_private_rule` 的局部证书是实际 program globalenv 下的 source-to-candidate 保持。新 [readonly_preserving_clight_rule](../prototype/interface/ClightReadonlyPreservation.v) 直接消费这一方向，保留原 domain、premise、formula、候选和源写界，用已有 loaded-tree 定理得到安全、可用、只读的 condition。

双向规则和保持规则分别提供所选实际分支的执行见证，再共用 `realized_projected_selection_contract`：它处理 source 的公开 temp 运输、私有实际分派、分支执行与正常公开出口。direct/shared 继续复用同一个原条件和局部证书，私有 Boolean 的写入由 freshness／frame 和状态运输覆盖。语言无关核没有被扩展成理解 Clight、指针或多面体调度的算法。

[实际使用者](clight-polyhedral-preservation.md) 消费真实 mapped-domain／依赖或 sequence tiling／依赖核对器，编译真实 `Loop.stmt`，再安装核对过的 AST table。其完整入口为 `ClightPolyhedralCompiler.compile_preserving_polyhedral`；`compile_preserving_polyhedral_correct` 对任意候选生产器、两种 lowering 和私有资源预算给出 Csem→Asm backward simulation。源识别、候选提案和优先级属于优化方；成功替换的语义证据不依赖候选搜索可信。

## 三方责任与最难义务

| 层 | 本次新写／复用 | 当前剩余义务 |
| --- | --- | --- |
| 框架 | 复用 readonly condition、公式合成和既有证据处理；不增加另一个 abstract select | 受限可运行入口推导算法及复用／成本实证，不能由新 record 代替 |
| Clight 语言实例 | 新增保持接口与旧证书桥；双向／保持共用安装；复用两种实际 realization、private pool、scope、source progress 和 CompCert backend | 一般 affine source 对应、stateful 检查与主只读前台的边界；shared whole-loop 仍未安装 |
| 优化／domain 实现者 | 复用 named 源解码、实际数组注册表、candidate 编码、模型依赖核对和入口范围／alias 覆盖证明；新增真实候选和完整 pass 的接口 glue | 扩大参数化源／访问与 pointer footprint；证明新入口 B 覆盖整个执行的 A，保留非空接受域和拒绝策略 |

本次 87 行保持接口、103 行 named 使用者、187 行编译入口共 377 行。它们是整个文件行数，包含定义、import 和证明；不是证明负担下降的证据。实际 memory/model/dependence 定理复用旧库，优化作者未被要求重证共享分派或补一个旧核对器未交付的反方向。随后量化应统计规则专属 obligations 和新增语义证明，而非总端点数。

此例复用已有矩形领域的 `B⇒A`：入口范围、静态 layout 和实际数组分离覆盖模型控制／地址／NonAlias 义务，源解码与候选编码连接真实执行。`D` 来自实际正常源执行；在范围通过后才能取得安全基址检查所需的绑定与有效性，D 不预置 alias 前提。没有新增通用投影、最弱条件或任意 S/T 的前提发现算法。

## 已通过的验证

| 范围 | 当前结果与边界 |
| --- | --- |
| 主 CompCert-only 接口 | 415 个端点、864 份源码摘要；FRAGMENT=6、MEMORY=1、REGION=6、PROJECTED_REGION=8、STEPWISE=8、COMPILER=35，无新增公理 |
| 可选 affine／tiling 使用者 | 11 个端点，260 项实际使用者依赖，809 份源摘要；完整程序继承 CompCert 35 项加既有 PolCert/VPL 七项，无新增公理。计数与主接口有重合，不相加 |
| 提取编译器 | `build/compcert-readonly-polyhedral/ccomp`，同一个二进制用环境配置选择 direct/shared；候选通过实际核对器后才生成替换 |
| 多数组候选／拒绝 | 两种 lowering 共 40 配置，每组 4,022 行输出与 GCC 和独立源模型相同；实际 Clight 检查了候选及安全基址比较 |
| 同函数连续替换与上下文 | 两种 lowering 共 8 配置，每组 149 行相同；两个实际 region、外围 goto、跨片段 cookie、公开 counters、完整数组、空外层未初始化内层 bound 均检查；无数组访问的 `(n,m)=(13,0)/(0,11)` 是有定义的源入口但不满足模型范围，保留源回退 |
| 当前产物绑定 | proof／compiler／native stamp、全部证明／native 源、提取文件与汇编／Clight／输出摘要核对通过，见 `build/interface-polyhedral/validation.json` |

接受配置包括实际 interchange、fission、平移、剪切、组合映射、内层反转和 1×1／2×3／17×13 tiling。行前缀依赖的 fission／反转被核对器拒绝，其他合法函数继续接受。错误参数、改变／丢失域、错误映射、机器范围不合法、缺失／坏语法输入、资源耗尽和错误 LCF 证书均保留源循环。实际运行也覆盖非零起点、空／负边界下的 runtime fallback。

共享实现的实际候选和回退各一份。以三数组 cross-chain 的 interchange 为例，direct 的打印 Clight body 为 6,392 字节、八份 source loop；shared 为 2,485 字节、一份 source loop，两者候选各一份。这是这个 fixture 的 AST 观察，未测量最终符号字节或运行时间，不能推断普遍性能收益。

主证明报告 SHA256 为 `5e3ccceed72201e676ef8cfad804060dbb9f735e25413b8afd2935a08a619656`。可选使用者 proof report 为 `d9acc90015936ca23624fdf684b00383bc3fffdcdf8f69e11c5b98c5023b5a01`，其编译器为 `c33d4e6c5aa761b077b977a96b8cdbba0cc81d19960803a5f3008d06d013b889`。源码摘要数说明核对范围，不声称本轮独立编译了全部 809／864 个新模块。

原有 **25 种提取配置全部重建／回归通过，40 份报告绑定当前 415 端点／864 摘要的证明、源码和产物**。相对 `26956a4` 保存的 40 份 C／Clight 摘要全部保持；unsigned 完整循环 fixture 仍为 540 次有限调用、六处新 loop 和两处旧 preload。整体核对见 `build/interface-compiler/preservation-validation.json`，回归汇总见 `build/interface-compiler/preservation-regression/summary.json`。P1 的固定结果仍见 [10 月 5–6 日历史记录](research-checkpoint-2026-10-05.md)，不把旧报告称为绑定本次修改。

## 复现与工具链

沿用现有 Rocq/Stdlib 9.2、CompCert v3.18 和锁定 PolCert optimizer 源，不重新初始化工具链：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-polyhedral-native
```

该目标依次审计、提取、执行两份真实程序并核对产物绑定。`GUARDCERT_LOOP_CANDIDATE` 指定不受信任候选文件；`GUARDCERT_GUARD_LOWERING=direct|shared` 选择已证明的实际实现，默认 shared。独立审计入口为 `make interface-polyhedral-proof`，整个依赖闭包可用 `scripts/audit_interface_polyhedral.py --rebuild` 重编译。

恢复旧多面体依赖时发现旧 `.vo` 的 Corelib fingerprint 与当前工具链不同；已在不改变锁定源码的情况下重编译实际依赖。公共接口审计还修正文件加入顺序不等于依赖顺序的问题：`StrictIteration` 被更早列出的 matrix 模块使用。新 `rocq_dependencies.py` 按实际 owned 依赖闭包排序并重建变化项，避免使用失配对象。验证用 Rocq 编译、假设报告、实际提取和完整汇编行为，不用 `coqchk`。

## 评审更新与后续目标

本阶段重新 fetch 三个评审分支。evidence/performance SHA 保持；topdown 新增 `f7936299fa6272fbf50db6b94a1bd0333808ea09`，其 cross-IR 讨论已同步并吸收。SSA/CFG 的 phi/live-out 和汇编的 scratch/flags/控制由对应语言实例证明；Clight 继续是主验收，第二 IR 是可选表达力证据。Peek、COVE/cSTOKE、Chamois 和 CoreJIT 继续约束贡献主张；方向文档不是新文献能力核实，未核实接口继续标未知。

当前 macro host 仍要求 source 独立进展；新的多面体入口没有因此覆盖任意无限源回退。源语法是 canonical rectangle 和已有 named body／layout 证书，不包含 ragged、一般 affine 源、真实指针切片和 stateful footprint 的迁移。参数化源、访问与指针路线是下一项 P2；P3 优先实现一个受限符号条件／足迹算法，明确 `B⇒A` 的全实例覆盖、编码安全、实际非空接受和完整程序接入。多个 dependent preload 与一般布局组合也继续保留。

完整目标保持 active。此次候选核对、证书复用和真实运行通过一项迁移验收，性能、作者证明负担与文献增量仍有独立验收。
