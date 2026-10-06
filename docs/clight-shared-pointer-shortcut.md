# 同一 pointer 条件的 direct／共享回退实现

本阶段接续 main `00b9dbf` 的 [源观察编译入口](clight-observed-pointer-compiler.md)。不改变 source、candidate、D／P、affine 包络条件或原 footprint scan；新增的是一个 Clight 控制实现和共用 compiler factory。证明审计、提取、两个完整十五配置矩阵和二十个机器路径探针全部通过，证据与摘要见 [新阶段记录](research-checkpoint-2026-10-06-shared-pointer.md)。

## 用户与三方责任

使用者继续给原 `pointer_preserving_proposer`：mapped Loop＋reindex、tile sizes，或 affine schedule＋reindex。`compile_realized_observed_pointer shared propose private_count program` 接实际 Csyntax；`shared=false` 是原 direct tree，`shared=true` 共享拒绝后的完整 scan。正确性端点 `compile_realized_observed_pointer_correct` 对两个值都量化，结论仍为 Csem→Asm backward simulation。

| 责任 | 本轮交付 |
| --- | --- |
| 框架 | kernel 未变，接受／拒绝及 local preservation 仍消费原证书和组合定理 |
| Clight 语言库 | [ShortcutRealization](../prototype/interface/ClightPrivateScanShortcutRealization.v) 把真实 direct-tree 的正常执行运输到共享 AST，保持 trace、temps、memory 和正常出口；`shared=false` 与原 AST 定义相等。复用已有 shared control、scope、prefix／suffix、source progress 和 backend |
| 优化／domain 方 | 已有 [候选适配器](../prototype/interface/ClightObservedPointerCandidates.v) 参数化最后的 realization；三类 checker、profile search、source matcher、C_opt、B⇒全部访问义务和实际 guard 编码只有一份。旧公开名称是 direct factory 的兼容入口，未复制一套共享 optimizer 或重证数学正确性 |

共享实现是 `shared_guarded_statement Q candidate original_scan`。只读 Q 的 true 叶子执行 candidate 后 continue；switch 将 false 叶子的 break 捕获为正常完成，随后执行唯一一份原 scan；外层单次 loop 的增量 break 统一退出。语言证明通过 `readonly_tree_execution_exact` 取得真实 decision path／选中分支，再消费既有 `shared_guarded_statement_execution`。不新增 materialized Boolean 或私有槽，private count 仍为 17。

这是有限 silent normal region 的服务，不是所有异常出口／发散下的新 abstract select law。原 scan 的 result／cursor 写入仍由原 private host 证明；新 macro 不要求复用 scan result 作 fresh guard Boolean。观察许可仍来自源 p[0]／q[0] load，快捷接受仍只覆盖同 base 且 offset 包络分离；这里没有扩大 condition 表达力或 pointer 源域。

## 完整验收与静态代码规模

共用入口审计通过 79 个端点（语言 35／domain 44），503 项实际 user closure，850 份源码摘要；基线保持 CompCert 35 项＋原 PolCert/VPL 七项，没有额外全局公理。本轮编译变更模块和必要依赖，没有声称 clean rebuild 整个 CompCert。新 compiler 已提取／链接，来源报告在 `build/interface-pointer-realization/report.json` 和 `build/compcert-pointer-realization/.guard-build.json`。

两个完整十五配置矩阵全部新编译并执行，每个配置是同一组 376 次完整源调用；共 11,280 次配置内调用，唯一源输入仍为 376 组。每个结果均与独立模型／GCC reference 一致，两种模式保持相同实际源选择和候选。`observed_flat2` 的实际产物为：

| 指标 | direct | shared |
| --- | ---: | ---: |
| 原 scan AST 副本 | 13 | 1 |
| 打印 Clight 函数体字节 | 109,608 | 13,907 |
| linked `observed_flat2` symbol 字节 | 11,750 | 1,566 |

全部十五配置的 direct Clight dump 与冻结 `00b9dbf` 摘要一致。上表只报告其中一个配置的静态代码规模；完整比较报告绑定各配置／函数的实际 symbol 字节与完整输出。候选仍可能出现在多个接受叶子，两个对称访问对的 base 测试也没有删除；没有运行时间测量。

运行矩阵覆盖同一七个真实函数、一／二／三维源、完整 buffer、公开出口、prefix 值、后缀 store 和外围 context。每种模式十五个配置各 376 调用；另外使用实际 GDB 指令断点／硬件观察点核对两种模式的快捷接受、scan 接受／回退和空路径。比较脚本核对 source／proposal／compiler／proof／完整输出绑定、静态选择及 linked symbol 大小；可另外核对冻结 baseline 的全部 direct Clight 摘要。比较与最终源码／proof／compiler／native／path 绑定验证均通过；两个完整矩阵全部本轮新编译，没有旧产物恢复。

## 复现与证据边界

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-pointer-realization-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-pointer-realization-runtime-paths
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-pointer-realization-direct
```

同一个 compiler 默认使用 shared；`GUARDCERT_GUARD_LOWERING=direct` 选择 direct，其他值拒绝。两个模式使用同一 proposer／backend 和 17 槽池。原独立入口 `compile_preserving_observed_pointer` 保持 direct；本阶段不自动把该源码特有服务加入所有 common-pass 规则。

`00b9dbf` 的历史 proof／compiler stamp／native／path／validation 和当时脚本已按原摘要保存在 `build/history/00b9dbf-observed-pointer/`；原 native 二进制与 dump 保留。它们是冻结提交的证据，当前四个参数化 proof sources 改变后，不将旧 stamp 宣称为当前源码绑定。新 factory 使用独立 build／报告目录，不覆盖旧阶段报告。完整性能测量、一般 affine pointer 源、多个依赖 preload 和作者负担比较继续按 [当前计划](current-work-plan.md) 验收。
