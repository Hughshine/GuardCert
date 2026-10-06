# 2026-10-06：同一 pointer 条件的共享 fallback

接续 main `00b9dbfb53e35b305a51e842f6a0ed47a13794fa`。本轮安装真实共享控制实现，并把原 observed pointer pipeline 参数化最后 realization；没有另复制一个 shared optimizer。完整目标保持活动。证明审计、提取、两个完整十五配置原生矩阵和二十个实际机器路径探针全部通过；本记录冻结当前阶段，不将其当作一般 affine pointer 域或完整目标完成。

## 实际入口和三方责任

入口 [compile_realized_observed_pointer](../prototype/interface/ClightObservedPointerCompiler.v) 对 `shared: bool` 量化；正确性端点 `compile_realized_observed_pointer_correct` 给出 Csem→Asm backward simulation。一个提取 compiler 按 `GUARDCERT_GUARD_LOWERING=direct|shared` 选择，默认 shared，其他值拒绝。原 `compile_preserving_observed_pointer` 是 false 的兼容入口。

| 责任 | 新交付与复用 |
| --- | --- |
| 框架 | kernel 没有改变；继续消费原 guard、conditional preservation 和组合定理 |
| Clight 语言实例 | [ClightPrivateScanShortcutRealization](../prototype/interface/ClightPrivateScanShortcutRealization.v) 新增实际正常执行运输与 direct AST 定义相等；消费既有 tree execution exactness／shared control。复用 source receipt、scope／private frame、sequence contract／progress 和完整 backend |
| 优化／domain 实现者 | 原四个 observed preservation／candidate／candidates／compiler 模块参数化 realization，旧 API 用 direct 别名保留。source matcher、原三类 candidate checker、C_opt、affine 全点与 footprint coverage、条件编码不复制、不重证 |

语言服务以 `readonly_tree_execution_exact` 获得真实 decision path 和被选择分支，再用 `shared_guarded_statement_execution` 构造同 temps／memory／normal outcome 的实际共享执行。原 private scan 的私有游标与 result 继续消费原 certificate。没有新 materialized Boolean 或额外 scratch，池保持 17 槽。

这关闭一个具体控制实现义务，不是一般 abnormal exit／divergence 下的新 abstract select law；适用范围是 finite silent normal region。语言层证明新控制的执行，domain 层只改变目标构造的最后一步，kernel 不读取 Clight／pointer／polyhedral 语义。源码复用是可核对的事实；尚未做总 proof-burden 或作者时间的同例测量。

## 证明与工具链

共用入口审计通过 79 个公开端点（语言 35／domain 44），503 项实际 user closure，850 份源码摘要。语言端点不超出 CompCert 35 项基线；完整 domain／compiler 继承原 PolCert/VPL 七项假设，没有额外全局公理。端点新增包含旧 API／generic aliases，不将数量增长解释成能力增长。

本轮编译一个新语言模块及四个变更模块、必要依赖并进行实际 closure／源码绑定审计；不是 clean rebuild 整个 CompCert。随后实际 extraction、OCaml build／链接通过，新 compiler 由独立 stamp 绑定。

工具链继续锁定 CompCert v3.18 commit `14d616046360a0b2611ebdfc2f98368af402e1f7`、Rocq／Stdlib 9.2.0、OCaml 4.14.1，见 [lock](../toolchain.lock.json)。tag 的 VERSION 文件仍为 3.17，以实际 tag／commit 为准。

| 产物 | SHA-256 |
| --- | --- |
| `build/interface-pointer-realization/report.json` | `120d0315ea98db0fea5fd81c867b2a959cafcdb7bd8fe8c03e37f9ba538414fe` |
| `build/compcert-pointer-realization/.guard-build.json` | `5739e8e48e2557bf810b03edfdd7e37a90768766bcf2c1f0b4391cc731065708` |
| `build/compcert-pointer-realization/ccomp` | `babb69d31a6eb33df60a844b289dd5ae0cd259f793a3048afb12d4ea6bfb7180` |
| `build/native-interface-pointer-realization/shared/runtime-path-report.json` | `8e459195f4646b91a0dcbc45365b35bf8fabfef586a09cd5d5bc47120d98d7c7` |
| `build/native-interface-pointer-realization/direct/runtime-path-report.json` | `8c546edee27ea5736be0b5d17eb79b3a23b896cbcd06e2fdefcb2ea677b1a2a1` |
| `build/native-interface-pointer-realization/shared/report.json` | `be3feb3ec0a52df6b23d3abe499602c23625f95d466dfe092b83aaf910a3aab3` |
| `build/native-interface-pointer-realization/direct/report.json` | `a5cda9b5a864c3175177021d07239ee8d2b3d88cd3dd39100c70add986a32b77` |
| `build/interface-pointer-realization/shared-validation.json` | `0ec2d9d33e1d963a07bd16dbf4f79d430960aec16fb2f1f9e7332a0319eeb770` |
| `build/interface-pointer-realization/direct-validation.json` | `87ac856c661834492ce4ebbfc364a4e9f5bae554d2dfd5eaed3300f54f392890` |
| `build/interface-pointer-realization/comparison.json` | `756282441cae60ca9f9c8e116581775fc8376076b0c02b1810d3a8e2800969bd` |

源 fixture SHA-256 保持 `bb62918974f0d39c88b5bcd578cf4636d3969f0638c76b7ab7326361c75b992b`；当前 native 脚本为 `56066478bf258056acceeb8b11ced970cd709c39d9b73ef64df14f7a535f77a2`，probe 为 `8de4a1251863d750ed3f86d9063d3abcb81a1a2459beaa35519afe51d3100866`，比较脚本为 `bc4082cf65128732e79ebdac8f2efaaa296a8b239cf8e0eaaabec8aa3c560830`。报告绑定当前脚本及所有产物，比较另绑定冻结 baseline report。

## 完整程序与实际机器路径

同一 [完整 C fixture](../examples/native_interface_observed_pointer.c) 有七个函数、一／二／三维、分组／条件包围、缺失／破坏观察许可和普通后缀 store。每个配置执行同一组 376 次源调用，对照独立 modular word 模型与 GCC `-O0 -fwrapv`；核对两份完整 4096 单元 buffer、公开 i／j／k、prefix 读值和外围 effect。

两种模式的完整十五配置全部通过：一／二／三维 mapped、实际 schedule generation 后重新核对、`2×3` 与 `17×13` tiling，以及五种静态拒绝。每种模式 5,640 次配置内调用，两种共 11,280 次；唯一源输入集合仍是同一组 376 次。全部三十个配置在本轮新编译／执行，没有使用旧阶段产物恢复。编译预算保持显式 1800 秒，超时仍失败，本轮没有超时或删减配置。两个模式的完整 output、proposal 和静态选择一致；共享模式所有选中快捷条件的函数均只有一份 scan。

二十个 linked-machine 探针全部通过：每种模式的 direct／schedule interchange 各五种入口。实际 disassembly、GDB instruction breakpoints／硬件 watchpoints 和 report 绑定二进制／命令／日志，验证路径和真实写入顺序。

| 每种模式、每个 interchange 配置的入口 | base 比较次数 | scan 地址比较次数 | 实际执行 |
| --- | ---: | ---: | --- |
| 同 base／包络分离 | 2 | 0 | 候选 interchange |
| 包络重叠 | 1 | 112 | scan 后源顺序 |
| 不同分配／实际分离 | 1 | 32 | scan 后候选顺序 |
| 移位 base／实际 alias | 1 | 32 | scan 后源顺序 |
| 空源条件分支，p／q 为 null | 0 | 0 | 保留空路径 |

这些是当前 x86_64 fixture 的机器路径证据，不是一般 probe 分类定理。两个 full suites 并发运行，未采集受控时间；编译诊断 budget 和最终 bytes 不构成性能测量。

## 静态代码规模与历史绑定

已通过的 `direct-interchange-2` 中，同一 `observed_flat2` 的产物为：

| 指标 | direct | shared |
| --- | ---: | ---: |
| scan AST 副本 | 13 | 1 |
| 打印 Clight 函数体字节 | 109,608 | 13,907 |
| linked 函数 symbol 字节 | 11,750 | 1,566 |

全部十五配置的 direct Clight dump 与冻结 `00b9dbf` 摘要相同；比较脚本绑定 source／proposal／compiler／proof／完整输出和实际 linked symbol。共享模式只保证原 scan 一份，候选可能仍出现在多个接受叶子；两个对称访问对的 base 比较保留。没有运行时间、一般代码规模或总证明负担收益的主张。

`00b9dbf` 当时的四份审计／native／probe／validator 脚本、proof／compiler stamp／native／path／validation 报告按原摘要保存在 `build/history/00b9dbf-observed-pointer/`，旧 compiler 和 native 产物保留。当前四个 proof sources 参数化之后，旧报告属于冻结提交，不能作为当前源码绑定；新 factory 使用独立目录，不覆盖旧证据。

## 评审、未完成项与下一阶段

本轮重新 fetch，三分支维持 `f7936299fa6272fbf50db6b94a1bd0333808ea09`、`9673381676e18ed0afbc6114e0a62bea9c48002c` 和 `3e9f0080def8c029cceedbd35184b4de7b8b96bc`，没有新增意见。用户要求的 topdown narrative／三方责任继续纳入 [活动计划](current-work-plan.md) 和 [责任矩阵](framework-responsibilities.md)。本阶段以实际 lowering、同一管线和机器产物回应复用／成本问题，不从计数或 shared 名称推导 novelty。

condition 仍仅在同一实际 raw base 且包络分离时快捷接受；其他情况保留原 scan。source 仍是受限矩形、稳定 register counts／非负参数 package；新 realization 不扩大其条件或源域。多个依赖 preload、一般 affine pointer 源、对称条件去重、共同候选出口、同版原 CompCert 性能和同例作者负担比较仍未完成。

下一项 [非矩形 pointer 域设计](affine-pointer-domain-next.md) 明确实际源／候选、全部访问覆盖、检查安全和公开出口分别由谁证明；尤其区分可用盒包络作保守分离推导，与不能扫描源未访问的盒中额外位置。完成标准仍为实际 checker、Clight 执行、Csem→Asm、提取和完整程序验收；新 helper 或文档不计完整多面体目标完成。
