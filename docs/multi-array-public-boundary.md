# 两数组 guarded statement 的任意 caller 边界

日期：2026-10-08。

本阶段把 [完整两数组条件](multi-array-complete-guard.md) 的局部定理扩展到
caller 指定的任意 live temporaries，并生产现有 Clight language host 所消费的
`PrivateRegion.projected_region_contract`。它没有完成新族的整程序安装。

## Narrative 核对与责任

本轮重新 fetch，`origin/topdown/research-positioning` 为
`12419c1e1e3da450bf378742a2fb4e204e51e060`；
[paper-narrative](topdown/paper-narrative.md) 与
[context-lifting](topdown/context-lifting.md) 的正文均与 main 一致。
本阶段按其澄清落实一个实际 host 边界问题，没有因设计讨论重构 kernel。

| 责任方 | 本阶段消费／提供的证据 | 后续责任 |
| --- | --- | --- |
| Framework kernel | 保持既有局部证书组合；不认识 Clight temps 或数组 | 持续区分局部组合与语言的安装定律 |
| Clight language library | 实际 AST 写集、任意 live frame、源执行运输、big-step 到 small-step、现有 projected boundary | typed 资源分配、progress、control／labels、placement、selected 安装与 backend 接线 |
| Optimizer/domain implementation | 完整条件、原源许可、足够 setup／separation、checked candidate 与 iterator restore | source family 识别／参数化、loaded 两次 store 的 header 保持与原源 prefix、真实同族 pipeline 的 factory |
| 源码使用者 | 标注 C、phase／tile 与资源选项 | 不提供缺失的 frame、模型对应或安装 simulation callback |

`C_guard` 与 `C_derive` 的区分仍有实际意义：检查 primitive 的执行安全由
语言证明；其接受足以建立模型前提及覆盖所有实际访问，由 domain 证明。
`C_host` 的局部 choice 定律也不替代完整程序的 progress／placement。

## 为什么固定 source ports 不够

源片段只用 `n,m,c,ld,alpha,i,j,k,a,b`，但 continuation 可以读取任意其他
temporary，例如 `x`。原先要求 `live` 是固定 source public list 的子集，
不能将这份定理用于 host 的整个 `program_temps`。

新的执行结论保持任意 `live`，只要求其与实际 guard 的写集不相交。
该写集为六个 pair-scan cursors 加一个 flag。它是静态 AST 的属性，不依赖
入口 counts、指针或数组值。源程序公开 iterator 的变化由既有 restore 证明
处理；它们可以属于 `live`，并不因此被当作 private。

`tensor_disjoint live private` 是编译时资源检查，不是注入的运行时 condition。
新的 checked producer 自己检查它；冲突返回 `None`，不安装 target。
成功仍要经过原 candidate checker，因此 candidate scratch 的 freshness
保留原有验证。该 producer 尚未生产 guard slots 的 typed declarations。

## 证明链与接口

1. `GuardMemoryPairScanWrites.v` 从矩形与双矩形 AST 的结构生产 `writes_only`，
   最后得到通用 `multi_tensor_pair_scan_writes`。调用者无需为动态 point 数
   枚举写集。
2. `ClightMultiTensorPublicScan.v` 将实际 guard execution 与静态 disjoint
   检查组合，导出任意 caller-live frame。将 source ports frame 与 caller
   frame 合并后，运输实际原 AST 到 scan exit，保持相同最终内存及 caller
   观察。没有要求 private temps 或整个 temp environment 相等。
3. `ClightMultiTensorPublicCandidates.v` 将该源执行与 setup／restricted
   separation 运输接到既有 checked candidate 和 iterator restore；alias
   拒绝执行相同出口的原 AST。两条分支都保持 caller 的全部 live 观察。
4. `ClightMultiTensorPublicComplete.v` 在完整 setup guard 上复用上述分支，
   并提供 `check_multi_tensor_demo_public_full_versioned live pool proposal`。
   成功输出满足完整实际 statement execution，以及现有的
   `PrivateRegion.projected_region_contract live source target`。

最后一项 contract 的内容是：给定 source 在其入口正常完成，且 target 入口与
source 入口在 `live` 上一致，在任意 continuation 下 target 有对应的有限
silent small-step 执行；出口 live 一致、memory equivalent。本阶段得到更强的
相同最终 memory，再使用现有 reflexivity 定律。它不单独证明 source 总会退出，
也不提供任意 goto／label 进入区域的合法性。

两个静态 witness 展示固定 source ports 加额外 caller temporary `301` 可通过，
而把 guard flag 放入 caller-live 会拒绝。主要执行定理量化任意 `live`，
不局限于这两个 witness。

## 仍未闭合的安装责任

本阶段仍固定 demo 的 source／private identifiers；任意 caller live 证明不等于
任意源片段或 fresh allocation 已实现。下一个 factory 应从实际 source 数据与
typed private pool 生产：AST 识别、独立 source／scratch 名称、typed allocation、
scope、progress、合法 selected site，以及 checked target 的 label/control 证据。
再消费现有 host 得到该同族的新 Csem→Asm 端点及 native/context 验收。

Loaded bounds 的两 store header 保持与原源 prefix 许可仍是独立难点；canonical
源的完整执行不能许可尚未证明对应的 loaded scan。Frame 也不能把之后才定义的
array word 前移为入口已定义值。

完整 OLO 功能与可用性仍在 active goal 中：参数化 affine domains、真实依赖、
实际 scheduling／tiling/codegen、条件推导／安全检查、整程序 fallback，以及
code size、guard work、接受域、完整成本和作者负担。这个 boundary checkpoint
不缩小目标，也不增加新族 compiler、C／Asm 或成本结果。

## 验证与复现

只编译本阶段新增模块，保留已成功的对象和 prerequisite。独立 audit 查询
所有新增 `Print Assumptions` 端点，绑定 source、objects、helpers、直接依赖和
已验证 parent closure，并比较既有 42-global compiler baseline；不运行 `coqchk`。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/compile_multi_tensor_public_guard_sources.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_multi_tensor_public_guard.py --validate
```

报告位置：`build/multi-tensor-public-guard/proof/report.json`。

四个模块的独立 audit 查询 16 个端点：8 个闭合，其他最多 14 项既有 globals，
123 项绑定加已验证 parent closure 保持旧 42-global baseline，零新增公理。
报告 SHA-256：
`2032825e50ad484019abc28b93d4f8b943c8f75a9a8ab6845f9e8df989d58a26`。
