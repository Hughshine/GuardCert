# 非矩形 pointer：独立候选到完整 Csem→Asm

2026-10-06。延续 [完整 source guard](research-checkpoint-2026-10-06-affine-pointer-alias.md)，本阶段取得一个新的实际 compiler，而非旧矩形 compiler 回归。使用者接口和 walkthrough 见 [接入说明](clight-affine-inner-pointer-compiler.md)。活动目标继续沿 [topdown narrative](topdown/paper-narrative.md) 和 [责任矩阵](framework-responsibilities.md) 推进，完整多面体 goal 尚未完成。

## 结果与证明边界

同一 source package 现已绑定独立 mapped-domain／dependence candidate certificate、validator/encoder 两套范围、实际 Clight lowering、完整最终内存和公开 i/j/k restore。[candidate execution](../prototype/interface/ClightAffineInnerPointerCandidate.v) 与 [preservation](../prototype/interface/ClightAffineInnerPointerPreservation.v) 组成实际 prefix/loop contract；[factory](../prototype/interface/ClightAffineInnerPointerCandidates.v) 检查真实 normalized source 和不受信任提案，运输 source grouping 和 quiet suffix。已有 language progress/private-pool/program host 消费这个 table，得到 [compile_affine_inner_pointer_correct](../prototype/interface/ClightAffineInnerPointerCompiler.v) 的 Csem→Asm backward simulation。

kernel 未改，继续复用 readonly condition sequencing。语言的 prefix receipt、表达式／范围编码、public frame、实际只读分派和小步安装定律未重写。domain 新增完整 context 的 width-model 连接、两套 candidate ranges、安全域和独立候选的组装及实际 compiler factory。入口类型证据仍来自真实有限正常源完成和 retained source receipt；全程序结论另消费实际 progress/scope/host，不从 big-step 条件单独推出。

实际 schedule generation 暴露 signed32 表示问题：生成检查含 `2147483648` 或 `-a`，而非单位行宽的重排边界可含除法。新候选整理器提出参数 guard 删除、interval 覆盖循环与 division-cleared affine 条件，再对整个候选做原域／依赖核对。整理器不可信、不绕过机器 lowerer，也不新增 normalization-correct 公理。该实例直接 readonly tree 拒绝时回完整源；没有新增 ragged scan 或 shared lowering。

## 形式验证和提取

工具链为 CompCert v3.18 `14d616046360a0b2611ebdfc2f98368af402e1f7`、Rocq/Stdlib 9.2.0、OCaml 4.14.1。CompCert VERSION/ASM 文本仍标 3.17。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make affine-pointer-compiler-proof
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/build_memory_compiler.py --affine-inner-pointer
```

[proof/report.json](../build/affine-pointer-compiler/proof/report.json) 记录 103 个端点，其中 9 个语言端点，533 项实际依赖、878 份源码摘要。CompCert 基线 35 项假设，继承 domain 基线另 7 项 PolCert/VPL 假设；新增全局公理为 0。独立 candidate checker sound 使用其中 12 项，实际 candidate/local execution 使用 6 项；source writes 和 endpoint encoding 闭合于全局上下文；新完整 compiler 使用继承基线的 42 项。

报告 SHA-256：`d4234ff315952b66e1569c87b8cc9b19cec3c127db164fde36d161953f0b69b7`。全部源码和 `.vo` 摘要核对当前产物。审计编译变更／过期依赖并检查选定闭包，没有请求 `--rebuild`，不是整个 CompCert 的 clean rebuild。旧 `compile_realized_observed_pointer_correct` 的假设也被核对；未重跑旧 native 矩阵。

六个新 Rocq fixture 核对实际 affine-inner source progress、normalized observation matcher、receipt coverage/缺失拒绝、便利 profile 经真实 checker 接受，以及不同迭代域的实际 Clight candidate lowering。它们与本节提取及下面真实 C frontend 证据分别记录。

## 原生和机器路径

[native C](../examples/native_affine_inner_pointer.c) 含两种真实源域 `j<i+1` 和 `j<2*i+1`，以及缺失 q receipt 的源。源保留 prefix 普通读取、公开 i/j/k/rp/rq、末尾 pointer stores 和外围全局 context。三个 pointer 关系为同 base、不同对象和同 buffer 的偏移 base。每个配置执行同一组 81 次函数调用，完整两个 20,000-word buffers 与公开状态分别对照 GCC 和独立逐点模型。

| 配置 | 实际安装 | 验证 |
| --- | --- | --- |
| triangle mapped | 三角域列优先候选 | 81 次完整结果匹配 |
| ragged mapped | 第二个域的 affine-guarded 列优先候选 | 81 次完整结果匹配 |
| schedule generation | 两个域均生成、整理、重新核对并安装 | 81 次完整结果匹配 |
| raw ceiling bound | 原 affine extractor 拒绝，源保留 | 81 次完整结果匹配 |
| invalid domain | 少执行一行的错误候选拒绝 | 81 次完整结果匹配 |
| oracle resource limit | `GUARDCERT_FM_ROWS=0`，源保留 | 81 次完整结果匹配 |

共 486 次配置内调用；六个配置均由最终提取编译器新编译。它是该受限源的功能矩阵，调用数量不代表更一般优化支持或性能收益。[native/report.json](../build/affine-pointer-compiler/native/report.json) 绑定 compiler/proof/stamp/C/Clight/assembly/binary/output 摘要。[validation.json](../build/affine-pointer-compiler/validation.json) 还核对当前 proof objects、提取脚本、Driver、构建脚本、native producer 和验证脚本。

| 最终产物 | SHA-256 |
| --- | --- |
| compiler | `06c5d316008e3b486f56586676ebca555ee9b22de43a89391b49602d2cec051b` |
| native report | `dc5f03bb7008f52066058817869b64df8e9cfcb15c855be556240a45bf50b756` |
| extraction stamp | `c48c9ece2ec29b0eccb887ce43b3776f04a19eae118656021296c8a6988d9a33` |
| validation report | `c1c0b6f303b77ad67d7669176dae737837c93fe1ec646de770163cdaa727a197` |

五个 GDB linked-machine 探针分别观察 triangle 接受、偏移 alias 拒绝、同-base 包络相交拒绝、第二个域接受和 generated schedule 接受。候选先写 `p[160]` 再写 `p[97]`；原源顺序相反。真实 alias 反例的源 `p[97]=4660`，无条件重排模型为 `4723`；机器回退保留 `4660`。此前设计记录中的 `p[65]` 是索引笔误，实际绝对下标为 4597，本次已修正设计文档。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_affine_inner_pointer.py
python3 scripts/validate_affine_inner_pointer.py
```

沙箱禁止 `ptrace` 的首次 GDB 运行失败；六个功能配置当时已经通过。随后在允许调试的环境完成并用最终报告/stamp 重新绑定全部配置和五个探针，最终报告为 passed。调试用的临时提取源码已由最终正式 extraction 替换，未用于最终证据。

## 下一项验收

同一非矩形 pointer package 的 quotient/tiling 证书、一般深层 affine 源、多个有依赖 preload 的合法观察与参数稳定性继续是功能目标。源不同 base 的符号拒绝仍保守；如加入第二次扫描机会，必须枚举真实 ragged 域并证明 capability/private-state 运输。未取得性能、同例作者证明负担或 novelty 结论。新增 876 行 Rocq 源及端点数是审计范围，不计贡献或复用收益。
