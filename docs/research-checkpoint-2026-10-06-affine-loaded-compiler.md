# 参数化 memory-loaded affine compiler：真实 C 到原生执行

这是 [固定 profile 安装](research-checkpoint-2026-10-06-loaded-placement.md)
的后继阶段。新入口不绑定 fixture 标识符，从实际 source AST 中取得
iterator、bound pointer、已有 snapshot 和 checked cached model。
`compile_guarded_affine_loaded_correct` 给出 Csem→Asm backward simulation，
提取和真实 C 上的候选／回退／静态拒绝均已运行。完整目标继续 active。

当前覆盖的是受限两层 affine-inner 源、旧 checker 已支持的 memory body
及 mapped、tiling、schedule proposal。Bound 是写缓冲区的逻辑单元 0，
snapshot 来自保留的 source public load；没有自动插入 private cache，
也没有安装独立 bound-buffer 的动态稳定性条件。

## 一个实际输入及证明链

[C fixture](../examples/native_affine_loaded_pointer.c) 中包含：

```c
rq = *q;
snapshot = *p;
rp = *p;
for (; i < *p; ++i) {
  k = i + 1;
  for (j = 0; j < k; ++j)
    p[32 + 64*i + j] = q[4096 + 64*i + j] + a;
}
```

Snapshot 是 prefix 的第二次读取。另一个函数使用不同实际标识符和
`k = 2*row + 1`。候选由外部文件提出；编译器不信任 profile、schedule
producer 或候选 normalization。

1. [source selector](../prototype/interface/ClightAffineLoadedSourceSyntax.v)
   核对 observed prefix/loop/suffix、loaded header、cached source/model equality、
   metadata、snapshot receipt 和静态 write exclusion。Prefix outputs 必须唯一，
   不能覆盖 pointer binding。没有相应 receipt 时静态保留原 source。
2. 语言 [preload snapshot service](../prototype/interface/ClightPreloadSnapshot.v)
   从任意 prefix 位置的真实读取取得 final-entry value/load 一致性；
   它尚未推断未来 loads 稳定。Source observations 提供实际 base pointer
   比较的许可，不能用 `p+k` 的权限冒充 base 许可。
3. Domain 的 [loaded source evidence](../adapters/compcert-memory/GuardMemoryAffinePointerLoadedDomain.v)
   从实际 header 和第一轮 body 生产 word 读取证据。
   [preparation interface](../prototype/interface/ClightAffinePreparationEvidence.v)
   接收这些证据，依序检查 header、width 和 body geometry/scalars 范围。
4. [cache transport](../adapters/compcert-memory/GuardMemoryAffinePointerLoadedCache.v)
   在接受的坐标／参数范围内，将所有实际 writes 归入已验证 affine 足迹，
   排除观察单元，推出 `Mem.loadv` 保持，再把原 loaded source 执行运输到
   checked cached source。D 没有预置未来稳定性；静态 exclusion 不调用 ghost
   权限或在运行时假设别名消失。
5. [local rewrite](../prototype/interface/ClightAffineLoadedRewrite.v) 用原
   `sequence_readonly_conditions` 将新的 preparation 接到已有 candidate guard。
   Candidate checker 的独立证书、两套表示范围、实际 lowering 和公开游标
   restore 被 [factory](../prototype/interface/ClightAffineLoadedCandidates.v)
   绑定到同一 package。False 分支始终是原 memory-loaded loop。
6. 原 source-prefix、flatten、quiet-suffix 契约保留真实上下文效果；
   [loaded table host](../prototype/interface/ClightLoadedRegionHost.v) 消费原
   independent progress／scope／private-pool 定律。
   [compiler](../prototype/interface/ClightGuardedAffineLoadedCompiler.v) 组合
   SimplExpr、SimplLocals、实际 table 安装与 CompCert backend。

Preparation 的 D 仍含有限正常 source completion。Whole-program 安装另由
语言的 signed loaded progress 证明，而不是把待检查的 bound 稳定性写入
进展前提。本阶段没有将这个 finite host 描述成任意无限源的有限前缀证明。

## 三方责任与实际复用

| 层 | 本次交付／复用 | 还需具体使用者提供什么 |
| --- | --- | --- |
| framework kernel | 无修改；域限制、readonly sequential condition、接受／回退组合继续被真实 local rule 消费 | 语言定律及 `C_opt`／`C_derive`／guard 安全证据 |
| Clight language | 任意 prefix 位置的 source receipt；复用 actual expression、load/store、private transport、strict nested progress、sequence/suffix 和程序安装 | 实际 prefix producer、protected writes、合法 source 形状及 placement checker 成功 |
| optimizer/domain | 参数化 actual source package、loaded header/body evidence、全部 writes 覆盖与稳定性、cached transport；原 mapped/tiling checker 和 schedule generation 后 rechecking | 不受信任 metadata/proposal 可由调用者替换；成功时必须绑定实际 AST、candidate、range 和 restore |

新 preparation interface 目前由 loaded 入口消费；旧 cached compiler 仍使用
原 guard 证明。它展示可替换 source evidence 的边界，不说明两个 installed
入口已经共用这份 proof implementation，也不证明总作者负担降低。

## 验证结果

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make affine-loaded-compiler-native
```

本阶段按这条 target 的三个实际步骤执行：proof audit、提取构建和 native
矩阵／绑定验证。Audit 检查所选依赖闭包的时效、source/object 摘要与端点
假设；新增模块已实际编译，未 clean 重编译整个闭包。

| 证据 | 结果 |
| --- | --- |
| `build/affine-loaded-compiler/proof/report.json` | 47 端点，12 language 端点；549 项依赖，893 源摘要；没有超出原 CompCert＋mapped＋tiling 的全局公理，新 compiler 和旧 regression 为 42 项 baseline 假设 |
| `build/affine-loaded-compiler/compiler/.guard-build.json` | 提取入口绑定新 proof report、sources、driver、native proposer/oracle 和实际 ccomp；无未实现 extraction axiom |
| `build/affine-loaded-compiler/native/report.json` | 十一配置全部本轮新编译；每配置 150 次调用，累计 1,650；独立模型和 gcc 源执行比较完整两个 20,000-word buffers、prefix values、i/j/k、snapshot、实际 suffix 和外部 globals/context |
| 七个 GDB watchpoint probes | triangle、ragged、schedule、4×1 tile 接受；shifted alias 和 covering-box 拒绝后源顺序；source/candidate 顺序实际不同 |
| `build/affine-loaded-compiler/validation.json` | proof、object、compiler、native 文件及验证脚本逐项绑定，非仅引用旧报告 |

150 个唯一输入来自五个 source functions、三种 pointer relations 和十组
controls。额外三个函数分别缺少 bound snapshot、写 bound 单元、重复覆盖
prefix output，所有配置均未安装这些函数。Runtime controls 包括空／负界、
非零起点、n=64 和超过 cap 的 n=65。运行结果不能单独证明每个调用走了哪条
路径；七个机器探针提供明确接受／回退路径证据。

候选配置包括 triangle/ragged mapped、explicit schedule、2×3/4×1 tiles；
错误 quotient witness、缺失源点、零 tile、未支持 raw division、错误域和
oracle resource limit 均静态保留源。真正需要 alias 条件的反例是 shifted
同 buffer：三次迭代时，源最终单元为 4660，未 guarded 的换序候选为 4723。
同-base 可接受小域的实际前两个探针 writes 是 160 再 97，拒绝时为 97 再 160。

报告的 proof 字段不宣称 frontend/native 验收；实际运行由独立 native
report 提供。没有测量性能或证明负担收益。

```text
proof report:
2e0b5fbe55632b90652ea5cc0b2e74b6ccdc9c00566de32f51cfa2354ee2600d
native report:
cb3ab04c6681e1798f44433a6c41a4cc33203ef094dea11dc7b588bcd57d0f82
compiler stamp:
2e2744faadf384a6fd46c857020c441011020d900d35b140ad4559d965a647db
```

## 评审吸收和下一项

本次 fetch 的 topdown SHA 为 `8c098ed`，其他两个评审分支仍为
`9673381` 和 `3e9f008`。新的 context-lifting 讨论已同步，
[源码核对](clight-boundary-contract-review.md) 明确 language host 的 reusable
安装定理与优化／具体位置的 guarantee/placement 证据，保留 finite/open 的
实质差异，不为 diagram 改写 kernel。

共享 extraction script 新增 loaded 入口，因此原 affine-inner 入口也重新
构建及完整回归；它的证据单独绑定原 891 调用／七个探针，不作为新的 loaded
运行能力。原 proof digest 仍为 `ecba792cd8bd04be0aa78876b516a61e2d12499665b295947550ec01309adbd6`；
本轮 native digest 为 `d7d8d31cbdeed3ddf71a9f647adb412c88928263ae451d76b3acb13523b5a515`，
compiler stamp 为 `6655ccb7ebd88b512b0ca038632ecb84c81cbb5839d64f7a628df5900489a5c9`。
绑定验证通过，原 native suite 和验证脚本保持。

下一必交付是独立 bound pointer：用 actual source 的 bound receipt，并用
动态物理 write-footprint 分离覆盖所有 stores；不能以不同变量名或指针不等
代替 byte non-alias。之后接依赖 preload 的安全顺序与 private snapshots，
以及一般深层 affine 域。Direct tree 当前会复制 source fallback，candidate
guard 还重复 preparation tests；已有 shared/residualization 设施可供后续
接入，这些成本问题仍保留，不能据功能验收主张盈利。
