# 非矩形 pointer 分块：复用局部证书与完整编译入口

2026-10-06。接续 `88d4da5` 的 [affine-inner compiler](clight-affine-inner-pointer-compiler.md)，本阶段将 tiling witness 接入同一真实 source package、运行时条件和完整程序宿主。实际 C 的 `j<i+1` 与 `j<2*i+1` 均安装 2×3 和 4×1 分块候选；错误 witness、遗漏源点及非正 tile 大小保留源。完整研究目标仍在进行，依赖加载和一般深层域没有由这项接入解决。

## 使用者交付与验证责任

`AffineInnerTilingProposal candidate witnesses` 提交实际 Loop 与逐指令 `statement_tiling_witness`。优化实现者可以自行生成它们；[便利 tiler](../prototype/interface/ClightAffineInnerPointerCandidates.v) 和 OCaml callbacks 均不受信任。`(tile rows columns)` 使用便利生成器，`(tile-loop rows columns loop)` 允许自定义 Loop 并附标准两轴 witness。Rocq 接口支持直接提交其他 witness，CLI 便利语法尚未暴露任意 link 编码。

| 责任 | 新增／复用 | 实际证据 |
| --- | --- | --- |
| framework | 核心未改；复用 readonly sequencing 和局部保持／宿主接口 | 条件接受证据的组合不解释 tile、pointer 或 quotient |
| optimizer/domain 的 `C_opt` | 新 [model tiling wrapper](../adapters/compcert-memory/GuardMemoryParametricModelTiling.v) 连接独立 checker 和实际 source/candidate | 源／目标抽取、quotient link、当前域对应、指令和依赖核对成功才产生旧 candidate certificate |
| optimizer/domain 的 `C_derive` | 复用实际源域、footprint、范围和物理 non-alias 推导 | 不把分块包络当成源的访问权限 |
| language＋实例的 `C_guard` | 相同机器条件、两套 ranges 和 source receipt | 边界控制迭代不读取数组；实际 body 只在 source-point 条件成立时运行；表达式仍通过机器 lowerer |
| language 的 `C_host`＋规则 witness | 相同 prefix、candidate/restore、suffix、private pool、progress 和 table host | 新 tiling 分支消费相同 local contract 后进入原 Csem→Asm 证明 |

`check_affine_inner_pointer_certified_package` 抽出此前 mapped 工厂中的共同条件编译、candidate lowering 和 local contract。其 sound theorem 参数是“本次 checker 的接受结果蕴含**同一个实际 candidate**的局部证书”。这不作为提取代码中的可信 oracle：mapped 与 tiled 调用点分别用已证明的 checker sound 定理填入，schedule 路径继续生成后调用 mapped checker。没有为 tiling 重写 source typing、alias guard、出口恢复或程序 simulation。

最困难的对应由原 [extracted tiling checker](../adapters/compcert-memory/GuardMemoryExtractedTiling.v) 承担：绑定 tile 坐标的 quotient 关系与真实 source-point 域，并核对实际 candidate 的当前域。`C_guard` 建立其语义前提，不能替代这个核对。wrong-witness 和 missing-row 两个配置分别检验 link 和全部源点的绑定。

## 候选形状与边界

便利 tiler 提出 `ti,tj,i,j` 四层控制，tile 中的 i/j 范围由 tile 大小给出，body 以真实源上下界筛选。插入 tile 坐标后，源指令的 `[i;j]++context` 参数保持；公开 i/j/k 仍由旧 restore 实现。非整除边界 tile 可以有空控制迭代，但不增加源域之外的 memory operations。

tile 控制范围根据已核对的 metadata cap 计算，tile 数量中的整数除法发生在编译时。quotient 的**数学点对应**已由 witness checker 核对；本阶段没有增加通用运行时 floor/ceil lowering，也没有声称 tile 范围对每次输入最紧。含原始 `Div` 的 affine candidate 边界仍可被原 extractor 拒绝。便利 tiler 没有单独的生成正确性证明，全部输出重新验证。

两个 source domain 仍是 register-valued affine-inner bounds，未缓存每轮重新读取的 memory bound。静态拒绝、动态回退及完整 buffer/public state 分别验证，不从结果相同推断 guard 确实接受。

## 证明、提取与原生结果

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make affine-pointer-compiler-native
```

机器路径探针要求环境允许 GDB `ptrace`。selected closure audit 编译变更／过期依赖，不是整个 CompCert 的 clean rebuild。109 个端点中 9 个为语言端点；535 项实际依赖，879 份 source digests。CompCert 基线 35 项假设，继承 domain 基线另 7 项；新增全局公理为 0。model tiling sound 使用 12 项，公共 certified-package local sound 使用 6 项，tiled-package sound 使用 14 项，完整 `compile_affine_inner_pointer_correct` 使用继承基线的 42 项。两个新增 Rocq fixture 核对真实分块 Clight lowering 和零 tile 拒绝，均闭合于全局上下文。

| 新原生配置 | 实际安装／拒绝 | 完整程序结果 |
| --- | --- | --- |
| tile 2×3 | 两个 affine-inner 源均安装 | 81 次调用与源 GCC、独立逐点模型一致 |
| tile 4×1 | 两个源均安装 | 81 次调用一致 |
| wrong quotient witness | 保留源 | 81 次调用一致 |
| missing last source row | 保留源 | 81 次调用一致 |
| tile size 0 | 提案拒绝，保留源 | 81 次调用一致 |

此前六个 mapped/schedule/refusal 配置也由最终新 compiler 重新编译并执行。共十一配置、891 次配置内调用，均检查两个 20,000-word buffers、公开 i/j/k/rp/rq、保留 prefix/suffix 及外围 global context。missing-q source receipt 的函数在所有配置保留源。

七个 linked-machine 探针包括此前五个路径，以及实际 4×1 tiling 的接受／alias 回退：n=3、same-base 的候选先写 `p[160]` 再写 `p[97]`；偏移 alias 输入回到源的相反顺序并保留 `p[97]=4660`。若无条件采用候选，该值为 4723。这证明一条真实 tiling 接受路径和一条有必要回退的路径，不等于收益测量。2×3 配置与第二个源的结果／安装另有上述完整矩阵证据，没有为它们增加独立机器顺序探针。

| 当前产物 | SHA-256 |
| --- | --- |
| proof report | `ecba792cd8bd04be0aa78876b516a61e2d12499665b295947550ec01309adbd6` |
| compiler | `a02b12a143c41a907ceab7e3327ddd88ae9d2eecdfac49b3b814809302ce24aa` |
| extraction stamp | `fc54ddc109c6e28264eb78b93c5e8c4a361d5234b38e0afdb34279905bd7551e` |
| native report | `b93b2975531dd239ac4dc74299ef124c9d9035aee6a8558a2b5613d14d83a3d6` |
| validation report | `dcb6c398bd3663afb09edd6b4bd7a8cc77c0e1e4c288143102af6e4a43c6ea9a` |

[validation](../scripts/validate_affine_inner_pointer.py) 核对当前 source/object digests、proof/extraction/compiler/native 摘要和完整矩阵／机器报告。前次阶段记录的摘要为历史 evidence，当前同一 build 目录已由本阶段产物替换。未重跑其他旧 compiler 的原生矩阵，没有性能或证明负担收益结论。

## 下一项必须交付

优先接 source 活动支持的依赖读取和参数稳定性：后项 load 只有在前项检查成功后才安全时，guard 必须保留读序；cached candidate 必须证明相关 stores 保持所读 bound。原入口 D 不可预设这个稳定性。source 每轮重新读取 memory bound 的情况，不能由“先 preload 到稳定 temp”的实例代替。随后扩展一般深层 affine 域，以及需要实际 ragged capability 的第二机会 scan；性能与同例证明负担各自验收。
