# 2026-10-06：参数化仿射源通过公共保持接口编译

公共接口的第二个真实多面体使用者已经编译和运行：它处理外层 `i<n`、内层 `j<U(i,parameters)` 的仿射源，以及已有多数组、不同布局、偏移和多读取／word compute body。实际不受信任调度经过生成和独立核对，再接安全条件、direct/shared 实现、公开出口与完整 Csem→Asm。此次是已有领域证明的公共接口迁移，不是一般条件发现算法。完整活动目标继续进行。

本阶段按 `topdown/research-positioning` 的 [paper narrative](topdown/paper-narrative.md) 检查三方责任和最难义务，见 [责任矩阵](framework-responsibilities.md)与[当前计划](current-work-plan.md)。该方向持续属于活动目标；CGO 2017 Optimistic Loop Optimization 的完整覆盖仍按[验收账本](optimistic-loop-acceptance.md)推进。

## 实际接口和证明链

[ClightParametricPreservation](../prototype/interface/ClightParametricPreservation.v) 的 proposer 收到已识别 body 的 instructions、坐标数量和 context arity，返回未经信任的 mapped Loop／坐标变换、二维 tile 尺寸或 affine schedules。调度路径运行实际 `memory_generate_scheduled_loop`，之后重新核对生成 Loop 的实例域和依赖；生成器的答案不会直接进入替换 table。

局部证明复用 `memory_parametric_body_candidate_rule`，经 `encoded_private_as_preserving` 消费实际 globalenv 下的 source-to-candidate 保持。`choose_preserving_dispatch_sound` 复用语言层 direct/shared realization；shared 另核对 candidate quiet 和私有 Boolean freshness。候选包含公开 i/j/k 的出口恢复，安装继续消费私有作用域、frame、source progress 和上下文证明。

[ClightParametricCompiler](../prototype/interface/ClightParametricCompiler.v) 的 `compile_preserving_parametric_correct` 对任意 proposer、lowering 和 private budget 给出 Csem→Asm backward simulation。提取入口和本次原生执行使用同一函数，不只验证一个与实际编译无关的模型。使用步骤与完整例子见 [使用说明](clight-parametric-preservation.md)。

| 责任 | 本次实际新写／复用 | 没有据此自动完成的义务 |
| --- | --- | --- |
| 语言无关框架 | 复用 readonly 条件处理、局部保持证书消费和组合，不增加另一个抽象 if 核 | 任意语义前提的编码、自动 assumption extraction |
| Clight 语言实例 | 共用保持分派 helper、已有 direct/shared realization、私有名字／frame／公开观察运输、有限 host 和后端连接 | stateful 扫描的一般关系与 exact dispatch；任意无限 polyhedral fallback |
| 优化／domain 实现者 | 参数化 source/body package、仿射端点覆盖、参数范围的安全 lowering、实际 mapped／tiling 及依赖核对、源／模型／候选执行对应；新 proposer 接口与完整 pass glue | 新源域和 body 的对应、所有实例覆盖；一般深度 polyhedron 与 pointer footprint 的公共接口安装 |

最难的 `C_derive` 在本例中复用已有仿射端点证明：入口 U(0)、U(n−1) 的界覆盖所有迭代宽度。`C_guard` 另证明参数 interval 下机器表达有定义且具有所需数学意义；检查依次取得源 header、参数范围、端点宽度及实际数组比较依据。D 来自正常源执行，没有预先放入待检查的范围或 no-alias。首行为空时可有定义的源仍回退，这个限制单独记录。

当前 profile 搜索是默认 bounds 加 outer cap 8/4/3/2/1，并复用已有 width=1 证书候补。它不是最弱条件、通用 QE 或一个新符号推导算法。数据计算保留机器 word 回绕；控制／地址的数学对应使用另外的范围证据。

## 已通过的验证

| 范围 | 本阶段实际结果 |
| --- | --- |
| 参数化公共使用者证明 | 12 个审计端点、329 项实际使用者依赖、811 份源码摘要；继承 CompCert 35 项与既有领域七项，无新增全局公理 |
| 提取入口 | `build/compcert-readonly-parametric/ccomp`；任意不受信任 proposal 经过实际核对；同一二进制支持 direct/shared |
| 原生功能回归 | 六份原有完整 C 程序，134 个编译配置，全部 stdout 与独立源模型及 GCC 相同；核对实际 Clight 候选、公开 counters 与完整数组 |
| 实际运行顺序 | 四个 x86-64/GDB 硬件观察点探针；两种 lowering 均观测到接受后的 interchange 顺序，以及非零起点的 source fallback 顺序 |
| 输入／产物绑定 | proof、compiler stamp、全部证明和 native inputs、提取文件、proposal、binary、assembly、Clight、输出及可选探针日志摘要全部核对通过 |
| 旧路径兼容性 | 当前主接口 415 端点／864 摘要、25 配置／40 报告的绑定重新核对通过；named 使用者 40＋8 配置绑定通过。本阶段未重新构建全部旧配置 |

领域继承的七项是 `CoqAddOn.posPr`、`CoqAddOn.zPr`、`PedraQBackend.add`、`PedraQBackend.isEmpty`、`PedraQBackend.pr`、`PedraQBackend.t`、`PedraQBackend.top`。这是旧 PolCert/VPL 证明边界的继承；不把可选使用者描述成只有 CompCert 假设，也不把两份重合审计的端点／摘要相加。

| Fixture | 配置数 | 每配置输出行数 |
| --- | ---: | ---: |
| 参数化 affine 源 | 32 | 4,378 |
| 参数 context 与重复参数 | 22 | 2,531 |
| 不同数组 layout 的复制 | 20 | 4,868 |
| 多 statement／连续 region | 20 | 5,844 |
| 仿射偏移与链式读写 | 20 | 3,651 |
| 多读取与 word compute | 20 | 4,263 |

上述输出行数不是独立输入调用数，不用于声称 optimizer 一般性。候选包括 metadata-aware identity／interchange／fission、1×1／2×3／17×13 tiling、平移与剪切。错误映射、错误维度、溢出系数、缺失 statement、错误参数 arity、畸形／缺失 proposal、FM 预算耗尽与错误 certificate 均有实际保守拒绝。offset body 中两条依赖链的 fission 拒绝沿用独立旧回归的逐候选策略；成功识别 source 不代表任何调度都成立。

同一 `affine_growing` interchange 二进制在 `(0,2,2,0)` 下先写 `a[20]=44` 再写 `a[1]=8`；在非零起点 `(2,4,5,1)` 下先写 `a[41]=82` 再写 `a[60]=118`。探针没有修改源或汇编，是两个入口的功能见证，不增加形式定理的量化范围。

GCC 对照用 `-O0 -fwrapv`，匹配这些 compute fixture 的 word 数据语义。134 配置的最终完整回归使用四个独立编译进程；这是功能测试，没有性能结果。测试驱动先后修正了报告路径的 `Path` 类型和 offset fission 的已有逐候选拒绝集合，随后重新运行完整 134 配置；最终报告只绑定通过的这一轮。过程中编译器保持同一摘要。

工具链继续锁定 CompCert v3.18 的完整 commit／归档摘要与 Rocq/Stdlib 9.2，见 [toolchain](toolchain.md)。上游 VERSION 仍写 3.17，源码身份按 tag／commit／checksum 核对，未改版本文件。10 月 6 日重新核对[官方下载页](https://compcert.org/download.html)和[v3.18 release](https://github.com/AbsInt/CompCert/releases/tag/v3.18)，两者均列其为最新 release。

## 私有扫描检查的独立证明进展

[ClightPrivateCheckFacts](../prototype/interface/ClightPrivateCheckFacts.v) 证明真实 projected check 的完成执行唯一性，并将一个完成见证的性质推广到所有完成执行。[ClightParamPointerCheckFacts](../prototype/interface/ClightParamPointerCheckFacts.v) 证明旧实际参数化 pointer scan 的 quiet 语法并实例化这一设施。独立审计通过四个端点、388 项实际依赖和 801 份源码摘要；这些端点的继承假设不超出 CompCert，无新增公理。

这是语言确定性设施和真实 domain 使用者的接入，尚不是新的 pointer pass。它只得到 `accepted⇒P(checked)`；下一项须证明私有写入保持 P 的全部观察依赖，得到 `P(original)`，再交付公共 guard certificate、无额外分支控制耦合的 exact dispatch、安装与提取。源 package 使用稳定寄存器矩形 bounds 下的参数化仿射指针访问，不把它与本次非矩形 affine 内层源混为一体。具体义务和责任见 [private-check 迁移规格](clight-private-check-migration.md)。

## 报告身份与后续工作

| 产物 | SHA-256 |
| --- | --- |
| `build/interface-parametric/report.json` | `b86ba479a231b31f5d6d64e2d1444bb310539c23bddd052607e73886fe8a477b` |
| 新提取编译器 | `5355e3858928d1783de4f110fb9ec4ded9d61f48ed604712b41c1bf1baf97160` |
| `build/interface-parametric-native/report.json` | `c22ebd98f0df653f9e2723e8e972d7bf79acd800b9fc968730d17e3e92989398` |
| `build/interface-parametric-native/runtime-order-report.json` | `4f6d3acda530ed20a3a048b6b956e4fa8736b59642a06bd85c3e5114ce4e7265` |
| `build/interface-parametric/validation.json` | `fd8ab0935a9653cf837470422105fde17c7c1c7254731f9f3e772b6b23bdc8ae` |
| `build/interface-private-check/report.json` | `90961f12a141ae3a051e9bdf10adf77efa0c7c0d6607e0a2a003d5caf26d5262` |

三个评审分支的读取锚点仍为 `f793629`（topdown）、`9673381`（evidence-to-claim）、`3e9f008`（performance）；新增的一手 [Chamois／Peek 接口补核](related-work-interface-check-2026-10-06.md)关闭了 oracle API／CFG proof 的访问未知项，未据此宣称动态 guard 能力缺席或研究首创。

下一项先完成真实私有 scan 的原入口前提稳定与 exact host。一般深度 affine 域、符号化受限条件／足迹算法、shared whole-loop／无限 pointer fallback、同例作者负担和实际性能仍分别验收。当前实现只使用正常有限 region 的 source progress；方向文档、新 record、端点数量或测试行数均不将完整目标标为完成。
