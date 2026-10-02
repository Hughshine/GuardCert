# Guard：带前提的程序变换与组合证明

研究问题：如何把片段变换所需的语义前提处理为可靠证据或安全的检查代码，并复用条件正确性证明接入完整程序？首条实现主线是顺序 CompCert 中的行为保持变换，采用入口检查与原片段回退。PolCert 是可能的实例，接口不依赖多面体表示。

以 Doerfert、Grosser、Hack 的 [Optimistic Loop Optimization（CGO 2017）](https://dl.acm.org/doi/10.5555/3049832.3049864) 为主线，现有原型覆盖 presumption 编码、condition 合成和 conditional rewrite。真实 Clight 分支、表达式与有限语句区域 passes 已接入 C 到汇编正确性，并提取成编译器运行了 C 示例。当前工具链锁定 CompCert v3.18、Rocq 9.2.0 与 Stdlib 9.2.0。

研究对象还包括人工或工具给出候选后，由框架寻找成立条件、生成检查与回退。COVE/cSTOKE、Peek、Chamois、Icing 和 CoreJIT 已覆盖这条链的不同部分；当前原型是可行性基线，候选增量是可运行的、已验证的前提处理与检查代码生成。候选条件推断尚未实现，新颖性也尚需具体算法与实例支持。

- [文献与需求](docs/survey.md)：已有工作解决了哪些部分，以及候选研究空隙。
- [跨领域 survey](docs/survey-general.md)：重构、修复、合约、更新、enforcement、近似和超性质等场景的区别。
- [已有覆盖与研究定位](docs/research-position.md)：CompCert 主线、verified peephole 和最接近工作的对比；值得检验的具体问题。
- [从候选到带检查的程序](docs/candidate-conditioning.md)：人工/机器候选、COVE、条件等价，以及与 CoreJIT、Alive2 和 Peek 的区别。
- [具体贡献与推进计划](docs/contribution-plan.md)：建议主线、算法与定理、第一批实例和验收标准；补充可执行前提及最优 guard 合成的先例。
- [框架扩展设计](docs/framework-extension.md)：证据、状态关系、失败协议与不同证明目标；区分设计和已实现能力。
- [性质运输与状态关系的补充文献](docs/composition-literature.md)：CompCert／Verasco defensive form、开放模块组合及安全插桩的已有覆盖。
- [研究动机草稿](docs/intro.md)：先描述变换类与研究对象。
- [Presumption 分类与合成](docs/presumptions.md)：表达能力、编码定理、overflow flag 和死分支 rewrite。
- [问题定义与证明接口](docs/framework.md)：插件义务、局部到全程序的桥接、CompCert 接入路线。
- [性质接口与抽象核心](docs/abstract-kernel.md)：语言实例、可组合的语义维度、三种检查结果、残余化，以及新条件树的实际 C→Asm 接入。
- [验证记录与边界](docs/validation.md)：实际编译、实例和反例检查。
- [真实 CompCert 接入](docs/compcert-integration.md)：插件证书、C 到 Asm 定理、提取与原生执行。
- [常见 rewrite 接口与实例](docs/common-rewrites.md)：除法、取模、条件算术取消、Truth identity；真实内存的局部接口。

## 原型

当前主线是 `AbstractGuard.v` / `SemanticFacts.v`：通用核不内置整数或内存语义，语言实例提供性质、检查原语与条件选择。`ClightCondition.v` 将生成的条件树降低成实际 Clight 控制流，表达式与语句宿主接到完整程序模拟，`RegionCompiler.v` 接到 C→Asm。overflow 取消规则已使用这个路径。`ResidualGuard.v` 提供有证书的静态消去，`AbstractSchedule.v` 提供性质驱动的交换链证明；这两项尚未进入原生驱动。详细接口与 PolCert 尚需的桥接见 [abstract-kernel.md](docs/abstract-kernel.md)。

[同地址读取实例](docs/clight-same-address.md) 在这一端到端路径上增加内存性质维度：源 load 建立检查有效性，运行时 `p == q` 允许后端消除重复读取。原生检查覆盖快路、回退、unsigned 边界及 signed／volatile 排除。

[树形原子检查与 signed 取消](docs/clight-signed-cancellation.md) 让一个性质原子由多步骤条件树实现，继续复用同一完整程序宿主。signed32 的 `(x*2)/2 → x` 已进入实际 C→Asm 驱动，使用 signed64 检查而在溢出时保留源式回绕行为。

[有限语句区域宿主](docs/clight-statement-regions.md) 将局部条件正确性证书提升到完整 Clight 小步模拟，证明源区域内部每一步的工作量度量严格下降。`encoded_region_rule` 复用同一性质与条件合成接口；冗余赋值实例已进入实际提取驱动，原生例子验证普通、循环和 goto 外围中的快路／回退。出口 memory 已支持双向 `Mem.extends`；内部循环和 private temporary/live frame 仍待接入。

[内存与宿主运输性质](docs/compcert-memory-transport.md) 从不依赖具体语义的双向模拟引理，实例化真实 CompCert 内存、运算、Clight 表达式和完整小步执行。代码及 temps 相同而 memory 双向扩展时，语言实例提供相同观察及后继关系的证书。PolCert 的具体 load/store 桥接已复用这个接口；区域替换宿主已借此连接等价内存出口与完整 C→Asm 定理。

可选的 [PolCert 适配](adapters/polcert/README.md) 已在同一工具链上完整重编译真实 `Loop` 的 57 个证明依赖，直接接入 `INSTR` 的 Bernstein 交换性质和 `Loop` 条件片段。`make polcert-proof` 从锁定源码与补丁复现；实际 PolCert 优化器到完整 Clight 循环程序的桥接仍在推进。

[实际优化器适配](adapters/polcert-optimizer/README.md) 进一步移植 92 个证明依赖。`PolCertOptimizer.optimize_version` 调用真正的 `Opt_prepared`，检查 metadata 并生成 guarded `Loop.t`，其正确性直接消费上游端点；复现目标为 `make polcert-optimizer-proof`。这是循环 IR 终止执行的精化，还需候选进展、固定宽度 lowering 与 Clight 区域模拟才能获得多面体优化的完整 C→Asm 链。

[signed32 仿射桥接](docs/polcert-affine-clight.md) 已证明实际 Loop 表达式和布尔测试到 Clight 的 lowering，并通过通用性质接口生成输入区间 guard。接受的 guard 建立静态区间证书需要的运行时前提；缺失布局或无效区间保留 unknown。复现目标为 `make polcert-affine-proof`。完整循环与区域 lowering 仍在推进。

[计数循环桥接](docs/polcert-clight-loop.md) 进一步提供基本指令插件、`Instr/Seq/Guard` 的 body 编译、一个外层 Loop 的 Clight lowering，以及任意 continuation 中的实际小步执行证书。复现目标为 `make polcert-loop-proof`。当前 body 要求保留 temporaries，内部循环尚未支持；多面体优化的完整程序 simulation 仍未闭合。

[嵌套循环桥接](docs/polcert-nested-clight.md) 扩展到指定 scratch 深度的多层 Loop，允许内层 scratch 改变并保护参数、外层计数器及声明的 live frame。编译器检查整个 scratch pool 的新鲜性；复现目标为 `make polcert-nested-proof`。翻译另有纯语法接口，正确性证书由语言实例提供。

[具体数组实例](docs/polcert-array-clight.md) 重编译真实 `CInstr/CState/Loop` 的 60 个依赖，将一维 signed32 数组指令和嵌套循环接到 Clight 的真实 load/store 与小步执行。最终端点没有抽象指令执行假设；真实分配／初始化例子证明 `B[0]=7` 时生成代码产生 `A[0]=8`。复现目标为 `make polcert-memory-proof`。标量参数入口、候选进展、tiling 边界运算及完整程序区域模拟仍在推进。

[真实 CInstr 调度区域接口](docs/polcert-schedule-regions.md) 已将源片段解码、条件调度证书和候选生成组合为完整 Csem→Asm 定理，采用与 PolCert 相同的等价内存出口。插件仍须证明这三个义务；具体数组写入解码已提供，这套调度包接口的具体包仍待构造。

[具体 CInstr 双写重排](docs/polcert-store-swap.md) 已用真实 Bernstein 定理证明同一数组的两个不同常量元素写入可以交换，并接到完整 Csem→Asm 定理。检查器验证静态参数和源 AST，真实分配例子构造两端执行。该实例尚未提取成原生编译器，内部循环与真实多面体调度器接入仍未完成。

[无人工区间的仿射 guard 合成](docs/affine-dynamic-synthesis.md) 直接从“不溢出”前提与 layout 生成依赖顺序的 signed64 检查树，证明检查精确对应所选 signed32 前提，并经性质接口支持复合公式和 unknown。复现目标为 `make polcert-dynamic-proof`；这一合成器尚未进入原生驱动。

`GuardedRegion.v` 把片段表示为一次返回事件、控制出口和状态的转移。新的插件路径先证明语义义务与 presumption AST 的编码对应，经 `Synthesis.v` 合成为显式短路条件程序，再由通用定理提升到任意外围 CFG 的有限与无限执行。

| 文件 | 内容 |
| --- | --- |
| [GuardedRegion.v](theories/GuardedRegion.v) | 版本选择、证书与原片段的绑定、多位置替换、上下文替换定理 |
| [CheckedGuard.v](theories/CheckedGuard.v) | 8 位无符号加法检查；接受的表达式与数学整数求值一致 |
| [Examples.v](theories/Examples.v) | 无回绕假设下的比较消除、无别名假设下的写操作交换、完整示例程序 |
| [Presumption.v](theories/Presumption.v) | 有限表达子集：算术、NoOverflow、边界、不相交及布尔组合 |
| [Synthesis.v](theories/Synthesis.v) | 编码契约、带 flag 的求值、condition 合成与真/假对应 |
| [ConditionalRewrite.v](theories/ConditionalRewrite.v) | 恒假分支、前提下的死分支、矛盾前提；共享完整程序定理 |
| [CompCertArithmetic.v](theories/CompCertArithmetic.v) | 实际 CompCert Int 运算与 checked-add 原语的对应证明 |
| [ClightGuard.v](theories/ClightGuard.v) / [ClightGuardProof.v](theories/ClightGuardProof.v) | 真实分支版本化 pass；Clight 两种入口语义的完整程序仿真 |
| [ClightEncodedRule.v](theories/ClightEncodedRule.v) / [ClightNoWrap.v](theories/ClightNoWrap.v) | 编码、condition lowering 与局部正确性证书；unsigned32 分支实例 |
| [ClightExprRewrite.v](theories/ClightExprRewrite.v) / [ClightExprRewriteProof.v](theories/ClightExprRewriteProof.v) | 表达式版本化与完整 Clight 程序的仿真 |
| [ClightExprRule.v](theories/ClightExprRule.v) / [CommonRewrites.v](theories/CommonRewrites.v) | 完整快照上的表达式证书；严格表达式上下文提升；四个 rewrite 实例 |
| [CompCertMemoryRule.v](theories/CompCertMemoryRule.v) | Disjoint 编码与实际 Mem.load/store 的局部稳定性、load hoisting 端点证明 |
| [GuardCompiler.v](theories/GuardCompiler.v) | 扩展编译驱动、Csem 到 Asm backward simulation 与规格保持 |
| [ClightIntegrationExamples.v](theories/ClightIntegrationExamples.v) | 真实 Clight 快路／回退；恒假分支与矛盾前提的编译器实例 |
| [CommonRewriteExamples.v](theories/CommonRewriteExamples.v) | 实际 AST 命中、类型拒绝、嵌套上下文和无条件取消的溢出反例 |
| [demo.py](prototype/demo.py) | 独立 Python 执行模型、边界枚举和错误变体反例 |
| [synthesis_demo.py](prototype/synthesis_demo.py) | 从 presumption 合成 condition AST，运行新增 rewrite |

真实 passes 在 `SimplLocals` 后运行：分支版本化允许 guard 接受时进入原 else；表达式版本化允许 guard 接受时运行保持类型和值的候选。后者支持赋值右侧和 return，可提升到二元／单目运算及 cast。四个新实例是 `x/y→x>>1`、`x%y→x&1`（检查 y=2）、`(x+x)/2→x`（检查不回绕）和 `x-x→0`（Truth）。完整程序证明覆盖调用、外部事件、可能发散的循环、switch 和 goto。

当前语句宿主只覆盖有限静默区域，尚无任意候选 region 的关系式宿主、完整数组 non-alias 检查、preload 或完整 DSL lowering；真实 Mem 的 load-hoisting 证明尚未接入 Clight。同地址内存表达式 guard 已可执行。独立 `GuardedRegion.v` 模型仍采用总的有限宏转移，两条证明路径的边界见接入说明。

## 运行

需要 opam、Python 3.10 或更新版本和通常的 OCaml 构建依赖。工具链在项目的 `.toolchain/` 中隔离，不需要系统安装。详细版本与构建记录见 [toolchain.md](docs/toolchain.md)。

```sh
sh scripts/bootstrap.sh
opam exec --root="$PWD/.toolchain/opam" --switch=guard -- make check-integration
```

只验证独立语义核和 Python 模型：

```sh
opam exec --root="$PWD/.toolchain/opam" --switch=guard -- make clean
opam exec --root="$PWD/.toolchain/opam" --switch=guard -- make check
```

`make proof` 编译独立语义核；`make demo` 运行两个独立执行模型。`make check-compcert` 还完成 CompCert proof 构建与接入文件编译。`make check-integration` 进一步审计实际驱动定理的假设、提取 `RegionCompiler.compile_property_regions`、构建编译器、编译五个 C 示例并比较原生输出，没有全局安装。已有 Python 模型不是 Rocq 提取产物；原生示例使用的编译器来自实际提取。版本、条件 AST 与原生结果分别在 `build/compiler.txt`、`build/synthesized-conditions.json`、`build/native-demo/`、`build/native-rewrites/`、`build/native-alias/` 、`build/native-signed/` 和 `build/native-region/`。
