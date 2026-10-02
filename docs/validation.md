# 本轮验证记录

## 2026-10-02：实际 PolOpt_prepared 与 guarded Loop 程序连接

实际 `driver/PolOptCorrect.v` 的 92 文件依赖闭包已迁移到锁定的 CompCert/Rocq 工具链。冻结指定提交、原 v10 工作目录改动及 32 份兼容补丁后，重新恢复全部锁定输入，再执行 `build --clean`，完整重编译成功。日志为 `build/polcert-optimizer-clean-check.log` 与 `build/polcert-optimizer-build.log`。没有修改 sibling 仓库。

`PolCertLoopGuardFor`、`PolCertLoopProgramFor` 接受已有 Loop 模块。`metadata_equal_correct` 核对 metadata，`checked_version_refines` 在失败时保留源程序；核心三适配器重编译与 19 项 INSTR 参数审计通过。

新 `PolCertOptimizer.optimize_version` 直接调用真实 `Core.Opt_prepared`。`optimize_version_correct` 经 Rocq 编译，并直接消费上游 `Opt_prepared_correct`。两个共用适配器以隔离的 `GuardPolCert` 名称重编译，不复用另一 profile 的不兼容 `.vo`。实际端点与新定理的假设名集合经脚本比较，均为相同的 42 项，新增集合为空；详细报告为 `build/polcert-optimizer-adapter-report.json`。

原 97 文件路径因 `PolOpt` 的未使用 import 拉入具体 C 转换器。移除这两处 import 并显式引入仍需的 `Csyntax` 后为 92 文件。额外的九份补丁处理 notation、Proper instance、关系运输与 replace 证明方向；组合 validator 的未使用转发别名引发新版 Rocq module-substitution 异常，改为直接引用原模块后通过。算法与原定理陈述未改变。

已验证的是 alarm monad 成功返回的 guarded Loop IR 程序之终止执行精化，没有候选进展或无报警保证。本轮未提取、运行 PolCert 优化器，未提供数学循环→Clight lowering 或循环区域的完整 C→Asm 模拟。`Loop.semantics` 自身的 NonAlias 前提仍然存在；外围动态检查与原 Clight 回退仍需接通。

## 2026-10-02：提升到真实 Loop.t 程序语义

新增 `PolCertLoopProgram.v` 经 Rocq 9.2 编译。`version_program_preserves` 保留源程序实际的 `Compat/NonAlias/InitEnv` 前提及 metadata；`version_program_refines_endpoint` 在候选 metadata 对齐时消费真正的 `Loop.semantics` backward endpoint。`impossible_program` 证明恒假条件下任意候选死分支保持 wrapped 程序的终止执行。

脚本新增相互隔离的 core/optimizer profile。修改后再次恢复锁定核心输入，`build --clean` 完整编译 57 个文件成功；随后三个适配器全部编译，假设审计恰好为 15 个 `INSTR` 参数，额外全局公理为空。日志为 `build/polcert-core-full-program-check.log` 和 `build/polcert-adapter-build.log`。这轮没有重跑未修改的 Clight 原生执行检查。

`Loop.t` 是循环 IR 程序，尚未由这一步得到完整 C 程序优化定理。优化器 97 文件的移植正在单独工作目录进行；未通过的探索构建不计入上述成功报告。

## 2026-10-02：真实 PolCert INSTR/Loop 的工具链迁移与适配

可选 `make polcert-proof POLCERT_SOURCE=.../verified-compilation-v10-driver` 完整通过，退出码 0。该目标重新编译现有 31 个 GuardCert 核心／Clight 文件，复用已编译的 CompCert proof，随后从锁定提交与保存的工作目录补丁恢复 57 个真实 PolCert 输入，使用 `--clean` 完整重编译，最后编译两个新增适配器。完整日志为 `build/polcert-integration-check.log`，报告为 `build/polcert-core-report.json` 和 `build/polcert-adapter-report.json`。

PolCert 基础库来自当前 CompCert v3.18，而不是旧仓库的 CompCert/Flocq 副本。锁定输入保留 v10 原工作目录中所需的修改；另外 23 份兼容补丁恢复旧 tactic、Hint/instance 可见性和标准库名称，显式解构 `DomainGCL` 的带证明规格，完成所有现有正确性义务。没有修改 sibling 工作目录。

`PolCertSchedule.schedule_correct` 直接消费真实 `INSTR` 的 NonAlias、状态等价稳定性、Bernstein 三项条件和交换性质。`PolCertLoopGuard.version_preserves/refines` 把通用 condition compiler 接到真正的 `Loop.stmt`。`impossible_version` 证明实际参数条件 `P ∧ ¬P` 生成的候选死分支不改变片段终止执行。

新增两个模块没有 `Admitted` 或新全局公理。其 `Print Assumptions` 合并集合恰好为 11 项 `INSTR` 模块参数，构建脚本核对这一集合。上游 VPL 自身的 monad/oracle 公理仍存在；不能从 57 文件编译通过推断整个上游无公理。此次目标没有提取 PolCert、调用实际优化器或进行原生多面体优化。此前 Clight 原生编译检查仍是独立的验证记录。

源码、复现和待接通的 C/Clight 区域边界见 [PolCert 适配说明](../adapters/polcert/README.md)。

## 2026-10-02：抽象性质接口与生成的 Clight 条件树

新增 `AbstractGuard`、`SemanticFacts`、`ResidualGuard`、`AbstractSchedule`、`EndpointBridge` 和 Clight 条件树／宿主／驱动。通用核心只依赖性质维度、检查证据、语言的条件选择与观察关系。它证明三种检查结果的短路编译、保守拒绝在否定下的安全性、维度组合、静态证书的残余化和局部 preservation。抽象调度接口证明独立指令的相邻交换链，不解释内存或算术。

`ClightTreeRewriteProof.transform_program_correct1/2` 已证明真实条件树宿主的完整 Clight 程序模拟。`TreeCompiler.compile_property_rewrites_correct` 给出实际新驱动的 `Csem → Asm` backward simulation。overflow 取消规则通过 `encoded_tree_rule` 接口生成检查树；其他已有规则通过明确标记的 legacy adapter 复用。

最终再次清理工程输出后，`make check-integration` 退出码为 0，重新编译当前全部 31 个工程文件，完成两个 Python 回归、上游 proof 目标、新驱动提取／构建及两个原生示例，并包含增强后的原生 IR 检查。完整日志为 `build/abstract-final-check.log`；较早的 30 文件检查保留在 `build/abstract-integration.log`。没有再次清理上游 CompCert。

新原生驱动的入口为 `TreeCompiler.compile_property_rewrites`。旧边界值、24 对除数输入、循环、switch、label、goto 及源零除保护均通过，输出仍与 GCC 参考一致。新增检查确认 Clight dump 确实包含由性质接口生成的 validity/value 嵌套条件树；报告的 `property_generated_condition_tree_checked` 为 true。

在同一 Rocq 环境中重新输出上游和新驱动的 `Print Assumptions`，两者均有相同的 35 个假设，新增集合为空。结果记录在 `build/property-assumptions-report.json`。通用核心的主要定理为闭合证明；CompCert 桥接继续继承上游假设。新增工程文件无 `Admitted`、语义 `Axiom` 或 `Parameter`。

已实现的静态残余化与交换链接口尚未进入原生驱动；这次检查没有 PolCert 原生优化实例、性能结果、完整 arithmetic DSL 的 Clight lowering，或可执行的 alias guard。实际接口及后续桥接义务见 [abstract-kernel.md](abstract-kernel.md)。

## 2026-10-02：常见表达式 rewrite 接入

新增六个工程文件：`ClightExprRewrite.v`、`ClightExprRewriteProof.v`、`ClightExprRule.v`、`CommonRewrites.v`、`CommonRewriteExamples.v` 和 `CompCertMemoryRule.v`。表达式适配器统一接入四种 unsigned32 rewrite：除数为 2 时除法变移位、取模变掩码，无回绕时 `(x+x)/2→x`，Truth 下 `x-x→0`。它们复用 presumption 编码与合成证明，再与既有分支 pass 及上游后端组合。

`compile_common_rewrites_correct` 给出实际编译函数的 `Csem → Asm` backward simulation；`compile_common_rewrites_preserves_spec` 给出排除出错的规格保持。具体定理没有源程序 no-overflow 或固定除数前提。`encoded_expression_rule` 暴露完整入口快照、编码、lowering、类型及局部值保持义务；识别器和严格表达式上下文提升也已证明。

最终执行 `make clean` 后的 `make check-integration`，退出码 0。全部 19 个工程 Rocq 文件重新编译，既有两个 Python 回归、CompCert proof 目标、编译器提取／构建和两个原生示例通过。上游 proof 使用此前完整构建的 `.vo`，未清理上游。日志是 `build/common-integration-check.log`，报告是 `build/common-integration-report.json`。编译器缓存键现在包含全部工程 `.v`，执行入口是 `GuardCompiler.compile_common_rewrites`。

原版 `Compiler.transf_c_program_correct`、既有 `compile_no_wrap_correct` 和新增 `compile_common_rewrites_correct` 的假设名集合均为相同的 35 个，新增集合为空。工程源码没有 `Admitted`、新增 `Axiom` 或 `Parameter`。这些定理继承上游假设，不是闭合的独立语义核定理。

真实 C 测试 [native_rewrites.c](../examples/native_rewrites.c) 的结果：

| 检查 | 结果 |
| --- | --- |
| IR 实际命中 | 9 个除数 guard、2 个 no-overflow guard、7 个 shift 候选、2 个 mask 候选、1 个 Truth identity；原始 fallback 保留 |
| 输入 | x 为 `0,1,254,2147483647,2147483648,4294967295`，除数为 `1,2,3,4294967295`，共 24 对 |
| 无回绕边界 | `2147483647` 接受，取消后仍为 `2147483647` |
| 第一个回绕值 | `2147483648` 拒绝，原式结果为 0；Rocq 另证明无条件替换会错 |
| UINT_MAX | 拒绝取消，原式结果为 `2147483647` |
| 上下文 | return、临时赋值、真实全局 store、嵌套表达式、循环、switch、label body 与 goto |
| 控制保护 | goto 进入 label 后执行新 guard，结果为 61；零除数在源保护分支返回 777 |
| 原生执行 | 所有输出与 GCC 编译原 C 的结果相同，退出码均为 0；取消加法结果另与独立预期核对 |

旧 no-wrap 分支测试继续通过：两个版本化区域、带 label 区域的 barrier、UINT_MAX 回退和外部 goto 均保持。新报告、Clight dump、汇编及输出在 `build/native-rewrites/`，旧报告在 `build/native-demo/`。没有性能测量。

内存类新增真实 CompCert Mem 局部证明：Disjoint 编码恰好对应字节不重叠条件，合成检查接受后跨 store 的 load 值稳定，并给出 load-hoisting 的成功端点。实例拒绝不等地址但重叠的访问，接受相邻访问，拒绝 endpoint overflow。它不包含可执行 C alias guard、Clight reinsertion 或内存 rewrite 的端到端定理；访问／权限仍由独立 `Mem.store=Some` 前提承担。完整说明见 [common-rewrites.md](common-rewrites.md)。

## 2026-10-02 较早阶段：首个 Clight pass 与端到端接入

新增六个文件：`ClightGuard.v`、`ClightGuardProof.v`、`ClightEncodedRule.v`、`ClightNoWrap.v`、`GuardCompiler.v`、`ClightIntegrationExamples.v`。实际编译通过了编码与 lowering、Clight 两种入口语义的完整程序仿真、`Csem → Asm` backward simulation 和规格保持。具体的 no-wrap 编译器定理不要求源程序始终无溢出。

最终执行 `make clean` 后的 `make check-integration`，退出码 0：13 个工程 Rocq 文件全部重新编译，已有两个 Python 回归通过，CompCert proof 目标通过，新的编译器提取、构建及原生检查通过。上游 `.vo` 复用此前已完成的完整构建，没有再次清理上游。随后单独重跑构建脚本，checksum 匹配并使用缓存编译器。日志为 `build/integration-check.log` 和 `build/native-build.log`。

原版 `Compiler.transf_c_program_correct` 与新增 `compile_no_wrap_correct` 的 `Print Assumptions` 各有相同的 35 个假设名，新增集合为空。真实 CompCert 定理继承上游假设；接入前的 19 个闭合输出不能用来声称这些定理也没有假设。工程源码没有 `Admitted` 或新增 `Axiom`／`Parameter`。

提取在独立的 `build/compcert-guard` 副本中完成，并构建了实际 ccomp；OCaml Driver 调用的是 `GuardCompiler.compile_no_wrap`。提取沿用上游配置，所有 roots 一次生成。`vendor/CompCert` 源码及 sibling PolCert 没有修改。

真实 C 测试使用 [native_guard.c](../examples/native_guard.c)：

| 检查 | 结果 |
| --- | --- |
| 编译器实际命中 | Clight dump 有两处 no-wrap guard，分别在普通函数和循环内 |
| 运行输入 | `0,1,254,255,4294967294,4294967295` |
| 安全输入 | `probe=22`，两次循环后 `loop=144` |
| UINT_MAX 回绕 | 原条件通过回退执行，`probe=11`、`loop=122` |
| label 适用性检查 | 第三处带 label 的 if 没有版本化；外部 goto 返回 11 |
| 原生结果 | 汇编经 GCC 汇编／链接后运行，与 GCC 编译同一 C 文件的输出一致，退出码均为 0 |

复现目标为 `make check-integration`。证明终点仍是形式化 Asm；原生测试不把解析、打印、系统汇编器、链接器或 libc 纳入新增定理。接口、命令和当前限制见 [接入说明](compcert-integration.md)。

## 2026-10-02 较早阶段：编码、合成、rewrite 与新工具链

以下为真实 Clight 接入前的历史记录，其“尚未完成”描述对应当时状态。

最新验证使用 CompCert v3.18 的已锁定源码、Rocq 9.2.0、Stdlib 9.2.0 和 OCaml 4.14.1，版本与复现见 [toolchain.md](toolchain.md)。当前源码已迁移到 `From Stdlib`；下面 2026-10-01 的 Coq 8.15 记录只描述早期原型，不能用于重新编译当前版本。

本轮新增三个独立证明文件和一个 CompCert 桥接文件：

- `Presumption.v`：分类后的 DSL、数学语义及区间分离含义。
- `Synthesis.v`：overflow flag 与独立数学范围的对应、编码契约、合成条件在成功求值时的真/假对应。
- `ConditionalRewrite.v`：无溢出与无别名编码对应、三种 dead-branch/contradiction rewrite、完整程序有限和无限执行。
- `CompCertArithmetic.v`：用 CompCert 实际 Int 操作构造的 checked-add 原语对应。

六个独立文件从清理后状态完整编译，随后编译 CompCert 桥接；19 个 `Print Assumptions` 输出均为 `Closed under the global context`。CompCert 本身从新解压的发布源码完成 `configure`、`make depend` 和完整 `make -j4 proof`，退出码 0；没有据此声称 C 编译器可执行文件或新的 IR pass 已完成。

新增执行检查：180 个公式，在全部 8 位标量、两指针各三个代表位置上，共比较 414,720 次合成结果。成功求值时真/假均与独立 presumption 语义一致；另检查 flag 保持失败、短路、`not` 下的失败以及显式 `NoOverflow` 取反。新增完整程序比较 6,400 次，并加入范围外输入回退检查。

生成的 condition AST 在 `build/synthesized-conditions.json`，独立回归程序为 [synthesis_demo.py](../prototype/synthesis_demo.py)，并非 Rocq 提取。关键结果：

| 输入 | 事件轨迹 | 结果 |
| --- | --- | --- |
| 安全且无别名 | `[100,7]` | 正常返回，heap `[1,2]` |
| `x=255` 回绕 | `[100,900]` | 回退后保留原错误出口，heap `[0,0]` |
| `p=q` | `[100,7]` | 别名 rewrite 回退，heap `[2,0]` |

执行入口条件推断/投影、完整 condition 的实际 IR lowering、真实 CompCert 内存 guard，以及实际 IR 上下文替换仍未完成。新代码的有限/无限执行定理仍建立在总的有限 region 转移上。

## 2026-10-01：早期语义核记录

日期：2026-10-01。工作目录：`/home/hugh/research/polyhedral/guard`。本轮只在该目录添加研究说明和原型；没有修改 sibling PolCert。

## 证明编译

环境：Coq 8.15.0，编译器构建所用 OCaml 4.13.1。宿主原先没有 `coqc`，本轮将发行版软件包解压到 `/tmp/guard-coq/root`，未进行系统安装。

实际执行：

```sh
make clean
make check COQC=/tmp/guard-coq/root/usr/bin/coqc \
  COQFLAGS='-coqlib /tmp/guard-coq/root/usr/lib/ocaml/coq'
```

三个 `.v` 文件从清理后的状态顺序编译，命令退出码为 0。源码没有 `Admitted` 或显式引入的公理；以下七个 `Print Assumptions` 均输出 `Closed under the global context`：

- `contextual_replacement`
- `whole_program_infinite`
- `checked_add_sound`
- `accepts_sound`
- `overflow_conditional_correct`
- `alias_conditional_correct`
- `demo_whole_program_correct`

泛型定理仍有声明中的前提，例如 `plan_matches` 和每个插件的条件正确性；“没有额外公理”不意味着这些前提可以省略。实例文件确实构造了两个插件并证明其前提。

## 可执行回归

Python 模型独立实现相同的小型语义，不是 Coq 提取产物。结果：

| 检查 | 数量与范围 |
| --- | --- |
| checked addition | 65,536 个有效 8 位操作数对；另检查代表性的范围外操作数 |
| 局部带回退替换 | 38,400 次；全部 256 个 word 输入、两下标各 5 个位置、3 个初始 heap、2 个插件 |
| 完整程序比较 | 58,200 次；顺序、分支、错误出口、循环重入和静默循环的有限前缀 |
| 错误变体 | 7 类；朴素回绕检查、漏掉无别名条件、缓存过期 guard、错误出口、额外事件、错误 live-out、证书与原代码不匹配 |

循环重入用改变 `x` 的外围代码，使原先接受的前提在后续入口失效。正确实现重新检查并回退；缓存旧决定的变体产生不同的完整程序行为。

静默循环的 Python 检查只比较有 fuel 限制的前缀，明确返回 `prefix`，不把超时当成发散证据。无限执行保证来自 Coq 的余归纳定理。

三个可直接观察的运行结果：

| 输入 | guard（算术，别名） | 事件轨迹 | 最终 heap |
| --- | --- | --- | --- |
| `x=254, p=0, q=1` | `(true, true)` | `[100, 0]` | `[1, 2]` |
| `x=255, p=0, q=1` | `(false, true)` | `[100, 1]` | `[1, 2]` |
| `x=12, p=0, q=0` | `(true, false)` | `[100, 0]` | `[2, 0]` |

## 证据边界

已证明的是独立宏转移语义中的上下文替换，包含外围 CFG 的有限和无限执行。它不是实际 Clight/RTL 到汇编的端到端定理。

本轮未实现真实 CompCert IR 适配器、内部可能发散的片段语义、关系式内存接口、带 load 的 guard、CGO 2017 的完整条件推导/消元算法或中途去优化。guard 的 word 模型没有经过 CompCert lowering；玩具 heap 不含权限与指针语义。没有性能测量，也没有据此声称提速。

文献阅读深度逐项记录在 [survey.md](survey.md)。OOPSLA 2023 的块仿真论文目前仅核对官方摘要及作者海报，不能据此做完整接口或新颖性判定。
# signed32 仿射桥接与运行时区间检查

执行 `make clean` 后，组合目标 `make check-integration polcert-affine-proof POLCERT_SOURCE=.../verified-compilation-v10-driver` 完整通过，退出码 0。32 个既有核心／Clight 工程文件重新编译，两个 Python 回归、CompCert proof 目标、新驱动提取／构建及两个原生示例通过。随后恢复并以 `--clean` 重编译真实 Loop 的 57 个证明输入，三个原适配器及两个新增仿射桥接文件编译通过。完整日志是 `build/affine-full-integration-check.log`。

新增区间分析例子由 Rocq `vm_compute` 检查，包括正／负系数、最大安全边界、最小负数取负的拒绝、未支持除法和 unknown 在否定下的保持。`build/polcert-affine-report.json` 将桥接定理与实际 `Clight.eval_expr` 比较，二者都只列出相同的四个既有逻辑假设，新增全局公理为空。这里没有原生多面体优化或完整循环 lowering 的验证结论。
# 单层计数循环及基本指令插件

再次执行 `make clean` 后，组合目标 `make check-integration polcert-loop-proof POLCERT_SOURCE=.../verified-compilation-v10-driver` 完整通过，退出码 0。33 个核心／Clight 工程文件重新编译，既有 Python 与原生回归、编译器构建和 CompCert proof 目标通过；实际 Loop 的 57 个依赖从锁定源码恢复后以 `--clean` 重编译，原适配器、仿射桥接及两个循环／body 文件通过。日志是 `build/loop-full-integration-check.log`。

`build/polcert-loop-report.json` 的假设审计只保留实际 Clight statement 与 big-step→small-step 端点的六个既有假设及 `I.State.t/I.t/I.instr_semantics`。基本指令执行证书是定理参数，新增全局公理为空。循环输入和数学 `Zrange` 对应、空／非空范围、`INT_MAX` 上界、参数布局冲突拒绝和空 body 例子均包含在编译证明中。当前实现仍没有完整程序的多面体优化 simulation。
# 同地址读取的完整程序与原生验证

实际 `TreeCompiler.compile_property_rewrites` 已组合内存性质插件。清理工程输出后首次 `make check-integration` 完成 34 个工程证明、提取与构建、既有两组原生回归；新的 alias 检查输出与 GCC 相同，但检查函数体的脚本误读了原型声明。修正脚本后完整目标再次通过，退出码 0，日志为 `build/alias-final-integration-check.log`。

新增检查覆盖五个相同地址边界、25 个不同地址输入对、空指针前置分支、signed／volatile 排除与赋值目标别名。实际 Clight dump 含四个生成的地址条件树、候选及原表达式回退；锁定 x86_64 汇编的接受路径为一次读取，回退为两次。报告为 `build/native-alias/report.json`。`build/alias-assumptions-report.json` 对比上游与新组合的 C→Asm 端点，35 个假设一致，新增全局公理为空。没有运行时间性能测量。

# 不依赖输入区间提案的仿射 guard 合成

执行 `make clean` 后，组合目标 `make check-integration polcert-loop-proof polcert-dynamic-proof POLCERT_SOURCE=.../verified-compilation-v10-driver` 完整通过，退出码 0。35 个核心／Clight 工程文件重新编译，既有 Python、三个原生回归与驱动提取通过；实际 Loop 的 57 个锁定依赖以 `--clean` 重编译，原适配器、区间桥接、循环／body 桥接以及新的动态合成器均通过。完整日志是 `build/dynamic-full-integration-check.log`。

`build/polcert-dynamic-report.json` 记录新的检查算术与精确性端点：与 Clight 表达式基线相同的四个逻辑假设，新增全局公理为空。Rocq 例子覆盖 `2*x+1` 的接受／拒绝边界、最终值合法但中间步骤溢出的拒绝，以及不支持原子在否定下保持 unknown。检查树和实际表达式求值均有证明；这一合成器当前尚未接到原生编译器，既有单层循环仍使用输入区间方案。

# 树形原子检查的完整程序接入

新增 `ClightDecisionRule.v` 与 `ClightSignedCancel.v` 后，执行 `make clean`，随后 `make check-integration polcert-loop-proof polcert-dynamic-proof POLCERT_SOURCE=.../verified-compilation-v10-driver` 完整通过，退出码 0。37 个工程证明、独立模型、CompCert proof 目标、实际驱动假设审计、提取及四个原生 C 示例均通过；实际 Loop 的 57 个锁定依赖重新恢复并以 `--clean` 编译，全部既有桥接及复用共享树合成器的新版本也通过。日志为 `build/signed-full-integration-check.log`。

新的 signed 原生检查覆盖九个输入、五个实际插入点以及嵌套／局部赋值／goto 上下文；结果对应独立模算术计算及 GCC `-O0 -fwrapv`。`build/native-signed/report.json` 记录五个加宽检查树，源式回退保留 signed32 乘法回绕行为。`build/compiler-assumptions-report.json` 比较实际组合驱动和上游 C→Asm 定理，35 个假设一致，新增全局公理为空。实际 PolCert 多面体驱动尚未进入这个原生入口。

# 实际嵌套 Loop、公共 temporary frame 与联合优化器构建

执行 `make clean` 后，组合目标 `make check-integration polcert-nested-proof polcert-dynamic-proof polcert-optimizer-proof POLCERT_SOURCE=.../verified-compilation-v10-driver` 完整通过，退出码 0。39 个工程证明、独立执行模型、上游 proof 目标、实际 C→Asm 假设审计、驱动提取和四组原生回归通过。真实 Loop 的 57 个依赖及真实 `PolOptCorrect` 的 92 个依赖分别恢复到隔离副本并以 `--clean` 重编译；所有原适配器及新的嵌套循环桥接通过。日志为 `build/nested-full-integration-check.log`。

`build/polcert-nested-report.json` 审计递归 lowering 与任意 continuation 中的小步端点，只继承六个 Clight 假设和 `I.State.t/I.t/I.instr_semantics`，新增全局公理为空。两层相关边界循环的实际 AST、live 冲突／重复 scratch／深度不足拒绝由 Rocq 检查。`build/polcert-optimizer-adapter-report.json` 的实际优化器端点继续继承原先 42 个假设，新增全局公理与接口字段均为空。联合成功构建不表示多面体优化已进入原生 C→Asm 驱动。

# 具体数组内存实例、纯语法循环接口与真实执行例子

执行 `make clean` 后，组合目标 `make check-integration polcert-nested-proof polcert-dynamic-proof polcert-optimizer-proof polcert-memory-proof POLCERT_SOURCE=.../verified-compilation-v10-driver` 完整通过，退出码 0。39 个工程证明、独立模型、CompCert proof 目标、原生提取／构建和四组原生回归通过；57 个 Loop、92 个优化器及 60 个 CInstr/Loop 并集的锁定输入分别恢复并以 `--clean` 重新编译。日志是 `build/array-full-integration-check.log`。三份闭包的来源相同，逻辑命名空间与 `.vo` 分别隔离。

`compile_nested_raw`／`checked_compile_nested_raw` 现在把纯翻译函数与运行时执行证书分开。既有抽象端点的六项 Clight 假设及三项 INSTR 接口假设保持一致。具体数组实例的 `compile_array_nested_steps` 没有剩余 INSTR 接口假设，继承六项 Clight 假设；实际 CInstr Bernstein／CState 基线的并集为七项，包括上游 proof irrelevance。`build/polcert-memory-adapter-report.json` 记录新增全局公理为空，并检查当前全部桥接源文件的 SHA-256。

Rocq 检查了一维数组更新、单层／两层相关边界循环及四种保守拒绝。执行正例使用真正的 `Mem.alloc` 和访问权限证明建立两个数组，初始化 `B[0]=7`，证明 CInstr 和生成 Clight 均执行，并证明 `A[0]=8`。内存执行例子使用 load/store 定理；纯编译例子使用 `vm_compute`。同时核对上游标量解码拒绝：`CTy.of_compcert_arrtype type_int32s = None`。

循环与数组代码尚未进入原生驱动，完整程序区域 simulation、标量参数入口与目标进展仍是未完成义务。实际优化器假设审计继续保持原先 42 项，实际 C→Asm 编译器端点继续与上游相同的 35 项。没有性能测量。
## 2026-10-02：有限语句区域的完整程序接入

在具体数组桥接之后，新增七个接入模块。清理工程输出后，以下联合目标完整通过，退出码 0：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  make check-integration polcert-nested-proof polcert-dynamic-proof \
       polcert-optimizer-proof polcert-memory-proof \
       POLCERT_SOURCE=/home/hugh/research/polyhedral/polcert/work/verified-compilation-v10-driver
```

日志为 `build/region-full-integration-check.log`。此次重编译 46 个标准工程证明，并分别清理重编译 PolCert 核心 57、优化器 92 和具体内存 60 个源码依赖。四个适配报告均为 `compiled`，源码 SHA256 与报告一致，没有新增全局公理。

实际提取入口现在是 `RegionCompiler.compile_property_regions`。`compile_property_regions_correct` 给出完整 Csem→Asm backward simulation，假设集合与 CompCert 基线完全相同，仍为 35 项。新增的 `ClightRegionRewriteProof.transform_program_correct` 使用严格下降度量覆盖区域的内部小步，而非假定整段原子完成。

五组原生回归均通过。新增 `native_region.c` 的六个输入覆盖 guard 接受、拒绝、unsigned 回绕，以及普通函数、循环体和 goto 标签后的插入；Clight dump 明确出现三个 guard、对应候选和原始 fallback，变量重合的例子没有注入 guard。结果同时匹配 GCC 和独立 unsigned 算术计算。报告在 `build/native-region/report.json`；未测量性能。

该宿主只替换有限静默源区域，要求正常出口的全部 temps 和 memory 精确一致。内部循环、PolCert 的 private temporary/live frame 和 mutual `Mem.extends` 出口关系尚未进入这一完整程序宿主；实际多面体优化的 C→Asm 链仍未闭合。详见 [语句区域接口](clight-statement-regions.md)。

## 2026-10-02：等价内存的语言实例与宿主运输

新增五个模块后，执行 `make clean`，联合运行 `make check-integration polcert-memory-proof POLCERT_SOURCE=.../verified-compilation-v10-driver`，退出码 0。51 个标准工程证明重新编译，五组原生回归通过；具体内存闭包的 60 个锁定 PolCert 输入也重新恢复并清理编译。日志为 `build/memory-transport-integration-check.log`。

随后独立运行新增的 `scripts/audit_memory_transport.py`，退出码 0。`build/memory-transport-report.json` 确认两个抽象运输定理没有全局公理，实际 Clight 小步及有限路径运输只继承八项既有假设，均属于 CompCert 完整编译器基线。编译器端点继续为与上游一致的 35 项；具体数组适配没有新增全局公理。

覆盖范围包括普通和字节访问、bitfield、复制赋值、分配释放、完整表达式及两种函数入口，直到真实 Clight 小步与有限路径。此次只是建立并复用语言提供的性质库；完整程序区域替换的出口仍要求精确内存，尚未升级为双向 `Mem.extends`。详见 [运输接口及边界](compcert-memory-transport.md)。

## 2026-10-02：区域的等价内存出口进入完整编译定理

放宽 `region_contract` 和作者接口的出口关系后，执行 `make clean`，联合运行 `make check-integration polcert-memory-proof POLCERT_SOURCE=.../verified-compilation-v10-driver`，退出码 0。51 个标准证明和 60 个锁定 PolCert 依赖清理重编译，五组原生回归全部通过。日志为 `build/memory-region-integration-check.log`。

`ClightRegionRewriteProof.transform_program_correct` 现在使用对齐状态见证和 Clight 路径运输，允许入口、暂停状态和出口保持双向 `Mem.extends`。局部候选和后续上下文可以产生不同的内存记录；最终 temps 仍精确相同。新增正长度路径运输保持模拟进展，内部停顿继续由严格下降度量排除。

更新的 `build/memory-transport-report.json` 审计实际区域模拟和三个运输端点，只继承八项基线假设；`build/compiler-assumptions-report.json` 仍与 CompCert 完整编译器相同，为 35 项。既有规则通过关系自反性适配，因此原生示例验证的是原有变换在新宿主中继续工作，尚不构成真实 PolCert 片段重排的原生实例。内部循环及 private temporary/live frame 仍未覆盖。

## 2026-10-02：CInstr 调度包到完整程序的接口证明

新增 `PolCertScheduleRegion.v` 与常量数组 store 解码／生成证明后，运行 `scripts/polcert_core.py memory-adapter --profile memory`，退出码 0，日志为 `build/schedule-region-adapter-check.log`。适配层七个隔离依赖和五个源文件重新编译；60 个源码输入沿用前一条清理重编译的锁定闭包。这次没有重跑未变更的原生驱动。

`build/polcert-memory-region-adapter-report.json` 单独审计真实 CInstr 实例的 `package_rule`、完整 Clight 模拟和完整 C→Asm 编译端点，假设并集与 CompCert 基线相同，为 35 项，没有抽象 INSTR 接口假设或新增全局公理。解码、条件调度证书及候选生成是调度包必须携带的局部证明字段；没有将它们改为公理。

`constant_store_inv` 和 `constant_store_run` 已覆盖经过边界检查的普通 signed32 数组常量写入，连接实际地址、真实 store 与两侧 Clight 正常执行。当前具体调度包数量仍为 0，原生驱动和真实多面体优化器接入均为 false；完整编译接口证明不能代替具体片段实例和内部循环宿主。详见 [调度包接口](polcert-schedule-regions.md)。

## 2026-10-02：具体双写重排的 CInstr→Clight→完整程序链

新增 `ClightSyntaxEquality.v` 和 `PolCertStoreSwap.v` 后，执行 `make clean`，联合运行 `make check-integration polcert-memory-proof POLCERT_SOURCE=.../verified-compilation-v10-driver`，退出码 0。52 个标准证明和 60 个锁定 PolCert 输入清理重编译，七个隔离适配依赖及六个实际源模块编译通过；五组既有原生回归通过。日志为 `build/store-swap-integration-check.log`。

实例的 `actual_cinstr_store_swap` 调用真实 `bc_condition_implie_permutbility`，生成两次逆序 store 及等价内存出口；实际源执行解码和候选生成义务均在本实例中构造。`compile_store_pair_correct` 经通用区域宿主达到 Csem→Asm。`build/polcert-memory-store-swap-report.json` 将这一具体端点与 CompCert 基线比较，两者都为相同的 35 个假设，没有 INSTR 接口公理或新增全局公理。报告中的源 SHA256 与当前源码一致。

Rocq 例子验证接受、重合下标、越界、源 AST 不匹配和前端结合方式；另以实际八字节分配及权限证明构造源／候选执行，并证明候选最终的两个元素为 7、8。语法绑定检查本身没有全局公理。

该实例仅处理一个数组的两次普通 signed32 常量写入，使用静态独立性条件；尚未运行提取后的原生重排驱动，也没有接入真实多面体优化器或循环区域。上述五组原生回归属于既有默认驱动，不是新实例的原生验证。泛型调度包的具体包数量仍为 0；新实例直接提供区域证书。

## 2026-10-02：真实 CInstr 双写重排进入原生驱动

新增 `PolCertStoreNative.v`、可选提取入口和原生套件后，执行 `make clean`，联合运行 `make check-integration polcert-store-native POLCERT_SOURCE=.../verified-compilation-v10-driver`，退出码 0。52 个标准证明与 60 个锁定 PolCert 输入清理重编译；七个隔离适配依赖和七个具体模块均通过。两套驱动分别提取构建，五组默认原生回归和新双写套件都通过。日志为 `build/store-native-integration-check.log`。

新入口 `PolCertStoreNative.compile_correct` 对任意数组标识符给出 Csem→Asm backward simulation。驱动传入前端 `a` 标识符作为普通数据；具体命名接口没有未实现的提取公理。独立假设审计确认原生入口与 CompCert 基线同为相同的 35 项。原生检查验证普通函数、循环体、goto 标签后三个实际交换，并验证五个排除情形；结果匹配 GCC 和独立预期输出。

当前选择器要求恰好两条写入的语法子树，可消费显式语句块的前端结合方式；它不截取任意长序列中的相邻写入。静态独立性条件仍是编译时检查，尚无此实例的动态 alias guard、内部循环区域替换或真实 PolOpt 接入，也未测量性能。
