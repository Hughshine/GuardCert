# 2026-10-07 阶段：实际 nested C frontend、候选提取与 assembly 行为

父阶段 `e0f59021a59e2aed1add1859b0ef4a4f47f93435` 已有完整 nested candidate／host
证明，但尚无新入口提取与实际候选运行。本阶段把既有
[olo_figure2_adapted.c](../examples/olo_figure2_adapted.c) 接入实际提取 driver，
安装 identity、interchange、2×3 tiling，并验证正常与回退行为。源文件、原八个
main cases、旧 16-call `not-supported` coverage report 保持；新结果另立报告。

重新 fetch 的 `origin/topdown/research-positioning` 为
`271f6fc941910456da43a76e9f0eed38e8a5e200`，narrative 与 main 无正文差异。
其三方责任、四条证书链、最小 kernel 的局部边界和 proof-first／usability
双重验收继续作为实现和论文的约束。完整目标 active，本阶段不等于最终完成。

## 实际源与原证明之间的桥

CompCert frontend 的 root 是 `*(shape+0)+1`，内层 reset 保留 skip prefix。
新增 `ClightZeroIndexHeader` 和 `ClightExecutionCongruence` 证明真实表达式、
sequence／loop 的执行对应，保持 trace、memory 和 outcome。
`ncs_frontend_execution_equivalent` 运输实际源到旧规范源；
`ncs_frontend_region_contract` 利用对应恢复原 frontend AST 作为 fallback。
不受信任 discovery 不能自行删除 AST 后宣称检查了原 source。

`ClightNestedFrontendFactory` 消费 shape／parameters／proposal 数据，重查实际
source、typed pool、原 site、candidate validator 与实际 lowering，不收新的
source/model 语义回调。`GuardNestedFrontendCandidate.ml` 识别本实例的两次
constant-index loaded headers 和 literal 第三维，选择私有缓存／helpers，
调用既有 range proposer 和 candidate producer。它的识别逻辑不属于可信基。

实际提取入口为 `ClightGuardedNestedFrontendCompiler.compile_ncs_frontend_regions`。
`compile_ncs_frontend_regions_correct` 在 `mayReturn ... (OK target)` 前提下给出
完整 Csem→Asm backward simulation，消费已有 signed-expression region host。
局部安全仍消费原 source silent normal completion；整程序的 progress／安装
责任由语言 host 提供，不能把二者混为一个结论。

| 证书环节 | 本实例交付方与复用点 |
| --- | --- |
| `C_opt` | 优化实例复用 affine candidate checker、实际 window backend、public-exit restoration |
| `C_derive` | Domain producers 从原源 prefix／stability scan 得到 cached model，并运输到实际 checked entry |
| `C_guard` | 语言的实际读取／比较和私有状态证明，结合 domain 的 numeric／scan coverage，证明检查安全及接受充分性 |
| `C_host` | 语言的 guarded choice、frontend 执行同余、typed resources、placement／progress 和完整编译接入 |

最小 kernel 只组合已有证书，本阶段未改。前提发现和候选构造继续由实例作者提供；
框架没有新增通用 assumption extractor、任意 WP 或最优 guard synthesis。

## 验证与证据边界

20 个新阶段端点：17 language、1 domain、2 fixture；569 required dependencies，
1,104 source digests。父 nested multi 源／对象保持。Kernel 闭合；新 compiler
保持原 42-global assumption 集合，零新增 global axiom。提取 stamp 绑定实际
entry、driver、proof sources／objects、native proposals、oracle 和 compiler binary。

六配置 native matrix 共 48 full assembly calls；追加一个 input 的三配置 harness
共 27 calls。75 calls 均对照全部 2,048 output words、两个 headers、公开 counters，
同时使用 GCC wrap reference 和独立 source word model。无效 reindex／domain
提议静态不安装候选，disabled 保留原三层 loop。

16 instrumented Clight calls 单独记录：interchange／tiling 各两个 fast、六个
fallback。6 个 GDB machine probes 观察未插桩 assembly，单独计数。独立-array
输入在 indices 15、80、160 上的 watchpoint 顺序分别为 source `[15,80,160]`、
interchange `[80,160,15]`、tiling `[80,15,160]`；公开出口均 `[3,4,5]`。这是三个
被观测位置的顺序，不是全部 BODY stores 的日志。其余 probes 检查 first-header
和 second-header-region 回退，包括未执行 cached domain 会访问的 index160。

当前函数代码尺寸为 disabled 161、identity 528、interchange 564、tiling 693 bytes。
这是代码增长观察，没有 timing、guard cost、profitability 或作者负担结果。
GDB 默认沙箱启动失败 127 后，在允许本地子进程调试的执行环境中跑完；
`--validate` 只读核对现有结果，不重新运行调试。没有全新 checkout bootstrap 验证。

| 报告 | SHA-256 |
| --- | --- |
| `build/nested-frontend/proof/report.json` | `bf12d374fad912538dd16a9e71aae6366106fa44fe4ae9eb3ffb2f280252759c` |
| `build/nested-frontend/native/report.json` | `8665f46362aa85b53e23074469f6d67809cee504f9f91e64e80e3e139ca62859` |
| `build/nested-frontend/native/path-report.json` | `6e00c1b3cd85dfa1de46385e6b8ca80e3b07658516d7932d84e0a2c8cb685039` |
| `build/paper/report.json` | `3640e3a4d44e8d342c4b002ac6e91e54829cc8cc0e6bce0e11ace0a5ab143257` |

运行和复核命令见 [nested frontend 说明](nested-frontend-native.md)。
`make nested-frontend-validate` 已通过；论文更新 abstract／intro／case study／
evaluation／conclusion 和 evidence map，离线编译 12 页，无 unresolved references／
citations 或 overfull boxes，改动页已渲染检查。Paper build 不代替 Rocq／native 审计。

## 接下来的验收

先在这个新 frontend 上验证 multi-array read/write BODY、真实 dependency 拒绝、
same-allocation slices、非零 row、未定义 BODY parameters、重复 rewrite／control
contexts，再交付 fresh-build 路径。旧 loaded-root 的 matrix 不替代新入口覆盖。

之后在同 source／candidate 上比较 scan 与 compact sufficient condition：证明
每个实际 primitive 的安全／partiality、dependent reads 的次序和接受充分性，
测量 guard work、完整运行成本、接受域和 compile time。将 kernel／语言复用、
domain 库和 site-specific obligations 分开，与近邻接口做同例作者工作比较。
当前仅固定 16×16×5 flat layout 的 Figure 2 适配；完整原 BT 的动态布局／
delinearization 和更广 OLO source class 仍是明确差距。
