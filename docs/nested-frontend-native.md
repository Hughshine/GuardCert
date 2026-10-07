# 实际 Figure 2 适配源：nested compiler 与候选执行

2026-10-07，接续 `e0f5902` 的 [nested candidate／完整程序证明](nested-constant-multi.md)。
新的 frontend、编译入口和提取 driver 现已接受既有
[olo_figure2_adapted.c](../examples/olo_figure2_adapted.c)，实际安装并运行 identity、
interchange 和 2×3 tiling。原八个 C 调用和源文件未修改；先前 16-call
`not-supported` report 保持原有 producer／compiler 边界，新结果单独记录。
这是固定 16×16×5 flat layout、替换 arithmetic BODY 的适配，不是完整 NPB BT。

## 接入接口与语言证明

CompCert 保留 `shape[0]` 的 `*(shape+0)`，并在内层 reset 前保留 `Sskip`。
它们与先前 instance 的规范源存在真实 AST 差异，不能在不受信任 descriptor
中删除后声称仍是原程序。`ClightZeroIndexHeader` 证明零偏移的实际读取、控制
表达式和循环执行对应；`ClightExecutionCongruence` 提供 skip-prefix、sequence
和 strict-loop body 的可复用执行同余。它们对具体 trace/outcome 的对应成立，
没有预设未来 bound 稳定性。

`ncs_frontend_source indexed shape` 现在描述实际两次 prefixed reset 和三层 loop。
`ncs_frontend_execution_equivalent` 将实际源运到旧 source/model 证明；
`ncs_frontend_region_contract` 从已证明的 guarded execution 恢复**原 frontend AST**
作为 fallback。因此 guard 允许使用规范读取模板，refusal 仍运行原始两次 array
loaded-plus-offset headers。原 host 核对实际源 progress 和 placement。

[ClightNestedFrontendFactory.v](../prototype/interface/ClightNestedFrontendFactory.v)
接收不受信任 `describe`：返回 indexed-root 选择、parameters、affine proposal 和
shape 数据。Factory 重查实际 source AST、typed private resources、原 site、
candidate lowering 和 bounded validator，没有执行／未来 stability 的语义回调。
使用者自行发现片段和提出候选，支持集由实际 checker 决定。

`GuardNestedFrontendCandidate.ml` 是当前示例 discovery 算法：识别同 pointer 的
两个 constant-index loaded headers 和 literal 第三维，从 private pool 选缓存／
helpers，构造规范 model，调用既有不受信任 range proposer，保留两套扫描变量，
然后提出候选及可检查 evidence。它不是 trusted assumption extractor。
当前 root profile 从 row=0 开始；有序 positive gates、numeric/profile 检查、
完整 source-licensed stability scan、多数组 alias-only guard 继续由既有实例提供。

[ClightGuardedNestedFrontendCompiler.v](../prototype/interface/ClightGuardedNestedFrontendCompiler.v)
的 `compile_ncs_frontend_regions_correct` 将该 factory 经语言 region host 和
CompCert backend 接到实际 Csem→Asm backward simulation，前提是编译成功返回
`mayReturn ... (OK target)`。提取 driver 正在调用这个端点，源码／对象、entry、
driver、native proposals、oracle、compiler binary 和 reports 均绑定摘要。

## 运行与验证

在当前已验证的父阶段和 Rocq 9.2／CompCert 3.18 工具链上：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make nested-frontend-native
python3 scripts/probe_nested_frontend.py
opam exec --root=/tmp/guard-opam --switch=guard -- make nested-frontend-validate
```

GDB probe 需要本地子进程 ptrace 权限；当前默认沙箱下 inferior 启动返回 127，
已在允许本地调试的执行环境中运行并完成。`--validate` 只核对已有结果与绑定。
本阶段没有验证全新 checkout 的 empty-build bootstrap。

新 proof closure：20 endpoints（17 language／1 domain／2 fixture）、569 required
dependencies、1,104 源摘要；kernel 闭合，新 compiler 仍与父 compiler 使用同一
42-global assumption 集合，零新增 global axiom。父 multi 源／对象保持。
这些 proof-stage report 的 pending/native 标志是生成该阶段时的范围；实际运行
能力由下面的新 native／path reports 给出。

Native matrix 六配置，每配置八调用，共 **48 full assembly calls**：disabled、
identity、interchange、tile-2-3、wrong-reindex、invalid-domain。identity、interchange、
tiling 三种候选配置安装成功；disabled 和两个无效候选保持原
三层 loop。每次检查全部 2,048 个 output words、两个 headers 和公开 row/column/
component exits；GCC wrap reference 与独立 source word model 同时作对照。

Interchange／tiling 的 instrumented Clight 各八调用，共 **16 calls**；每配置
两个独立-array cases 走 fast、六个 alias/empty/wrapped-root paths 走 fallback。
这份证据与 actual assembly probes 分开，不把 GCC 插桩结果称作 machine path。

为区分 tiling 的遍历顺序，另外三个配置使用保留全部 kernel/context prefix、仅
增加 `(view=0,u=2,v=3)` main 调用的 harness。共 **27 full assembly calls** 对照
完整输出。三次 active GDB probes 在 output indices 15、80、160 上设置 watchpoints，
观察这三个位置的写入顺序如下；公开出口都为 `[3,4,5]`。表中不是全部 BODY stores：

| 配置 | 三个被观测 output word indices 的写入顺序 |
| --- | --- |
| disabled | `[15,80,160]` |
| interchange | `[80,160,15]` |
| tile-2-3 | `[80,15,160]` |

另三次 GDB probes 观察 first-header 和 second-header-region 的原源回退：first
alias 的写入 `[0,1,5]`、出口 `[1,2,5]`；second region 的写入 `[5,80]`、出口
`[2,3,5]`，未出现 cached domain 会访问的 index160。共 **6 machine probes**，
不加到普通 75-call assembly matrix 数中。调用完成后公开出口与模型一致。

当前配置中 `bt_excerpt` 的 machine bytes 为原源 161、identity 528、interchange
564、tiling 693；这是代码尺寸观察，不是 guard 成本或性能改进结果。

| 报告 | SHA-256 |
| --- | --- |
| `build/nested-frontend/proof/report.json` | `bf12d374fad912538dd16a9e71aae6366106fa44fe4ae9eb3ffb2f280252759c` |
| `build/nested-frontend/native/report.json` | `8665f46362aa85b53e23074469f6d67809cee504f9f91e64e80e3e139ca62859` |
| `build/nested-frontend/native/path-report.json` | `6e00c1b3cd85dfa1de46385e6b8ca80e3b07658516d7932d84e0a2c8cb685039` |

## 尚未完成的完整目标

此实运行关闭了适配源的 candidate 安装缺口，尚不支持完整原 BT 的动态布局／
delinearization。新 nested profile 的多数组 read/write BODY、真正 dependence
的静态拒绝、same-allocation slices、非零初始 row、未定义 BODY 参数、重复
rewrite／更多 control contexts、完整 fresh-build 流程还需实际验证；旧 loaded-root
路径对应结果不自动计作这个 frontend 的测试。

之后继续 compact 条件、guard work／完整运行成本、接受域、compile time／code
growth，以及同例作者责任与近邻比较。数学上概括的 footprint 条件仍须证明实际
pointer 比较和 dependent reads 安全，不能靠假定 cached future execution 执行
检查。没有 timing、speedup 或 proof-author effort 结果，完整目标保持 active。
