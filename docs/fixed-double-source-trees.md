# 常量上界：源／模型桥已证明，安装继续交付

本页保留局部 source 证明 checkpoint。[Factory／完整程序后继](fixed-double-installation.md)
已闭合该阶段的安装证明，第一次原 `nodep` 运行仍走 fallback；
[I32／I64 literal 后继](typed-literal-double.md)按其实际 AST 类型补充语言服务。
后续功能与 native 验收以这两页为准。

本页供 framework／语言／优化实例的实现者阅读。新服务处理实际 Clight 中的
常量上界循环树，复用已有多面体模型和候选 pipeline；目前完成局部源证明，
尚未安装到 native compiler。[证明摘要](fixed-double-source-trees.json)记录这个边界。

2026-10-10 用 `git ls-remote --heads origin` 核对 narrative 分支：可见最新仍为
`8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9`，
[paper-narrative.md](topdown/paper-narrative.md) 与 main 一致。这里落实该版本的
source/model 方向、前提来源和三方责任澄清，不声称取得另一份新提交。

## 对实际源的支持边界

`fixed_double_source_tree` 保留原 sequence、不同深度的循环以及实际 scalar／
global-double-array instructions。每个 range 保存原 bound expression；checked
decoder 核对完整 source AST，要求 bound 在空控制环境中解码为常量仿射表达式，
且最终数学值在 I32 signed range。Initializer 是原 I32 constant 的 I64 cast，
循环为 strict upper comparison 与 unit increment。它没有接纳 `k=j` initializer、
loaded／fixed 混合端点或任意依赖外层 iterator 的 bound。

投影 `fixed_double_tree_skeleton` 让既有 source Loop、footprint、candidate 和
出口服务可以消费固定 bound。它为数学常量建立 parameter name；这些名字只
索引数学参数，不声明 C global，也不生成 header load。相同常量共享一个 slot。
实际机器参数由已证明的 private I32 constant assignments materialize。

这个路径将用于关闭原 `nodep` 的常量上界识别缺口。当前没有原 `nodep` 的新
decoder／candidate／installation 运行证据，因此不增加 native 源族或 requested
transformation 支持计数。常量 facts 可以完全静态建立；这也不增加 OLO 动态
入口条件构造能力。已有 loaded-bound 路线仍承担相应动态检查。

## 证明方向与前提来源

`fixed_double_source_tree_source_Loop` 在 checked syntax、shared layout、scope、
model facts 和 control-entry words 下证明：实际 Clight 的有限正常执行，当且仅当
source Loop 具有对应执行，并且真实 temp exit 等于计算出的 source exit。
IEEE values 和实际 `Mem` 的关系复用已有 point execution；没有以 word-copy
替代原计算。该 iff 不声称无条件完整行为等价，独立 source progress protocol
另由 `fixed_double_source_tree_region_progress` 提供。

| 前提或结果 | 当前证明来源 | 安装时必须交付的生产者 |
| --- | --- | --- |
| 原 AST、bound decoding、控制 freshness、layout consistency | checked decoder soundness | static factory／site checks |
| 原 bound 的实际 I64 modular 求值及最终表示范围 | affine endpoint execution 与 checked I32 bound | 语言算术服务，由 domain decoding 消费 |
| 所有到达 point 的数学 footprint／cell resolution | `fixed_double_tree_footprint_model_facts` | domain factory，消费 static footprint、真实 globals 和 scope |
| prefix words 与准确公开出口 | source execution/model theorem | 语言 source bridge，factory 接到 actual entry |
| source control／progress | 独立 framed／region progress 服务 | language host 的 supported-site producer |
| 私有参数 words、数学 values、其他 temps 不变 | `fixed_double_cache_*` | 语言 private-state 服务，factory 生产 distinct／fresh slots |
| actual candidate 正确性 | 既有 source-aware phase 与最终 checker 接口可复用 | 新 factory 必须实际调用并消费结果，尚未完成 |
| 当前程序安装和 Csem→Asm | 既有 scoped host／backend 可复用 | 新 compiler endpoint 必须消费此路径，尚未完成 |

表中的 source execution 是 correctness proof 的起点。运行时无需先执行 source
来建立它。`fixed_double_tree_footprint_model_facts` 仍要求 `preserving_globals`、
`double_source_tree_scope` 和 box facts；局部 theorem 不代替 factory 对这些
义务的 discharge。数学 footprint 不等于 `Mem` permissions。实际 modular
execution 与数学 final-value representability 也分别证明。

## Framework、语言和优化实例的责任

最小 kernel 不变，仍消费 guard／conditional correctness 证书，止于局部 guarded
correctness。此次扩展没有加入新的 host law 或全局公理。条件处理和 source/model
服务属于 kernel 之上的库。

语言／host 提供真实 execution、private/public frame、准确出口、安全 machine
encoding 及合法安装。优化实例提供 source-to-model 的结构、footprint 到局部
义务的推导，以及实际候选的验证。已支持族的 C 源使用者只提交标注与策略数据；
新 factory 应自动生产并组合证明，不要求使用者补语义 callback。

## 下一项交付

先用真正 array globals 建立 scope 和 static layout。数学常量的 parameter names
不能成为 `locals_avoid` 的 C header obligations，也不能引入伪造 global symbols。
然后连接 private constant cache、实际 checked candidate lowering 和 source exit
restoration，证明新 projected region contract，复用现有 selected host。

安装阶段要让 literal normalization 与新 pass 消费实际 intermediate program，
再接已有 combined compiler／CompCert backend；为原 `nodep` 保留 source、model、
phase、candidate、guard／常量前提、最终安装与完整输出，并检查标注选择和公开
出口。完成该链后才增加支持计数。`dsyrk` 的 outer-control initializer、general
pieces／ISS、更多 tiling phases 和 CGO17 compact condition／成本继续是未完目标。

## 验证

七新模块共 702 行，16 次编译尝试中七成功、九失败；每次日志与源快照保留。
审计查询 28 个端点，其中 27 个在新模块声明，一个是复用的 canonical progress
端点；九个查询 closed，最多六个既有 globals，没有新增 globals。Audit 绑定
292 个 reachable sources 和 10,783 个文件；这不是 native compiler build 或
新 whole-program endpoint 的验收。
