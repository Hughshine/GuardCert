# Literal promotion 接入实际 guarded compiler

原 `fusion5` 的第一段循环含 `2 * A[i+2][j+2]`。Clight 保留 signed
integer literal，而已有 double expression decoder 要求浮点运算的 operands
均为 F64，导致该循环在 scheduler 之前被拒绝。本后继在标注区域内规范化
受支持的 assignment RHS，随后将**实际中间程序**交给原 quotient compiler。
原数组、IEEE 计算和完整状态观察保持；未替换原 benchmark。

## 局部变换及其证明

`GuardMemoryDoubleLiteralOperands.normalize_double_literal_operands` 只接受
signed I32/I64 literals、F64 leaves、由 C 实际 promotion 到 F64 的
`+ - * /`，以及浮点 negation。Literal 使用 CompCert `Float.of_int/of_long`。
保留运算树和 array-read occurrences；不将整数子树改成浮点运算。Unsigned
operands、动态整数 operands 或其他不支持的结构保守返回 `None`。

`normalized_double_literal_operands_forward` 从**实际原表达式执行**及 assignment
cast 得到规范化表达式执行，保持同一 memory 和结果。它是一个有明确方向的
定理，不宣称为独立双向等价。`selected_double_literal_assignment_execution`
将该定理用于实际 assignment，包括原 lvalue、cast 和 store。

`DoubleLiteralSelectedNormalization` 给出 projected region contract，并通过
已有 scoped selected host 证明 `normalize_selected_double_literals_correct`。
只在选中标签内访问 assignments；无新增 private temps 或 globals。Scope、
public-temp transport、memory relation 和有限 assignment progress 均在证明内
闭合。C 用户不提供逐 site semantic callbacks。

这是无条件正确的 preprocessing，不是新增 runtime guard。原 source execution
是局部正确性证明的起点，不是编译器发出的预执行检查。

## 与条件优化及完整程序组合

实际链路为：

```text
SimplExpr / SimplLocals 得到实际 Clight P
  -> 标注 assignments 的已验证 normalization 得到 P1
  -> 当前 P1 上提议、检查和安装 quotient tiling 得到 P2
  -> 后续 passes 消费其实际 intermediate program
  -> CompCert backend
```

`LiteralQuotientDoubleTiledCompiler` 将 normalization simulation 与原
partitioned quotient compiler simulation 组合，交付
`compile_selected_literal_quotient_tiled_stable_program_correct` 的
Csem→Asm backward simulation。Candidate 的最终 polyhedral checker、实际
Clight lowering、安全 capture、公开 iterator exits 和 source fallback 都保留。
后续 guard 的 fallback 是**当前规范化 source**；与最初 C 程序的关系由前一
simulation 提供，而非要求 fallback 的 AST 与 parsed 原输入完全相同。

## 责任与 narrative 对照

再次 fetch 的 narrative 为 `8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9`，
两份 topdown 正文与 main 一致。这里落实其已有澄清：

| 责任方 | 本后继承担或复用的义务 |
| --- | --- |
| Minimal kernel | 局部 guard certificates/composition 的边界不变；本 preprocessing 未冒称为 `guardify` 的直接调用 |
| Clight language/host | 实际 promotion/cast/assignment、state transport、finite progress、选中 site 安装及 backend composition |
| Polyhedral domain | 已有 actual source/model/candidate、dynamic quotient relation、最终 validator 和 lowering；在规范化后的真实程序上运行 |
| 源码使用者 | 提供 C、`scop` 标注及策略；不提供内部语义证书 |

最难的任务仍是将实际源语义、入口条件、安全 checks、候选执行和 continuation
连成完整证明链。本轮解除其中一个真实 syntax/representation blocker，没有
声称 framework 能普遍推断 assumptions。

## 已核实证据与剩余验收

三个新模块共321行、八个新端点；完整十五模块链1,414行、29端点，三个闭合，
最大42个既有 globals，没有新增全局假设。审计绑定518个可达源文件及失败
尝试。Native build 真正提取并调用 normalization，再调用原 guarded optimizer。

原 `fusion5` 已安装第一段循环的 quotient tiling，完整30,201个 array values
的摘要与原 GCC 参考一致；保留 scheduler、raw/generated Loop 与 quotient
receipts。24项 disclosed variants 全部通过：I32/I64及其上界和 rounding、混合
operation tree、negation/signed zero、unsigned与integer-subtree拒绝、错误候选、
资源拒绝、未标记、多标记、动态 tile boundaries／空循环及公开 I64 exits。

第二段的 `N-j` 下标仍不在当前 access decoder 的表达力内。本轮只支持第一段，
不能宣称整个 fusion5 的 transformations/configurations 已覆盖。独立 bounds、
非零／inclusive headers、statement sequences、scalar reads/writes和其他顺序
phases，原 BT／LLVM／SPEC及 larger tiers 仍属于 active goal。

同一 build 完整重放62原例＋两份既有适配：60 raw＋2 adapted输出匹配GCC，
两个既有frontend拒绝，零timeout/mismatch。15原例31处安装，其中12原例28处
quotient，另三处initialized；前一build的全部安装保留。20项initialized
regressions亦通过。43个已编译原例未进入tiling phase；`tricky2`、`tricky3`
进入phase但未安装。单独trace确认tricky2的两个scalar-update loops已进入
producer，却在candidate生成之前因 `missing tiled point space` 拒绝；这不是
最终validator拒绝，也不是完成scalar optimization。

其他goal命令全部结束后，对本build原fusion5做一次warmup和七组交替完整调用。
Optimized/unmarked medians为0.004334／0.004428秒，比值0.978860；同compiler和
flags，复制原assembly，全部输出匹配GCC。计入启动、初始化、两段region和
digest，未隔离guard，未控制affinity/外部host load。这种短调用和单轮测量
不建立稳定加速或benchmark范围收益。前一quotient build的polynomial比值
1.300657仍属于前一binary，不重标成本后继结果。

固定[aggregate](double-literal-operands.json)绑定proof、build、原输入／完整语料、
24＋20上下文、producer拒绝和成本报告；重跑验证：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/summarize_double_literal_native.py --validate
```

下一source扩展先处理含参数的access rows及原read到capture的实际稳定性／执行
运输，同时补rank-one／scalar producer的point-space契约。之后继续独立bounds、
其他源结构、顺序phases、OLO功能和useful effects；没有缩小完整goal。
