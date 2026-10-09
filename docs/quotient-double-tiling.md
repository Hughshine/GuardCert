# 动态 quotient bounds：可运行 compiler 与完整程序证据

2026-10-09。重新 fetch `topdown/research-positioning` 后，可见提交仍为
`8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9`；[narrative](topdown/paper-narrative.md)
及 context 正文与 main 一致。本阶段完成了[前一证明检查点](quotient-parameter-installation.md)
所列的 native 接线和验收。前一固定摘要仍记录当时只有证明的范围；本阶段的
[固定摘要](quotient-double-tiling.json)独立绑定19份报告、17,799个文件。

当前 compiler 为 `build/quotient-double-tiling/compiler-attempts/native-v5/ccomp`，
SHA-256 `727876833bf3dda8737791e9f9d762b53f6c370c36f0bf436976996c5b287885`。
它使用新的 `PartitionedQuotientDoubleTiledCompiler` 入口和对应的完整
`Csem→Asm` backward simulation。Kernel 和语言 host 定律不变；策略与候选
仍可不受信任，实际候选必须通过最终 checker。

## 用户得到什么

支持族的用户提供含 `#pragma scop` / `#pragma endscop` 的 C 和 tile 策略，
无需手写目标 loop 或逐 site semantic callbacks。实际 PolCert/Pluto 路线执行
affine scheduling、rectangular tiling、intra-tile scheduling 和 codegen。
Adapter 从 raw candidate 提议依赖 private quotient 的边界，最后验证实际
adapted body，并安装 guard、candidate、原 source fallback 和公开出口恢复。

例如原 polynomial 保留 IEEE 表达式树、数组和 I64 控制。先安全捕获 n；只有
范围检查接受后才执行 private `q=(n+31)/32`。最终模型环境为 `[q,n]`，验证条件
包括 `0<=n<=limit` 及 `0<=32*q-n<=31`。真实生成 Loop 的两个 tile prefix
上界为 `2*q` 和 `q`。原输入 n=4096 得到 q=128；n=31/32/33 得到 q=1/1/2。
局部宽度仍为32，点 membership 和 prefix pruning 均在实际生成代码中。

以下命令使用当前冻结 compiler；输出使用新路径：

```sh
GUARDCERT_ORIGINAL_MODE=tile GUARDCERT_DOUBLE_TILING_MODE=tile \
GUARDCERT_TILE_SIZES=32 \
GUARDCERT_PLUTO="$PWD/build/polyhedral-pipeline/pluto-source/tool/pluto" \
build/quotient-double-tiling/compiler-attempts/native-v5/ccomp \
  -fall -stdlib build/quotient-double-tiling/compiler-attempts/native-v5/runtime \
  -dclight -S -o /tmp/guardcert-polynomial.s \
  build/benchmark-alignment/probe-v1/polynomial/marked.c
gcc -no-pie /tmp/guardcert-polynomial.s -lm -o /tmp/guardcert-polynomial
/tmp/guardcert-polynomial
```

标注只是请求尝试。Unsupported syntax/resources 或无效候选仍可静态拒绝；
运行时 n 检查拒绝时，跳过 quotient capture 并执行原 source。新路线静态拒绝后，
compiler 仍可尝试已支持的旧路线；两者安装独立计数。

## 三方证明责任及实际接线

| 责任 | 本阶段由谁交付 | 被消费的证据 |
| --- | --- | --- |
| 局部 guarded 组合 | 最小 kernel 的既有接口 | 抽象 check、entry relations 和 conditional/preservation certificates；本阶段未修改 kernel |
| `C_opt` 与模型前提 | Domain 的 actual source/model 桥、PolCert checker | 原 source 参数扩展；在同一实际 `[q,n]` 上验证 source 与最终 candidate；不是只检查 raw schedule |
| `C_derive` | Domain factory | 既有 footprint/range 证据加 exact affine quotient relation，推出候选的入口与全部 reached-point 义务 |
| `C_guard` 与入口运输 | Language arithmetic/capture 服务，由 factory 组合 | 实际安全 Clight division、typed view/ranges、fresh private q、memory/events/public frame、accept/refusal transport |
| Concrete choice 与完整程序 | Clight region factory、scoped host、CompCert backend | candidate lowering、精确 public exits、原 fallback、source progress、当前 program 的 scope/resources 和 Csem→Asm |

`compiled_double_ceil_capture_execution` 给出真实 q capture；guarded execution
消费其 relation，经 `DoubleQuotientModel.quotient_relation_exact` 取得数学值。
参数插入定理保持实际 source Loop 执行，最终 checker 消费受该 relation 约束
的实际 source/candidate。随后接实际 Clight lowering 和公开 iterator 恢复。
源执行是证明的起点，不是优化前 runtime 预执行。

新的 compiler 定理还量化
`fallback_phase : Clight.program -> OpenScop -> result ...`。它先执行 quotient
pass，把实际中间 program 交给 resolver，再以产生的策略调用旧 passes；每次
旧候选仍经过既有检查。证明不要求 resolver 正确识别所有 guard，不添加 host
前提，也不把旧 program 的 site 证据用于新 program。

这些路径直接构造 Clight 分支和 simulation。Kernel 未改、导入 generic 模块，
不等于新的 compiler proof 直接调用了 `guardify` theorem。Condition 服务及
参数 relation 的真实消费是本阶段可核对的复用。

## 一个 repeated-rewrite 问题及修复

首个 native build 实际已安装 q capture 和 q-dependent bounds，但之后的旧
pass 又优化了 q guard 的 false branch。旧 observer 要求 false branch 是 raw
source，因此报告 quotient=0，并把内部旧 guard 计为旧路线。这不是 q validator
拒绝；named trace 后继明确记录 final validation 和 lowering 接受，导出的 Clight
也有真实 quotient。额外版本还增加 capture/代码，偏离默认策略的原 fallback。

当前 resolver 在实际中间 program 中识别 q guards，用其 actual source descriptor
重新 extract/export OpenScop，建立不可变 model-key 集合；匹配者返回保守拒绝，
其余走原 phase。这个策略依赖当前输入，未使用 phase-call 历史 cache。Observer
也能剥开已知旧 guard 的 fallback，区分外层 q 与旧顶层 guard，避免嵌套重复计数。

这是不受信任的机会选择策略。不同位置若有相同 source model，也可能被跳过；
它不证明最优 partition、保留全部优化机会或任意 version syntax 识别。

## 同一个新 build 的验收

完整62原案例及两份已披露 initializer adaptations 全部尝试，默认资源／见证
策略、tile=32，没有原例单独覆盖设置：

| 项目 | 当前结果 |
| --- | --- |
| Raw native outputs | 60匹配 GCC；`corcol3`、`pca`仍是原 frontend refusal |
| 两份 initializer adaptations | 两份均匹配 GCC，独立记录 |
| Compiler timeout / native mismatch | 0 / 0 |
| 安装范围 | 14/62原案例、30sites；source coverage未增加 |
| 新 quotient 路线 | 11原案例、27sites |
| 保留 initialized 路线 | `dct`、`matmul-init`、`mxv`各1site |
| 旧 reduction 路线 | 该默认完整重跑中0site；legacy模式另行回归通过 |
| 新 polynomial contexts | 23/23，包括31/32/33、零／负输入、public exits、selection和错误提议 |
| Reduction、initialized、public/legacy | 14/14、20/20、7/7 |
| 未改 assembly 的实际路径 | 6/6；q值为2/0/1/1/2，负输入走fallback且不执行q capture |
| Canonical unit masks | rank3七种＋rank2三种均通过，各安装2个q版本，divisor=1 |

新 quotient cases 为 `fusion6`、`fusion7`、`gemver`、`matmul-seq`、`matmul-seq3`、
`multi-loop-param`、`mvt`、`mxv-seq`、`mxv-seq3`、`polynomial`、`tce`。
安装数不是 nonidentity 效果或收益证明；完整配置覆盖仍另行验收。

Unit 首轮 helper 使用了错误的 tag 字段名，十项 runtime/installation 子报告
均通过，但 observer 报告拒绝。后继只重新核对冻结的成功子报告和实际 tag，
没有重跑 compiler 或 runtime。失败 observer、原输入及修正报告都保留。
Native preflight 对 trace globals 的错误 closed 要求，以及初次 extraction
mapping 产生的 OCaml cycle，也保留 named rejection 和输入快照。最终 trace
wrapper 以 reflexivity 证明与原计算相同，继承既有 globals，没有新增假设。

十二模块合计1,093行、21 queried endpoints，其中3 closed，最大42个既有
compiler globals；本阶段在前九模块之上增加209行和6端点。审计绑定515份
reachable sources、9,025文件。Trace接口继承其定义引用的既有模型 globals，
不把它们错误报告为 closed。

## 成本与尚未完成的工作

所有上述 goal commands 结束后，使用同 compiler、同 flags 的未标记原程序
比较完整调用。每版本一次 warmup、七次交替 wall samples，所有输出匹配。
原 polynomial 的 optimized/unmarked median 为0.017454527/0.013419777秒，
比值1.300657，**成本验收仍失败**。测量包含 startup、初始化、region和digest；
未控制 CPU affinity/外部 host load，也未隔离 guard cost。前一1.271472比值
属于另一 build/run，不能作为 controlled ablation。

本阶段支持仍限于共同 n、既有 double assignment/reduction 和静态 global
tensors。它没有扩大动态 pointer alias、loaded child headers或任意 assumption
inference。45个已编译原案例没有 tiling phase；`tricky3`调用phase但无安装。
后续按实际 source/configuration blockers 扩展，并在每次扩展同时交付实际
source/candidate、guard/fallback、context 与 Csem→Asm。当前生成代码仍有多项
membership/prefix tests；紧凑检查与有用完整成本继续需要具体实现和测量。
ISS、其余 sequential configurations、原BT、LLVM/SPEC和larger tiers仍必需。
完整 goal 保持 active。

冻结报告可复核：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_partitioned_quotient_compiler.py --validate
python3 scripts/summarize_quotient_double_tiled_native.py --validate
```
