# PolCert／CGO 2017 对齐：验收范围与下一步

2026-10-08，吸收 narrative
`8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9`。本文面向参与实现和评审的人，
固定原始程序、配置与完整证明的验收口径；不把案例登记算作功能通过。

2026-10-09 [默认资源策略完整后继](adaptive-double-tiling.md)在单一build上重跑
62原例＋两适配，无手动budget覆盖：59raw＋2adapted匹配，两个raw frontend拒绝，
polynomial600.016秒compiler timeout；13/62安装29处。Tce自动22temps／十轴安装
四处，原dct、mxv、matmul-init各一处。45个已编译raw无tiling phase，tricky3调用
但无raw candidate。独立120秒trace／compact attempts将polynomial定位到AST
generation，尚未修复；后者不是完整重跑。七项public／legacy通过，没有controlled
cost或收益结论。下面保留前序build的范围，不能混成最新完整结果。

2026-10-09 [新完整 reindexed 对照与 initialized 后继](initialized-double-tiling.md)
保留原62＋两适配：前一build为59raw＋2adapted native matches，两个raw
frontend refusals、polynomial600.102秒compiler timeout，9/62安装22处。
Tce生成四个实际最终候选而未安装；十轴见证定向后继已安装四处并匹配，但默认
策略和最新build完整重跑仍待完成。Initialized mxv／matmul-init新增真实分块
配置，各安装一处并接Csem→Asm；空表资源后继修复legacy affine回归。
这些分别有build/configuration边界，不能合并为最新完整corpus或成本结果。

2026-10-09 [当前 compiler 的完整对照和实际修复](double-witness-policy.md)已完成：
先跑全部62原案例的三模式，再依据缺见证拒绝扩大 checked witness search。
新策略实际安装 `matmul-seq`／`matmul-seq3`／`tce`；完整 affine 复核无 native
mismatch。当前14/62原案例安装30处，8/62有非恒等证据；44项 scheduler 前回退、
dct／polynomial phase 后拒绝及两项 raw frontend refusal 仍是缺口。当前支持的
configured guards 和 Csem→Asm 端点已连接，完整 sequential phases／cost 未完成。

[Actual double tiling 后继](double-tiling-installation.md)跑完同一完整语料，保留
原IEEE／I64／布局：9/62原案例安装22处，59raw与2adaptations匹配，两个raw
frontend拒绝和`tce`180秒编译超时。后继`tce`长预算安装4处并匹配，跨两build
实测并集10/62、26处；不是最新build完整重跑。Unit／context／原出口和实际
branch验收也通过。本路线为identity pretransform＋tiling，affine后tiling与
其余sequential配置仍待连接，不报告收益或controlled cost。

## 已核对的输入清单

[机器可读清单](benchmark-alignment-inventory.json)绑定两个上游提交、下载内容
的 SHA-256 和原始文件的 Git blob。以下是清单事实，不是 GuardCert 运行结果。

| 来源 | 固定版本与输入 | 当前核对结果 |
| --- | --- | --- |
| [PolCert corpus](https://github.com/Hughshine/PolCert/blob/ca1ae3199c816594bab9d51eb77309a0d17527aa/tests/polopt-generated/README.md) | `ca1ae3199c816594bab9d51eb77309a0d17527aa`；62 个 `.loop` 输入 | 原始 tree、strict manifest、saved best 配置与运行报告的案例集合一致 |
| [PolCert generated C](https://github.com/Hughshine/PolCert/blob/ca1ae3199c816594bab9d51eb77309a0d17527aa/tests/end-to-end-generated/README.md) | 同提交；由源／目标 Loop 对生成 harness | 这是另一层 materialization；不能把 Loop 输入直接算作已接入的 C 程序 |
| [CGO 2017 author artifact](https://github.com/jdoerfert/CGO17_ArtifactEvaluation/tree/1b23e28261eb1c161192afa86ab996eb67d65f0c) | `1b23e28261eb1c161192afa86ab996eb67d65f0c`；serial NPB 源码 | 找到 BT、CG、DC、EP、FT、IS、LU、MG、SP、UA 十组 C 源；BT 的原文件为 `BT/rhs.c` |
| LLVM Test Suite | Artifact 指定 `1d312ed`／SVN r287194 | 完整 Git revision、实际输入名单与本地取得仍待完成 |
| SPEC2000／SPEC2006 | Artifact 不附专有源码 | 源码取得和 C／C++ frontend 差距保持未解决项，不能删出对照范围 |

62 项中有 19 项的已保存 best route 使用并发；这些案例全部保留，改跑其
顺序配置。Saved report 为每项提供顺序配置记录，同时有七条候选记录没有
execution metadata；清单保留后者，不将其解释为成功运行。Saved best 只是
历史调参记录，不作为当前机器上的最优性或 GuardCert 支持证据。

复现清单：

```sh
python3 scripts/benchmark_alignment_inventory.py --fetch
```

固定来源缓存于 `build/benchmark-alignment/source-pins/`。已有缓存可不带
`--fetch`；该命令只生成 inventory，不运行编译器或测量速度。

## 首轮实际尝试：baseline 通过，所请求优化仍为零

[详细记录](original-benchmark-first-attempt.md)与[机器可读摘要](original-benchmark-first-attempt.json)
绑定首轮原案例运行和新增浮点证明。62 项三配置有 180 次初始 native digest
匹配；另外六次在两个 harness 的显式常量初始化适配后匹配原 GCC 结果。
Active 124 对 Clight 均与 disabled 相同，没有 pipeline 调用。原 serial BT
Class S 的三配置各 17 个单元完成构建并通过原 NPB 自检，十行数值结果匹配，
但 11 个 rhs regions 也没有优化。完整 tiers、适用顺序配置及效果／成本比较
尚未完成，不能把这些原程序编译结果算成所要求的优化支持。

本轮 source/model 缺口具体包括原 harness 的 I64 controls、global array
地址和 F64／scalar 运算，以及 BT 的 inclusive／非零 starts、loaded globals
与公共 scalar exits。新增 generic memory value instruction 与 IEEE double
表达式后继已审计。其后[原 matmul typed bridge](original-matmul-typed-bridge.md)
已双向接 source assignment／memory action／PolCert 单 body Loop，并精确核对
同一原 C 的 exported Clight；八字节地址及 I64 点级对应也已编译审计。
完整 I64 nest、入口前提 producer、实际 typed scheduler、runtime Mfloat64
guard 和 compiler 安装仍缺，优化 case 数保持零。后续走原 matmul 的完整链，再扩 fusion、
multi-stmt-stencil-seq 和 BT；其余 corpus 与配置继续保留。

## 必须分别完成的五项验收

1. **实际源码。** 保留 numeric types、原运算、loaded bounds、驱动及周围
   context。PolCert harness 的生成过程与 CGO 原程序分别登记。标注、尺寸
   缩减、header 适配等修改保留 diff；word-copy fixture 不能代替浮点计算。
2. **实际优化。** 记录源模型、proposal、phase validation、生成的 candidate
   与最终 retained transformation。顺序路线包含适用的 affine scheduling
   后 tiling、ISS、intra-tile scheduling、diamond／two-level tiling、unroll/jam。
   Vector annotation 与实际 SIMD lowering 分别调查。Identity、静态拒绝和
   全部运行时 fallback 是诊断结果，不能算完成所需优化。
3. **安全条件。** 区分 assumption construction／simplification、实际安全
   machine check 和成功后的模型义务。源语义许可的读、短路、capture、
   stability、私有 state transport 与拒绝入口都有具体 producer。扫描可以
   是中间实现；条件代码尺寸、动态工作和完整成本仍需验收。
4. **整程序证明。** 每条支持的配置把实际 checked source、guard、candidate、
   fallback 和公开出口连接到对应 `Csyntax.program` 的 successful-compilation
   Csem→Asm backward simulation，保留现有 parsing／assembly／linking 边界。
   原源码用户只给标注和策略，不补未证 semantic callback。
5. **顺序效果与成本。** 对应计算、输入 tier 和可比顺序 backend，计入检查、
   fallback、capture、出口恢复与完整调用。原八线程 BT speedup 不是顺序目标。
   不要求相同 guard 或 speedup，但有用的顺序效果是尚须达成的目标。

## 责任与逐配置记录

Kernel 保持局部证书组合；language 提供执行、guarded choice、frames、
资源和 region installation；optimizer/domain 提供 source selection、
modeling、充分前提、源／候选对应及可核对的 proposal。Factory/site checks
生产适用的 invocation、scope、placement、progress、typing 与 freshness。
已有 host/backend 可以复用；复用不允许省去新 source/candidate 的对应。

每个 program/configuration 的运行记录必须绑定 source/hash、适配 diff、
numeric types、input tier、compiler/options、proposal、各 phase 的通过／
失败、actual candidate/hash、condition/hash、installed theorem endpoint 和
source `Csyntax.program`、native path／输出以及 complete-call measurement。
尚未生产的记录标为 pending；失败保留所在阶段、具体原因、已尝试修复和
后继行动。不能因某阶段当前有限制就缩小输入名单。

Concrete-to-model decode、model transformation、model-to-Clight、public exits
分别记录实际证明方向；loaded source 另有 capture/stable-source 桥。静态
syntax/resources、dynamic check/capture/transport 和作为证明起点的原 source
execution 不混为同一种前提，也不在 runtime 先执行 source 来许可检查。
Finite completion 与 open/diverging host 按实际 progress 要求选择；退出关系
本身不能证明可能发散的替换。重复安装的证据针对当前中间程序重新产生。

## 当前执行顺序

1. 从上述 62 项 materialize 原 C、numeric types 与 input tiers，跑实际
   selected compiler／顺序配置；以阶段失败表选择下一个实现阻塞项。同步
   固定 CGO serial NPB 的 build inputs、LLVM Test Suite 完整版本与案例名单。
   首批定位 matmul、fusion、multi-stmt-stencil-seq；它们不是最终子集，完整
   清单继续保留。
2. 首批原程序重点包含 BT `compute_rhs`。读取原浮点／scalar computation、
   loaded bounds、布局与周围 context；先取得真实 frontend/model/phase
   拒绝证据，再补对应 source 或 candidate 结构。当前 integer tensor 的
   standalone fixtures 保留为回归，不代替这个工作。
3. 每次 source／phase 扩展同时接入现有 guard、候选、fallback、出口、host
   和 CompCert theorem，随后提取／native。Context lifting 不留到最终集成；
   不重造 kernel、第二 IR 或抽象 context algebra 来延期。
4. 以原案例明确的阻塞项决定 condition service 扩展和成本改进。当前两个
   signed-child 草稿尚未成功编译、审计或安装；其功能不计入覆盖，继续投入
   前先说明它们解除哪个真实 case/configuration 的限制。

目前已完成原corpus的baseline、完整affine和上述单一tiling配置比较；完整
顺序phase矩阵、原BT优化、LLVM／SPEC和较大tiers／成本仍未完成。历史
header／empty／alias验收继续有效，不替代这些原程序功能。完整goal active。
