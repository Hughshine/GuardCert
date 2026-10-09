# 已验证包络之后的动态 tile bounds

主线新增一个已证明的 Loop 裁剪服务：最终多面体 checker 先验证仿射包络与
membership guard；服务再从 guard 恢复运行时上界，去掉不执行 body 的后缀。
实际 Clight lowering 消费裁剪后的 Loop，完整 compiler 接到新的 Csem→Asm
端点。核验数字和报告路径见[固定摘要](runtime-double-tile-bounds.json)。

## 为什么需要这一层

原独立参数 adapter 把 codegen 的除法上界改成常数 cap 包络，例如：

```text
loop t = 0 .. 4
  guard 0 <= t && 32*(t+1) <= N+31
    body
```

实际 `N=23` 时只有第一个 tile 活动，但旧候选仍检查整个包络。机器 lowering
已有正除数、非负分子的除法服务；阻碍直接保留除法的是最终 extractor 的
仿射语法检查，它拒绝 `Div` 边界。不能仅修改 native adapter 后声称接线完成。

新服务保留 checker 所消费的上述 reference，证明并实际降低：

```text
loop t = 0 .. floor((N+31)/32)
  guard 0 <= t && 32*(t+1) <= N+31
    body
```

guard 本身继续保留。这次没有实现 guard factor 消除，也没有把 point loop
的一般 `min/max` 上界接入机器 lowering。新的实际 Loop 不重新交给不支持
`Div` 的 extractor；它的执行保证来自已验证 reference 和裁剪定理。

## 使用接口与证明边界

[PolCertGuardedLoopTightening.v](../theories/PolCertGuardedLoopTightening.v)的
`PolCertGuardedLoopTighteningFor I M` 参数化 instruction 与 Loop model。
`tighten bounds statement` 返回具体 Loop，不需要使用者提供逐 loop 回调。
`tighten_execution` 的保证是：环境落在给定区间内时，reference 的任意有限
执行都能在返回的 Loop 中执行，保持同一最终 memory。

它识别合取中的 `factor*(iterator+1) <= numerator`，要求 factor 为正，且
numerator 能消去当前 iterator binder。由已有 floor 编码定律，接受该比较
意味着 iterator 小于恢复的上界；越过上界后的 guard 因而为假。list 执行
定理去掉这些 memory 不变的迭代，再把保证递归传递到 nested loops 与 sequences。

选择新上界还要通过 I32 interval analyzer：分子、系数和所有中间计算必须
满足它的表示与安全限制，新上界的最大值不超过原上界的最小值。不支持的
形状、负分子、overflow、当前 iterator 依赖或不满足包络关系时保持 reference。
这是充分的静态选择规则，不是最弱前提、任意条件推导或最优 bounds。

该服务在最小 kernel 之上，使用具体 I32 range 服务。它没有提供一般语言的
整数语义，也没有从有限执行保持推导 divergence 或 contextual equivalence。
Loop model 不观察候选 scratch counters；语言实例另证其私有性和公开出口恢复。

| 责任方 | 此次实际消费的证据 |
| --- | --- |
| Framework | 最小 kernel 边界保持；此次实际 Clight 局部证明直接构造 branches，没有新增 `guardify` 调用或 kernel 定律。 |
| Domain／优化实现者 | 原 source/model 和最终仿射／依赖 checker 仍验证 reference；新服务证明 membership 许可裁剪及有限 Loop 执行保持，不要求额外 alias 假设。 |
| Language／lowering | 原 capture 提供 typed 参数和区间；[candidate theorem](../adapters/compcert-memory/GuardMemoryDoubleTightenedCandidate.v)转换两份 interval 接口，消费 `tighten_execution`，再由原 nested backend 证明实际除法、public frame 和 Clight 执行。 |
| Language host／site | 新 factory 消费 checked source、资源、entry/refusal transport、公开 I64 exits 和独立 source progress；原 selected host 与 backend 用于当前 intermediate program 的全程序安装。 |

C 源码使用者仍只提供标注与配置。安全读取许可来自原 source 的实际执行和
已有静态／运输证明；这不是运行时先执行 source，也不是允许 speculative reads。
Runtime capture 写 private caches／flag，保持 memory 和 public state，不是完整
state readonly。此次没有增加 runtime alias test 或新的 entry-condition 类别。

完整端点位于
[TightenedRectangularHeaderLiteralQuotientCompiler.v](../prototype/interface/TightenedRectangularHeaderLiteralQuotientCompiler.v)，
名称为 `compile_selected_tightened_rectangular_header_literal_quotient_tiled_stable_program_correct`。
它量化任意 phase／adapter／caps／resolver 数据，证明成功编译的原 Csyntax
program 到 Asm 的 backward simulation，沿用 CompCert 的 parsing／assembly／linking
边界。新增 compiler proof 消费新服务，复用旧 host 和 backend；没有直接复用
旧完整 compiler theorem 来授权这份不同的 lowering。

## 本 build 的验证

七个新 Rocq 模块共 770 行；24 queried endpoints 中 15 closed，最大继承
42 个原 CompCert globals，没有新增全局假设。独立审计绑定 550 个 reachable
sources，native build 绑定 9,681 项；八份报告与失败观察记录的摘要绑定 17,660 项。
开发中的失败 proof attempts 和首轮观察器 inputs 保持，不覆盖成功源码或旧报告。

39 个二维／phase contexts 与 23 个三维 matmul contexts 全部通过，包含独立
M/N/K、31/32/33 边界、非正 count、逐轴 cap 拒绝、错误候选、unit/mixed tiles、
公开 iterator exits、unmarked 与多次安装。实际 Clight 中确认两轴和三轴的
参数相关除法上界。十次 unchanged-assembly 探针确认接受 captures 和 fallback。

五项实际 tile-comparison 观察通过。相同 `N=23,M=31` 源码，父 cap 版本两层
各比较 4 次，当前版本各比较 2 次；其他边界的比较次数为 `(2,3)`、`(2,2)`、
`(3,4)`。首轮只识别 loop 顶部比较，未识别父版本已由 backend 移到 backedge
的比较，保留失败后修正；不把模型迭代数当作机器比较数。这些不是 CPU timing
或隔离的 guard cost。

完整默认 62 原例与两份 initializer adaptations 重放：60 raw 与两 adapted
输出匹配，`corcol3`／`pca` 保持原 frontend 拒绝，零 timeout／mismatch。
仍为 22 原例、39 sites；七处 rectangular sites 都实际提出并安装动态 bounds，
另外 32 处沿用旧族。本轮没有增加 source 覆盖，单一默认配置也不证明全部
sequential phases／configurations 的覆盖。

## 同次完整调用成本

使用原 matmul 数值类型、数组与 IEEE expression tree，在披露的 repeat context
内执行 200 次原区域；一份初始化、区域执行、摘要和进程 startup 都计入。
固定同一 CPU，两次 warmup、七组轮换，每次输出与同一 repeated GCC reference
匹配。外部 host load 未控制，guard 未隔离。父 cap 版使用前一 compiler，另外
三个版本使用本次 compiler；四者使用同一 pinned CompCert backend 和编译选项。

| 版本 | Wall median（秒） | 相对本次 unmarked |
| --- | ---: | ---: |
| 本次 unmarked | 0.479005 | 1.000000 |
| 父 cap tiled | 0.234956 | 0.490508 |
| 本次动态 tiled | 0.234680 | 0.489932 |
| 本次 untiled | 0.208777 | 0.435856 |

动态 tiled／父 cap 的 wall 比值 `0.998827`，child CPU 比值 `0.997962`。
这次计时没有建立动态 bounds 相对 cap 版的明确额外收益；两种 tiled 和
untiled 在此披露上下文相对 unmarked 有用，不据此主张普遍 profitability。
旧 build 的 timings 不改写为本次结果。

完整目标继续 active。下一功能工作转向实际多 statement／不同深度 region，
以及非零／inclusive／affine source headers；每项都立即连接 source/model、
safe condition、实际 candidate、公开 continuation 与完整 compiler。一般
min/max point bounds、guard residualization 和 OLO compact entry-condition
derivation 仍须各自接线并验收接受域和成本。原 BT、LLVM/SPEC、larger tiers、
其余 sequential phases 与同例作者负担比较仍未完成。
