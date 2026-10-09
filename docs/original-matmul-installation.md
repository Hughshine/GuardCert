# 原 matmul：program compiler 与 raw frontend 衔接

2026-10-09 已证明 profiled selected compiler 的 `Csem → Asm` 正确性，并
提取可运行编译器。原 C 的首轮验收暴露了明确的 matcher 差距：实际 frontend
保留 `Ssequence Sskip s`，此前 Rocq exporter 省略这些节点。当前十个完整
程序都匹配 GCC digest，九次调用真实 pipeline，但实际安装数仍为零。
这里记录已证接口、原输入上的拒绝及下一项必须闭合的义务。

本次 fetch 核对 `topdown/research-positioning@8ce9c8b`；main 的
[narrative](topdown/paper-narrative.md) 与 [context lifting](topdown/context-lifting.md)
正文一致。最小 kernel 停在 local guarded correctness，全程序安装属于语言
host。优化器交付 source/model/candidate 桥和前提；C 用户提供标注与程序，
不用提供语义 callbacks。

## 已证编译器接口

[OriginalMatmulProgramCompiler](../prototype/interface/OriginalMatmulProgramCompiler.v)
提供三个层次的入口：

| 入口 | 输入与用途 | 保证 |
| --- | --- | --- |
| `apply_profiled_original_matmul` | chosen labels、已降低 candidate、当前 Clight program | 在已检查环境与实际 pipeline/lowering receipts 下的 whole-Clight forward simulation |
| `checked_original_matmul_program` | chosen labels、不受信任 scheduler、coordinate swaps、当前 program | 每个 `mayReturn` 结果均满足 whole-Clight simulation；无标注或检查拒绝保留原程序 |
| `compile_original_matmul_program` | 同一配置与 Csyntax program | 成功输出 Asm 时具有 `Csem → Asm` backward simulation |

最后一个入口实际经过 SimplExpr、SimplLocals、上述 checked rewrite 和
CompCert backend。Scheduler 与 coordinate witness 是数据生产者；extracted
checker 检查调度、最终 generated Loop 的域／坐标对应与依赖。它们不提交
未经验证的语义证明。

编译期 profile 检查 symbols、composite declarations、当前 program 的 public
temporary scope 及指定 globals 的 no-shadow。它不比较整个函数体或 global
initial values。因此负／零 header 的初始化变化仍可通过 profile。当前 profile
仍固定到已证的 identifiers、100×100 arrays、padding 2 及旧 public scope；
这是待扩展的 frontend 范围，不能作为缩减总验收目标的理由。

[ScopedSelectedRegionProof](../prototype/interface/ClightScopedSelectedRegionProof.v)
复用既有 occurrence-sensitive AST traversal，只在 chosen labels 内寻找支持的
片段。Scoped contract 只消费实际 program 的环境 invariant；语言证明运输
locals、symbols、continuations 和公开状态。原 pool 检查证明四个 capture 与
六个 scratch IDs fresh。Generic kernel 没有修改。

## I64 control protocol 的实际保证

[LongProgressControl](../adapters/compcert-memory/GuardMemoryLongProgressControl.v)
证明：对 signed I64 counter，如果 `< bound` 成功为真，则 counter 严格小于
`max_signed`，本次 increment 不 wrap。Bound 可以是任意返回 signed I64 的
Clight expression，允许重复 load。

[LongLoadedProgress](../adapters/compcert-memory/GuardMemoryLongLoadedProgress.v)
将该事实和 body 的 framed progress 组合成可嵌套的 source protocol。Body
保持 counter；rank 使用剩余 signed counter 距离与 body rank。因此这个
control protocol 不要求 header 稳定，也不要求 guard 已接受 0..98 范围。
它不产生读取许可或 source definedness。Header stability、访问安全与数学
域仍由原 source execution、safe capture 和 domain proof 交付。

[OriginalMatmulSourceProgress](../prototype/interface/OriginalMatmulSourceProgress.v)
实例化了此前 exported 三层 region。这个 protocol 排除该语法上的无限内部
步骤；不能把它写成任意原 C frontend AST 的 totality 定理。

## 原 C 的首轮结果及原因

提取入口保留原 double 运算树、global nested arrays 和 I64 counters。十个
配置包括真实 Pluto i/k/j、identity、unmarked、external refusal、reverse、
malformed、wrong coordinate witness，以及负 M、零 M、负 N 初始化变化。
全部编译、链接并运行，与相应原 C 的 GCC digest 匹配。七次重复 native
计时也核对相同输出。

五个预期拒绝／unmarked 配置符合预期；五个预期安装配置失败。它们的
guarded statement count 为零。九次 pipeline 调用与所有 artifacts 已保存；
不能把调度器调用或 target function 上附加的 private declarations 计为
优化安装，更不能把这些运行称为 runtime guard 分支验收。

Read-only diagnostics 定位到 `root.0`：canonical region 的第一项是 `Sset`，
实际 frontend 则是 `Ssequence Sskip (Sset ...)`。
[CompCert exporter](../vendor/CompCert/export/ExportClight.ml) 的 `stmt` 明确
省略左右 `Sskip` sequence。即使 `Info.normalized=false`，打印的 AST 也已
省略它们。因此此前的 exported-AST equality 只说明打印后的 AST 精确匹配。
当前正确编译定理仍覆盖实际 pass 的拒绝行为；它不证明原 C 的 loop 已被
改写。

另一个诊断 exporter 保留每个 skip/sequence，并输出真正入参的 selected
statement。[OriginalMatmulRawSource](../prototype/interface/OriginalMatmulRawSource.v)
用一个 closed Rocq endpoint 核对其三层形状：每层 initialization、condition
和 increment，以及 assignment body，都带前置 skip。这里已核对语法形状，
尚无 raw↔canonical execution transport 或 raw progress 证明。

下一实现须消费这个真实 source：提供 skip-prefix 的双向执行运输，扩展
现有 I64 protocol 以覆盖这些 administrative steps，交付保留 raw fallback
的 local contract，再接到同一个 scoped selected host 和 backend。最终应
在相同原 C 上看到实际 guarded region、i/k/j candidate、runtime accept/refuse
与完整程序 digest，而不是只改变 matcher 或运行 unverified normalizer。

## 责任与总验收

| 提供者 | 本次工作 | 下一项最具体的责任 |
| --- | --- | --- |
| Generic kernel | 沿用 local certificates 和 composition | 保持语言无关；不承担 skip syntax 或 CompCert continuations |
| Language/IR instance | I64 control rank、scoped selected host、program environment/scope check、backend composition | Raw skip-prefix execution/progress、合法 site 和 private/public transport |
| Domain/optimizer factory | 沿用原 source/model、safe capture、同参数最终候选与 lowering receipts | 在真实 raw source 上生产适用 contract，并扩充 source/layout/route 支持 |
| C 用户 | 原程序与 paired SCoP markers | 无新增局部语义证明责任 |

最困难的接线在 actual source 到模型以及 host boundary。Pipeline legality
与 `G accepts → P` 不能替代它们。原 finite normal execution 是证明起点，
不是 runtime 先运行 source 的检查。

62 个 PolCert 原案例、原 BT／serial NPB、各 sequential affine/tiling/domain
路线以及完整调用成本仍属于总目标。当前 requested optimized cases 仍为零。

## 可复现证据

[机器摘要](original-matmul-installation.json)绑定两个后继审计。八模块1,320行、
26端点／4 closed，395 reachable sources／7,742 proof bindings，最大42个
继承 globals，无新增公理；8成功／12拒绝证明尝试保留。Raw shape 模块
127行、一个 closed endpoint 单列。Compiler evidence 绑定20,114文件，包含
三次成功和两次失败 native builds、十个完整 C/Asm 运行与两次真实 AST 诊断。

Compiler wall time包含 frontend、pipeline、Pluto 与 backend；每个配置一次。
Native wall time包含 initialization、kernel 和 digest，每个配置七次。
数值见机器摘要。由于尚未安装 candidate，这些不是 guard 成本或优化收益。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_original_matmul_installation.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_original_matmul_compiler_evidence.py --validate
python3 scripts/summarize_original_matmul_installation.py --validate
```

重跑 native 验收应使用新的 attempt 目录。冻结的失败报告保留其预期安装失败
及全部真实输出；不覆写成成功结果。
