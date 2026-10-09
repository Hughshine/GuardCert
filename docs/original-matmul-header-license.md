# 原 matmul：条件式 header 读取许可与 narrative 责任落实

2026-10-09 重新 fetch 并核对 narrative `8ce9c8b`，`paper-narrative.md`
和 `context-lifting.md` 与 main 一致。本阶段把“原执行是证明起点，读取
许可不同于接受后的范围事实”落实到同一原 matmul。两个新模块 157 行、
六端点通过 Rocq 编译和假设审计，无新增公理。**还没有生成或安装原
matmul capture／guard**，新增优化案例仍为零。

## 已证事实与实际输入

`GuardMemoryLongHeaderLicense` 从 initialized I64 loop 的有限正常执行
取得第一次 header test；test 为真时恢复同一初始 memory 上的第一次
body 执行。成功的 signed I64 比较排除 `Vundef` 和其他 value kinds，
生产实际 `Mem.load Mint64` word receipt。

`GuardMemoryDoubleMatmulHeaderLicense` 沿三层原源实例化该语言定律：

```text
exists m_word,
  load M = Vlong m_word
  and (signed(m_word) > 0 -> exists n_word,
    load N = Vlong n_word
    and (signed(n_word) > 0 -> exists k_word,
      load K = Vlong k_word))
```

所有 loads 都指向原 region 的入口 memory。证明中的 i/j/k 初始化只改变
temps；第一轮 M→N→K 路径尚未执行 body store。这不是运行时预执行源
循环，也不要求修改公开 counters 后才检查。已有 global execution 定律
可以据此在其他 temp 环境中执行同一 global read。

`OriginalMatmulHeaderLicense.original_matmul_conditional_header_license`
通过实际 selected-body equality 和已有完整 nest equality 绑定原 AST。
它只要求 M/N/K global bindings 和原片段的有限正常执行；没有 header-load、
非负范围、layout、数组许可、header stability 或候选执行前提。Signed
words 可为负：M 非正时不要求 N/K 可读；M 正、N 非正时不要求 K 可读。

这是 source-definedness 的一个局部证明服务。Static bindings 仍需实际
matcher／scope／global-environment 接入来生产；有限正常执行不代替任意
源的 progress 或 divergence 定理。Receipt 只许可读取，不保证维数适合
模型，也不自动成为可执行检查。

## 三方责任与下一 producer

| 层 | 本阶段交付 | 下一项责任 |
| --- | --- | --- |
| Framework kernel | 复用局部 guarded correctness，未改接口 | 消费最终 guard／conditional certificates，不解释 M/N/K、C syntax 或调度。 |
| Language | 首次 header／body 恢复；实际 signed 比较取得初始 memory 的 load receipt | 安全 capture／range tests、typed fresh temps、公开 frame、拒绝入口运输，以及 host 所需 progress／安装。 |
| Domain／optimizer | 原三层 nest 的 M/N/K 许可组合，绑定实际 selected AST | 接受 words 生产范围、模型参数、稳定性；连接真实候选、public exits 和 host 所需 region guarantee。 |

下一 capture 先检查 M 的范围；M 为正且已通过时才读 N，M/N 均为正且
已通过时才读 K。空外层／中层填充未读取的私有模型参数，保留公开 j/k
出口规则。当前 bridge 用 `0..98`，这是该源／降低路径的临时接受范围，
不缩减总体目标；负数或超范围回退。若采用 I32 私有模型坐标，还须证明
I64 检查后转换的数学值精确性，保留源 I64 controls。

验收分别给出安全调用许可、接受推出数学事实、实际 E0／memory／公开
temps frame，以及真实 checked state 到 candidate／fallback 的入口关系。
Private captures 可写，不满足全部入口 state 相等；没有 freshness／scope
和 transport 证明就不能安装。Read-only frontend 不代替 private-state 接口。

## 必须保留本次 captured 参数

[真实 prepared pipeline](original-matmul-prepared-pipeline.md) 已运行 Pluto、
typed validator 和 codegen，但 wrapped backward theorem 存在量化参数
环境，当前 `InitEnv` 只检查长度。Source 和 candidate 各有三个参数，
不能推出它们使用本次读到的同一组 M/N/K。

最终 checker／factory 必须绑定 named context `[K;N;M]` 与实际执行环境
`[M;N;K]`，在**同一 captured 参数**下取得适用方向的 source／model／
candidate 执行对应、真实 Clight lowering 和所需 progress。不能任取
wrapped theorem 中另一组存在参数替代本次捕获；还要运输 registry／
memory、恢复公开 counters 并交付 selected Csem→Asm。Header license
没有关闭这项义务。

## 冻结检查点与复现

机器摘要见 [original-matmul-header-license.json](original-matmul-header-license.json)。
六端点均继承原 CompCert 假设，单端点最多六项，无新增公理。审计跟随
218 reachable sources，绑定 7,263 文件；三次成功、六次失败的 proof
attempts 保留。其中一次中止了展开机器整数常量的耗时尝试，后继显式
控制归约后编译通过；旧源和日志保留。

- Proof：`build/original-matmul/header-license-proof-v1/report.json`，SHA-256
  `73d34b416d37f70cce0075332536f65819417bfbcadfebb63699c59ff9d69cc2`。
- Actual source：`build/original-matmul/source-header-license-v1/report.json`，SHA-256
  `4fa5dabdaec101d47532bf9740bba6ce5156a2a88238eb2b7fd8b277b749cfe7`。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/compile_matmul_header_license.py GuardMemoryLongHeaderLicense --attempt NAME
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/compile_matmul_header_license.py GuardMemoryDoubleMatmulHeaderLicense --attempt NAME
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/prove_original_matmul_header_license.py --attempt NAME
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_original_matmul_header_license.py --validate
python3 scripts/summarize_original_matmul_header_license.py --validate
```

首次 audit 不带 `--validate`；成功源／对象和报告冻结，后继用新模块／
检查点。没有 native guard、C／Asm 优化调用、成本或新增 whole-program
endpoint。PolCert／CGO17 原案例、顺序功能／效果及完整程序正确性的
总目标继续执行。
