# 原 matmul：实际安装、运行时选择与 Csem→Asm

后继已修复双标记拒绝，并扩到实际程序的 global receipts／public frames，见[当前结果](original-matmul-actual-installation.md)。以下保留原检查点。

2026-10-09，原始 matmul C 输入已通过真实 Pluto scheduling、typed validation、
prepared codegen、guarded Clight installation 和 CompCert backend。实际候选将
`i/j/k` 改为 `i/k/j`，保留原 double 运算树、100×100 nested arrays 和 I64
source controls。十项原 C 验收全部满足安装／拒绝预期，完整 modeled-state
digest 都匹配原 GCC；五项安装 guarded region，另五项静态拒绝或不选择。
这使 pinned 62-case corpus 中一个原始案例获得实际 nonidentity 优化。

[完整编译器定理](../prototype/interface/OriginalMatmulRawProgramCompiler.v)
`compile_raw_original_matmul_program_correct` 将成功编译的 Csem 程序与生成汇编
联系为 backward simulation。它量化输入程序、选中 labels、外部 schedule proposer
和 coordinate witness；profile、validator 或 lowering 拒绝时继续编译原程序。
具体 source template／public profile 仍有限制，定理不意味着所有片段都能优化。

## 证明责任与复用

[语言服务](../adapters/compcert-memory/GuardMemoryLongRawLoadedProgress.v)为实际
frontend 保留的 `skip` prefixes 增加控制 cursor／rank，覆盖 init、header、increment
和 body 的真实步骤。它复用 framed body／sequence 服务；成功 signed-I64 比较
保证下一次 increment 不 wrap，body frame 保留父循环 counter。进度证明不要求
header 稳定或 guard 的接受范围，也不推断 source loads 安全或执行总是成功。

[Raw source instance](../prototype/interface/OriginalMatmulRawProgress.v)组合三层
循环。[局部契约](../prototype/interface/OriginalMatmulRawProgramBindings.v)通过
已证 finite execution 和 temporary-footprint 运输，复用原 source/model、安全 capture、
候选执行及公开出口证明。[选中区域实例](../prototype/interface/OriginalMatmulRawSelectedInstallation.v)
把这个契约接回原 scoped host。Fallback 保留实际 raw source。

Kernel 不改。语言实例负责实际 AST、检查安全性、private/public frame、source
progress、上下文安装与 backend composition；优化器负责真实 source/model
correspondence、前提和 schedule/candidate validation。C 使用者提供标记与阶段选择，
无需填写 semantic callbacks。新增五模块628行、16个审计端点，最多42个继承 globals、
无新增公理；这些端点均使用已有语义 globals，没有 closed endpoint。审计绑定403个
reachable sources、7,792个文件，保留五次成功和一次拒绝的证明尝试。

## 实际执行与尚未支持的上下文

原十项包含 affine、identity、unmarked、scheduler refusal、reverse dependences、
malformed schedule、wrong witness、负 M、M=0、负 N。九次 pipeline 调用中，实际
安装数共五；identity 只是回归，不能另算 nonidentity benchmark 支持。标记以外的
相同片段也测试过：一个 marked＋一个 identical unmarked 的完整程序只安装一次，
digest 匹配 GCC。

原程序的 M/N/K 是 `const`，backend 折叠其 guard。为了测量真实动态选择，独立
fixture 明确去掉这三个 header 的 const，并在 guard 前通过已有 rotate 函数各旋转
16位两次；对本次 signed32 输入保持数值。这是周边输入适配，原循环、double 数组
和运算树保持相同。四项均安装候选且完整输出匹配同一适配程序的 GCC。
用 debugger 在未修改的汇编中观察分支入口：

| 动态输入 | candidate entry | original fallback entry |
| --- | ---: | ---: |
| 正常 M/N/K=96 | 1 | 0 |
| M=-1 | 0 | 1 |
| N=-1 | 0 | 1 |
| M=0 | 1（空候选） | 0 |

保留 sandbox 阻止 ptrace 的第一次尝试；允许本地测试调试后第二次四项都通过。
这些断点观测不属于新的语义公理，不修改 source／compiler／assembly，也不提供成本。

两个 marked identical regions 的尝试尚失败。诊断确认两个 actual raw source 都精确
匹配，但第二个 label 使全程序 environment／public-scope profile 拒绝，新增公开 temp
173；`no_shadow` 通过。没有 pipeline 调用，输出仍匹配 GCC。这个限制属于语言实例，
不能用它缩减多次 rewrite 的验收。后继要从实际 declarations／symbol receipts 生产
所需 global facts，并把局部 frame 扩展到实际程序的 public temps；保留同一候选证明。
第一次上下文尝试另含 const-header assignment 的 C 前端拒绝；所有失败保留。

## 成本与后续

原 affine 编译耗时1.319871秒，identity为0.193694秒，unmarked为0.058051秒，
均含 frontend、pipeline、Pluto 与 backend。每项七次 native wall samples 包含初始化
和 digest；affine median为0.005238秒，unmarked为0.006710秒。这是小输入完整调用的
诊断记录：原 const guard 被折叠，没有单独 guard 成本，尚不作 profitability 结论。
后续需相同动态输入的 disabled baseline、输入 tiers、guard／fallback／exit 完整成本，
并继续其他原案例、BT 和规定的 sequential transformation routes。

[机器摘要](original-matmul-raw-installation.json)来自独立 evidence audit，共绑定13,468
个文件，包括两个完整提取构建、原十项、两次上下文尝试、路径尝试与 read-only profile
诊断。Frozen checkpoints 保留；完整 PolCert／CGO 2017 目标继续 active。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_raw_matmul_compiler_evidence.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/summarize_raw_matmul_installation.py --validate
```
