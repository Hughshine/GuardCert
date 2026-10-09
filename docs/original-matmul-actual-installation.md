# 原 matmul：实际程序证据与多次安装

2026-10-09，前一检查点的双标记 profile 拒绝已修复。两个相同 marked regions
现在都安装真实 Pluto i/k/j 候选，完整 modeled-state digest 匹配 GCC；旁边相同
unmarked region 保留。新增无关 global 的程序也接受。原十项回归与新增十项
上下文／动态测试全部符合预期，均匹配同一输入程序的 GCC 输出。

[完整程序定理](../prototype/interface/OriginalMatmulActualProgramCompiler.v)
`compile_actual_original_matmul_program_correct` 仍是成功编译时的 Csem→Asm
backward simulation。Kernel、源语法、候选 pipeline、runtime condition 和 scoped
selected host 都复用；本次改变语言实例如何取得实际程序证据及 public frame。

## 用户接口与证明责任

C 使用者仍给出 `#pragma scop` / `#pragma endscop` 和阶段选择，不填写 semantic
callbacks。编译器在 actual program 上检查：

- 八个相关 global 的实际声明及类型；
- language host 所需的 no-shadow 性质；
- actual public temps 与 private capture/scratch pool 的分离。

它不再比较整个参考 symbol map，也不要求 actual public temps 属于参考程序
集合。Source template 识别、实际 scheduling/validation/codegen、safe capture、
原始 fallback 和公开出口恢复继续适用。相同源族的两个 sites 复用一次 checked
proposal，分别在各自进入时执行 capture/guard；第二个 site 不复用第一次的运行时
参数值。发生静态拒绝仍编译原程序。

[Public capture](../prototype/interface/OriginalMatmulPublicCapture.v)以 actual live
集参数化 capture frame、原 source transport 和模型／候选对应。它只新增与 private
captures 的分离要求，由语言 producer 的 pool check 生产。
[Public lowering](../prototype/interface/OriginalMatmulPublicLowering.v)用同一 live
集实例化原 nested backend，保持 public temps 和 cached parameters，再复用公开
I64 出口恢复。[Actual bindings](../prototype/interface/OriginalMatmulActualProgramBindings.v)
从 input program declarations 建立所需 global lookup，不要求它们与旧程序的
block 编号相同。内存 read permissions 仍由实际 source execution 提供；声明检查
不会推断任何 load 安全性。

局部契约 `original_matmul_actual_scoped_contract reference live` 消费这些声明／资源
证据、checked pipeline 和实际 lowering 的成功结果，提供 raw source 到 guarded
statement 的 projected contract。Language host 提供 actual runtime environment 的
preservation、local no-shadow、caller scope 与上下文安装证明。优化器的 source/model
及 transformation obligations 不变，framework kernel 不加入 Clight 细节。

新增四模块447行、13个审计端点／1 closed、最大42 inherited globals，无新增公理；
406 reachable sources／7,843 bound files。保留四次成功和五次拒绝的证明尝试。
[机器摘要](original-matmul-actual-installation.json)共绑定16,753个文件，包含旧双标记
失败及诊断、完整新 native build、执行矩阵和真实路径观测。

## 执行验收与成本边界

新增十项覆盖：两个 marked、marked＋identical unmarked、无关 global、global
array type refusal、private-resource refusal、dynamic unmarked，以及四个 dynamic
接受／回退输入。七次实际 pipeline 调用、八处 guarded region 安装，全部预期通过。
类型或 private separation 不成立的输入不调用 pipeline。两 marked 的源码、运算树和
候选 witness 沿用前一失败测试。

动态输入仍使用已披露的 const-header／双 rotate 适配。新编译器未改汇编上的四项
断点观测确认正常与 M=0 进入候选，负 M／负 N 进入原始 fallback，且输出匹配 GCC。
对应 dynamic unmarked baseline 已补上：七次完整调用 wall samples 的 median 为
0.006706秒，dynamic accepted 为0.005405秒；各自编译耗时0.057976／1.010179秒。
原 affine median为0.005191秒，unmarked为0.006800秒。上述包含初始化、guard／fallback、
计算和 digest，是小输入诊断；没有隔离 guard 成本或建立 profitability 结论。

## 剩余范围与下一步

这个编译器仍识别一份 raw matmul source template，相关 global identifiers、100×100
布局和 private pool 仍固定。真实私有资源冲突已测试安全拒绝。它解决的是上下文衔接，
不是整个原 benchmark frontend；corpus 的 nonidentity optimized case 仍为1/62。

下一阶段扩展 typed source/data factory 的实际布局、control 和 instruction 表示，
从 input syntax 生产 source/model、private resources 与 guard obligations，接续其余
原案例；同时保留真实 tiling／ISS／其他 sequential phase 和原 BT 的实现要求。
Larger tiers、对应条件算法／完整成本与 CGO 2017 对齐继续验收，不能用本次多 site
或 proof 数量代替。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_actual_matmul_compiler_evidence.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/summarize_actual_matmul_installation.py --validate
```
