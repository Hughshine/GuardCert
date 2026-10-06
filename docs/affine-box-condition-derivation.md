# 符号仿射包络：条件推导、编码与实际使用者

本阶段按 [topdown narrative](topdown/paper-narrative.md) 区分推导、编码和安装。算法输入是受限仿射式及盒状迭代域，输出是关于入口计数与参数的仿射上下界。实际 CompCert 使用者用它替换 `j<U(i,parameters)` 的宽度检查，再复用既有候选、局部保持和完整程序安装证明。它没有替换 pointer footprint scan，也不是一般 polyhedral projection 或最弱条件算法。

## 使用者提交什么

[AffineBoxEnvelope](../prototype/interface/AffineBoxEnvelope.v) 不依赖语言语义、CompCert 或 PolCert。domain library 提交

```text
f(x,parameters) = coefficients · (coordinates ++ parameters) + bias
0 <= coordinate[d] < count[d]
```

并提供实际源实例到这些坐标／参数的对应。系数可以为负；维数是任意有限长度。`synthesize_affine_envelope dimensions form` 根据每个坐标系数的符号，选择 0 或 count−1，生成 `lower` 与 `upper` 两个入口仿射式。计数和未消去的参数都是输出的变量，没有运行时枚举坐标。

`synthesized_affine_envelope_covers` 证明每个实际盒内点都满足 `lower <= f <= upper`。`synthesized_affine_envelopes_disjoint` 进一步证明两包络分离时任意两点的仿射值不同；它只证明整数值不同，尚不证明两组机器指针的物理地址不相交。空盒没有点；实际宽度使用者的 header 在 count≤0 时走源分支。

## 三方责任与四张证书

| 层／证书 | 本阶段生产或消费的证据 | 使用者仍须提供 |
| --- | --- | --- |
| 语言无关 framework | 既有 readonly condition、语义前提运输、guarded preservation 和 rewrite 组合 | 语义对象、观察、host 定律及 domain／candidate 证据 |
| 优化／domain：`C_derive` | 包络覆盖全部盒内点；[实际源编码对应](../prototype/interface/ClightParametricEnvelope.v)；接受推出每个行宽约束 | 非盒状域的覆盖、其他真实 source/body 对应，或新的受限推导算法 |
| Clight：`C_guard` | [机器仿射编码](../prototype/interface/ClightAffineEnvelope.v)、有符号参数 interval 检查、实际 Boolean 精确性与安全 | 参数 word view 和已接受范围；合法观察从源或 placement 取得，不能先假设 P |
| 优化／domain：`C_opt` | 复用真实 mapped／tiling／schedule 依赖核对与 `memory_parametric_body_candidate_rule` | 新候选或 body 的局部对应；本算法不发现候选所需的任意假设 |
| Clight：`C_host` | [检查替换服务](../prototype/interface/ClightReadonlyCheckReplacement.v) 保留候选、D、P、局部证明；复用 direct/shared、scope、公开出口和后端安装 | 新语言实例的控制／状态／观察定律；此使用者仍是正常有限 region |

盒状算术库是可复用的 domain service。它不是 kernel 自动理解任意程序语义的能力。相同推导可以由其他语言编码，但该语言仍要证明自己的整数、溢出或 flags 行为和条件执行定律。

机器编码保留 CompCert 的 modular word 算术。`affine_form_code_evaluation` 证明实际值为数学仿射结果的 `Int.repr`；`compiled_affine_interval_comparison_exact` 在最终值落入 signed range 时证明比较对应整数比较。中间乘加可以回绕；这不声称所有中间运算都无 overflow，也不使用硬件 overflow flag。静态 range checker 支持包含负值的入口 interval。

## 一次实际使用

对已有 [C fixture](../examples/native_memory_parametric.c)：

```c
for (; i<n; ++i) {
  k = 2*i + m - p;
  for (j=0; j<k; ++j) a[i*20+j] = i*37+j+7;
}
```

新算法生成 `lower=m-p`、`upper=2*(n-1)+m-p`，加上首行值 `first=m-p`。实际树的三个宽度测试表达 `first>0`、`lower>=0`、`upper<=20`。负行系数则交换 0 和 n−1 的作用，例如 `U=m-2*i+p` 得到 `lower=m-2*(n-1)+p`、`upper=m+p`。实现中的计数与源参数 n 明确重复排列；它们都是实际 temp 读取。

`compile_parametric_envelope_width_correct` 证明实际检查完成，且接受意味着首行非空及所有 `0<=i<n` 的宽度界。`parametric_envelope_refines_width` 再推出旧宽度条件的接受，供原有局部 candidate 证书消费。新程序执行新宽度树；这个蕴含证明不执行旧宽度树。

[parametric_envelope_guard_condition](../prototype/interface/ClightParametricEnvelopeGuard.v) 在 header 和参数范围已经接受的域中使用这份证据。检查次序为 header、参数范围、新宽度、真实数组检查。复用的 `replace_readonly_stage` 证明新宽度拒绝时 suffix 不执行；接受时先建立旧宽度接受，再取得 suffix 的安全性。这保留原有 source-derived D，没有把待证数组或 alias 前提加进 D。

编译期 arity／编码／最终机器范围检查不通过时，`choose_parametric_envelope_width` 保留旧宽度检查。旧宽度 lowering 的成功仍是源选择和旧局部证书的条件，本阶段没有据新编码声称扩大其源选择域。正常输入的运行时拒绝执行原 source。首行为空但后来有非空行时也回退，因为当前数组观察证据依赖首行非空。

通过同一 untrusted proposer 的实际 interchange、mapped、tiling 或 schedule 核对后，现有 [compile_preserving_parametric](../prototype/interface/ClightParametricCompiler.v) 安装结果并进入 CompCert 后端。完整端点仍是 `compile_preserving_parametric_correct` 的 Csem→Asm backward simulation。

## 最难的边界与尚未完成的工作

本阶段关闭盒内全称覆盖、实际 signed 比较编码、依赖 suffix 的安全替换及真实候选消费。旧宽度检查本来也是一轴符号 endpoint 检查；替换它不等于已减少 footprint 枚举。性能和作者证明负担尚未测量，不从端点数或 Clight 字节推导收益。

原拟 pointer 快捷检查需要修正：当前 D 保证源访问 `p+k` 的 capability，却不保证原始 p weak-valid。例如地址偏移可以在运算后进入合法访问区域。CompCert 指针比较有自己的有效性条件，因此不能直接先比较 p/q，再用 offset 包络判断 separation。后续方案须由真实源前缀／placement 提供比较所需的观察证据，或设计只使用已许可访问地址的推导；否则保留现有 scan。不新增一个调用者无法从源推出的 base-valid 假设。

一般深度 affine 源、非盒状域、完整物理 pointer separation 的符号条件、该使用者的任意发散 fallback，以及同例 proof-burden／性能比较继续在 [当前计划](current-work-plan.md) 中验收。文献定位仍受 OLO、Chamois、Peek 和 CoreJIT 的已有服务约束；本阶段不据条件替换或 local-to-global 本身宣称新颖性。
