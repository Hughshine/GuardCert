# 实际 initialized double source：factory、整程序证明与 native 安装

[无 initializer 的 double nests 后继](reduction-double-installation.md)现已接通原
mvt 的相继 reduction 和逐 site coordinate witnesses，覆盖增为4/62。下文保留
本阶段的三个原案例、编译器和实验边界。

2026-10-09。[安全入口与真实 pipeline](initialized-double-pipeline.md)的整程序
后继已安装并执行原 `mxv` 的初始化/reduction fission 和原 `matmul-init` 的
fission＋i/k/j。原 `matmul` 路线保留，非恒等原案例覆盖为3/62，完整目标未完成。
[机器可核对摘要](initialized-double-installation.json)绑定全部证明和执行证据。

## 使用者与接口

源码使用者给带 `#pragma scop` / `#pragma endscop` 的 C 和调度策略。不要求源码
使用者填写 source/model、header load、point bounds、frame 或 context 的证明。
Scheduler 和坐标交换见证提出数据，由实际 checker 核对；未标记代码不进入优化。

当前新 factory 支持非空外层 initialized I64 nests，各层使用同一个 global I64
bound，leaf 包含一个 double initializer 和一个 double reduction assignment。
Tensor rank、dimensions、global IDs、outer IDs、IEEE 运算树和 affine accesses
来自实际 checked source 和声明。相继不同 nests、多参数界限和任意 statement
bodies 尚未覆盖。旧三参数 `matmul` 仍走先前单独证明的路线。

```text
check_initialized_double_region actual_program live typed_pool schedule swaps source
compile_selected_double_program chosen_labels private_count schedule swaps Csyntax_program
```

`private_count` 是资源参数。私有 IDs 从 actual public scope 提议，然后重新检查
typed captures、scratch pairs、freshness 和 lowering；Native 默认给16个临时变量。
不足会静态拒绝。按实际 generated candidate 推导数量仍待实现。

## 条件及证明责任

Factory 从实际 accesses 建立 affine interval bounds，检查 initializer/reduction
的所有 reached coordinates。32步二分提出正界限；最终 verified footprint checker
决定是否可以使用它。正确性不依赖搜索最优性或单调性证明。原 extent100、padding2
得到 `0 <= N <= 98`；extent104变体得到 `0 <= N <= 102`。这是充分条件，
不声称 weakest precondition，也没有 benchmark 名称分支或手写范围 lemma。

Runtime 使用已有两次有序 I64 比较、接受后的 I32 capture 和私有 flag 分派。
检查不写公共 memory。原程序执行许可 header 读取；这是语义证明起点，不是
runtime 预执行。接受产生 exact count 和全部 point-resolution 事实，拒绝运输
到 literal original source。Checked global bindings/block separation 建立这个族的
header stability，没有新增 runtime alias guard。Footprint/span 不推断 allocation
或 load permission，所需读取事实由具体执行桥提供。

| 责任层 | 本次交付 |
| --- | --- |
| Framework | 复用局部证书与有限组合接口，minimal kernel 不改。 |
| Language instance | 安全 capture、实际 Clight candidate 执行、private/public frame、I64 出口、source progress 和 scoped host 定律。 |
| Domain / 优化实现 | Actual source/metadata、affine footprints、充分界限提议及核对、实际 PolCert/Pluto pipeline、执行对应和 factory 组合。 |

`C_opt`／`C_derive`／`C_guard`／`C_host` 指证据来源。新 transformation 作者仍需
自己的 conditional correspondence 和前提 producer；已支持族的 C 用户不补内部
semantic callbacks。这沿用 `topdown/research-positioning@8ce9c8b` 的澄清。

完整链为 literal Clight → safe capture → source Loop → checked generated Loop →
lowered Clight → public exits → scoped guarantee → whole Clight → Csem→Asm。
局部 `checked_double_initialized_guarded_execution` 是 finite normal 执行定理；
独立 raw-source progress 和既有 scoped selected host 关闭安装义务。整程序端点
`compile_selected_double_program_correct` 是 backward simulation，没有将有限 iff
当作独立 divergence theorem。

## 实际验收

七模块839行、29个 audited endpoints、8 closed、478 reachable sources，最大42
inherited globals，无新增公理。23次 proof attempts 为7成功／16失败。第一轮
native extraction 缺少直接 Float import，拒绝证据保留，第二轮提取成功。

| 验收 | 结果 |
| --- | --- |
| 原 C 接受、未标记排除、phase/final refusal、负数／零 bound | 17/17 通过。 |
| 多 marked、marked＋identical unmarked、改名、改维度、类型／资源拒绝、动态界限 | 20/20 安装预期和 GCC modeled-state digests 通过。 |
| 公共 I64 controls 和旧 `matmul` 回归 | 7/7 通过。 |
| unchanged assembly 调试器 branch 观测 | 6/6，普通／零为 `[accepted,refused]=[1,0]`，负数为 `[0,1]`。 |

两个 marked 各调一次 scheduler、各安装一次。Public controls 初始为 `[17,23,29]`，
零／负界限为 `[0,23,29]`，保留未到达的 inner controls；positive `mxv` 为
`[96,96,29]`，`matmul-init` 为 `[96,96,96]`。摘要与相应原 C 的 GCC
`-O0 -ffp-contract=off` 执行比较，观测每个 modeled scalar/array element。

动态完整调用各测七次，包含 initialization 和 digest。`mxv` unmarked／accepted
medians 为0.001765／0.001855秒，compile walls 为0.057108／0.576038秒；
`matmul-init` 为0.006396／0.005101秒，compile walls 为0.059793／1.837756秒。
仅小输入诊断，未证明收益或分离 guard 成本。摘要绑定10,315文件。

## 后续与复现

下一项从 `mvt` 等相继 nests 和真实 tiling／ISS configs 推动表示扩展，每项携带
actual factory、host 和 Csem→Asm。资源自动计数、其余原62案例、BT、LLVM/SPEC
调查、larger tiers 和完整成本继续保留在 goal。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_initialized_double_installation.py --validate
python3 scripts/summarize_initialized_double_installation.py --validate
```

新 attempts 使用新目录名，不覆写已有证据。入口为 `build_initialized_double_compiler.py`、
`check_initialized_double_compiler.py`、`check_initialized_double_contexts.py`、
`check_initialized_double_public_exits.py` 和 `trace_initialized_double_guard_paths.py`。
