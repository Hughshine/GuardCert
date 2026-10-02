# 问题定义与证明框架

本页描述已经实现的入口 fallback 主线。跨领域调查后的候选接口见 [框架扩展设计](framework-extension.md)，新颖性边界见 [研究定位](research-position.md)；其中设计义务不代表已完成证明。

2026-10-02 更新：presumption 编码与 condition 合成已成为核心接口，详见 [分类与合成说明](presumptions.md)。真实 Clight 分支与表达式适配器已接入 `Csem → Asm` 正确性，并提取运行了 C 示例；新表达式接口解释完整入口快照，支持四个 rewrite 及严格表达式上下文提升。真实 Mem 的无别名 load-hoisting 已有局部端点证明，尚未接入 Clight。详见 [常见 rewrite 接口](common-rewrites.md) 和 [接入说明](compcert-integration.md)。独立语义核仍采用有限宏转移。

## 问题对象

给定程序 `P`、其中一个片段 `R`、候选变换结果 `R'` 和前提 `A`，构造片段 `V`：

```text
在每次合法入口处运行 guard
  Accept  → R'
  Reject  → R
```

目标不是只证明 `A → R' ≈ R`，而是证明将 `R` 替换为 `V` 后，完整程序在原有语义保证下仍正确，并能与 CompCert 后续 passes 的仿真组合。

这里先选择 **入口版本化**：guard 在被优化片段产生效果之前作出决定。更一般的 **中途去优化** 会在优化代码已经执行之后恢复源状态，需要恢复点、变量映射、内存表示与续体映射。二者共享条件仿真思想，但失败协议不同；不能由入口版本化定理直接推出中途去优化正确性。

## 面向真实 IR 的接口草案

一个插件提交以下信息。证明层的 `A` 可以是语义谓词，但生成代码使用的 presumption 必须属于有明确表达能力的 DSL。编码对应、入口推导和执行条件不能由任意 `Prop` 的接口替代。

| 接口项 | 含义 | 应由谁证明或验证 |
| --- | --- | --- |
| `RegionInterface` | 入口、出口标签及其映射，live-in/live-out，轨迹，内存和控制边界 | 通用 IR 适配器及区域适用性检查器 |
| `Original / Candidate` | 实际原片段、优化片段，以及身份绑定 | 插件或经过证明的候选验证器 |
| `Assumption A` | 足以支撑这次变换的语义前提 | 插件提供；可靠性由条件正确性定理兜底 |
| `PresumptionEncoding` | 可检查义务与 DSL 的独立语义对应；必要时先证明入口义务推出区域义务 | 各语义类别的编码器及插件实例 |
| `ConditionSynthesis` | DSL 到条件程序；成功执行的真/假与数学语义对应 | 通用合成器，本轮已有证明 |
| `StateRelation J` | 源与目标入口/出口状态的对应，包括上下文可见内存 | 插件提供关系；通用框架要求上下文兼容性 |
| `ConditionalSimulation` | 在 `A` 下，候选正确模拟原片段，包括轨迹、所有出口和发散 | 每个算法证明一次，或每个候选由已验证验证器核对 |
| `GuardImplementation` | 执行后产生 Accept/Reject，或内部可恢复检查失败 | guard 库与 IR lowering 证明 |
| `GuardCorrectness` | 安全结束、接受推出前提、拒绝可恢复原入口、无新增可观察效果 | guard 库；插件补充 preload 和有效期证据 |
| `ContextCompatibility` | 入口对应，出口状态可被余下程序继续模拟；排除非法内部入口 | IR 适配器一次证明，并检查各次区域实例 |

`J` 的意义是允许目标使用不同临时变量、忽略死寄存器或改变私有表示。只知道两个状态通过 `J` 关联，并不能自动把它们送回任意上下文；上下文观察的 live-out、内存和续体必须服从这个关系。

如果 guard 读取内存，把它建模成单纯的 `State -> bool` 会掩盖关键义务。真实接口应描述一次有执行轨迹的计算，并证明：

```text
guard 从合法入口 σT 出发，经过有限且安全的内部步骤得到 decision、σG；
这些步骤不产生新增可观察事件；
Reject 时 σG 可恢复到原片段的入口状态；
Accept 时 A 对当前进入以及所需有效期成立，σG 与候选入口相容。
```

这里不要求检查绝不读取源程序尚未读取的地址，而是要求提前读取具有独立的安全证据且不改变可观察行为。volatile、原子和有副作用的外部调用不能由“普通只读”默认处理。

## 独立语义核的较强、较小契约

[GuardedRegion.v](../theories/GuardedRegion.v) 使用：

```text
Region = State → (finite events, exit, final State)
exit   = Jump pc | Return value | Trap

check_sound:
  check σ = true → A σ

conditional_correct:
  A σ → optimized σ = original σ

versioned σ = if check σ then optimized σ else original σ
```

相等包含完整状态、事件列表和出口。guard 最终仍是 Gallina 中的总函数，不能修改状态；新的构造路径通过有语法和执行语义的 condition 产生这个 bool。因此当前模型中的安全结束与透明性仍由表示方式保证，完整机器 guard 的这些性质还需要 lowering 证明。

`versioned_correct` 给出所有入口状态上 `versioned σ = original σ`。计划 `plan` 可以指定多个 CFG 位置，但必须提供 `plan_matches`，证明每份变换描述中的 `original` 就是该位置实际的原片段。`apply_plan_step` 随后给出完整 CFG 的逐步相等。

据此已经证明：

- `whole_program_finite`：任意初始配置、事件轨迹和结束配置上的有限执行等价。结束配置可以是正常返回，也可以是错误；定理也覆盖有限前缀。
- `whole_program_infinite`：无限 CFG 执行等价，包含始终不产生事件的执行。每步事件列表允许为空，避免把静默发散漏掉。
- `contextual_replacement` / `contextual_replacement_infinite`：任意外围 CFG、入口配置和片段位置上的单位置上下文替换。

外围 CFG 可以分支、反复进入片段，也可以跳转到错误位置。片段内部只能由这次宏转移执行，不能被外围直接跳入。这个条件在原型中由类型构造保证；真实 Clight/RTL 接入必须有区域提取和适用性证明。

所有片段都是总的有限宏转移：内部循环的终止性被这个类型假定了。外围 CFG 的发散定理不能弥补这一限制。证明真实循环变换时，必须把片段内部发散纳入仿真，或者对所选片段显式证明终止。

## 两个共享接口的插件

[Examples.v](../theories/Examples.v) 中的插件不依赖彼此的语义。

1. **消除回绕比较。** 源片段计算 `result := ((x + 1) mod 256 < x)`；候选计算 `result := 0`。前提是 `0 ≤ x < 255`。`x=255` 时原结果为 1，说明不能无条件替换。guard 用 checked addition；中间运算溢出则拒绝。
2. **交换两个写操作。** 源片段先 `mem[p]:=1` 再 `mem[q]:=2`；候选交换顺序。guard 检查两下标在范围内且不同。`p=q` 时结果不同，必须回退。

算术是显式无符号 8 位 word 模型，不是未经类型分析的 C 表达式；C 的整数提升必须在接入时单独处理。内存是列表；越界写在这个模型中保持列表不变。它没有 CompCert 的 block、permission 或指针 provenance，不证明真实 C 的越界访问安全。

[CheckedGuard.v](../theories/CheckedGuard.v) 提供常量、输入、加法、比较和短路合取。接受的加法结果等于数学整数结果；任一中间表达式不能安全求值就拒绝。它刻意允许保守拒绝：即使最终数学比较为真，也可能因中间表达式越界而拒绝。没有最弱前提、Presburger 消元、乘法或 preload 的证明。

## 接入 CompCert 时的证明链

```text
实际 IR 原片段
   │ 区域提取及接口正确性
   ▼
条件仿真 + 安全 guard
   │ 通用版本化定理
   ▼
带回退的局部变换
   │ 入口/出口/续体兼容性
   ▼
实际 IR 完整程序仿真
   │ CompCert 已有 pass 仿真的组合
   ▼
目标程序行为满足 CompCert 的语义保持关系
```

实际 Clight 适配器已使用 CompCert 的 [Smallstep](https://compcert.org/doc/html/compcert.common.Smallstep.html) 仿真及组合，并通过 [Behaviors](https://compcert.org/doc/html/compcert.common.Behaviors.html) 的精化关系给出规格保持。它另行证明真实小步语义上的语句／续体关系，没有直接把独立宏步模型的相等定理作为 Clight 仿真。独立模型中的 `Trap/Faulted` 仍只是其显式结果。

首个真实适配器版本化 `if a then L else R`：guard 接受时进入 R，否则执行原 if。`encoded_branch_rule` 要求编码对应、实际 condition lowering 和前提下原条件恒假的证明；统一证明覆盖函数调用、外部事件和所有 Clight 续体。guard 无 load，L/R 内不得有 label，程序其他位置的 goto 仍支持。L/R 可以含调用和可能发散的循环。这个接口尚未接受任意候选 R′ 或一般循环变换的条件仿真。

新增 `encoded_expression_rule source guard candidate` 把独立 Q、编码、类型保持、condition lowering 和局部值保持交给插件。通用 pass 在临时赋值、内存赋值右侧和 return 处版本化；`select_deep_sound` 将一个子表达式证书提升到严格运算／cast 上下文。`compile_with_rewrites` 组合两种 pass 的完整程序 simulation，再组合原有后端。它还不是任意有副作用片段或不同状态表示的区域接口。

## 后续原型的验收标准

| 阶段 | 新增结果 | 验收条件 |
| --- | --- | --- |
| M0，已实现 | 独立语义核、编码与合成、多个 rewrite、通用全程序定理 | Rocq 9.2 完整编译；接受与回退均有实例；边界反例可复现 |
| M1，分支与表达式适配器已完成 | 两种 Clight 入口语义、Csem 到 Asm 定理；多个规则复用各适配器 | Rocq 编译与提取后的 C 示例均通过；任意候选区域接口仍待扩展 |
| M2，unsigned32 算术实例已完成 | 等式／无回绕／Truth 的 Clight lowering；真实 Mem 的 Disjoint 编码和局部 load-hoisting；安全 preload 尚未完成 | 算术接入 backend；内存实例仍需实际 guard 和小步上下文提升 |
| M3，进展已实现 | Clight plus simulation 保留内部／外围发散；关系式状态接口尚待扩展 | 下一步支持不同临时变量、候选表示与内存关系 |
| M4，可选扩展 | 中途去优化与状态恢复 | 恢复映射和续体证据；不能依赖 M0 的原入口回退定理代替 |

已有分支及四个表达式 rewrite 的 C 到汇编完整证明。算法性能和 guard 成本属于独立实验，本轮没有提速证据，也没有实现 CGO 2017 的完整假设生成算法、完整 DSL lowering 或一般循环变换适配器。
