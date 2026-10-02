# Presumption、condition 合成与 conditional rewrite

## 先确定处理哪类变换

目标类是：具有可描述的入口前提，且在该前提下有局部等价或仿真证据的变换。算法可以产生整个 region，也可以只改写表达式、语句或分支。入口版优化在产生效果前作出选择，检查失败回到原入口执行原代码。

| 变换形态 | 所需前提举例 | 当前状态 |
| --- | --- | --- |
| 表达式或分支 rewrite | 数值范围、无回绕、已知布尔事实 | unsigned32 分支、除法／取模 specialization、条件算术取消和 Truth identity 均已接入 Clight 与端到端定理 |
| 语句重排 | 不相交的读写区间、无别名 | toy-memory 写操作交换；实际 CompCert Mem 的无别名 load-hoisting 已有局部端点证明，未接入 Clight |
| 循环变换 | 控制算术对应数学整数、访问关系和依赖、整个循环有效期 | 接口目标；本轮没有实际循环算法接入 |
| 特化与检查提取 | 参数值、preload 安全、路径约束 | 变量除数为 2 的特化已接入；检查提取和 preload 尚未实现 |
| 中途去优化或表示变换 | 已执行效果可恢复，源/目标状态及续体映射 | 首阶段之外 |

## 分类与首个语言

核心 DSL 不接受任意 `Prop`、用户函数或自由的语义回调。语义义务可以写在证明层，但编码器只能用下列语法表达它，并提交对应定理。

| 类别 | 首个 presumption 表达能力 | 边界 |
| --- | --- | --- |
| 标量约束 | 常量、标量变量、加减、`≤`、`=`；范围可用合取表达 | 有限 word 的 unsigned 模型；常量和所有中间值可能导致拒绝 |
| 算术语义 | `NoOverflow(expression)`：所有叶子和中间结果均在 word 范围 | 不含 signed 范围、乘除、移位和转换规则；signed overflow 与 unsigned carry 必须分别建模 |
| 内存区间 | `InBounds(pointer,length)`、`Disjoint(pointer,length,pointer,length)` | 显式 block/offset/extent；已有真实 CompCert byte-range 解释；不相交不等于访问有效或 permission |
| 布尔结构 | `True`、`False`、`and`、`or`、`not` | 执行语义显式保留检查失败；不能把失败当作 false 后随意取反 |
| 区域有效期 | 入口条件足以支撑局部正确性，由插件证明 | 没有任意状态历史谓词、量词或迭代域投影算法 |
| 不变读取 | 本轮不含 load | 需要安全读取、稳定性和前提依赖的独立证据 |

模数是语义参数，不再固定为 256。实例用 8 位 unsigned word，CompCert 算术桥接使用其实际 32 位 `Int`。指针 block 编号是模型中的身份，不是可直接从 C 指针读出的运行时字段；extent 是显式提供的元数据，不是一个可以任意查询权限的实现。真实内存原语的 lowering 必须证明这些表示的对应。

## 五个独立的义务

```text
区域所需语义前提 A
    │ 入口推导：Q ⇒ A（可以保守）
    ▼
可检查的语义义务 Q
    │ 编码：meaning(p, view(s)) ⇔ Q(s)
    ▼
presumption AST p
    │ 合成：执行产生 Some b ⇒ b = meaning(p, view(s))
    ▼
condition AST synthesize(p)
    │ 实现 / lowering：实际 IR 执行满足 condition 语义
    ▼
接受 ⇒ Q ⇒ A；检查失败或拒绝 ⇒ 原代码
    │ 局部正确性 + 上下文兼容性
    ▼
完整程序仿真
```

入口推导处理“整个片段中都需要成立”的义务，例如把有限迭代域上的无溢出性质转换成参数限制。它与把已得到的无量词条件编译成布尔程序，是两个步骤。本轮实现后一个步骤，并为具体实例提供前一个步骤的简单证明；没有实现 Presburger 消元或最弱条件推断。

`presumption_encoding` 单独要求编码对应；`encoded_condition_correct` 组合编码与合成，在成功求值时反映 Q 的真或假。`encoded_rewrite` 再结合插件的局部正确性，构造已有 `guarded_rewrite`。插件不能仅仅把一个手写 bool 塞进接口而跳过编码和合成证据。

## Overflow flag 的含义

用户提到的 IMPACT 2012 确实提供了这一模型。Figure 8 的表达式结果是 `(value,e)`，`e=true` 表示没有发生 overflow，Figure 9 让相关比较在检查失败时拒绝；文中指出处理器 flag 或小型 builtin 可以用于实现。其验证器 soundness 在该论文中仍是 Conjecture 6.2。[全文 §6、Figures 8–9](https://acohen.gitlabpages.inria.fr/impact/impact2012/workshop_IMPACT/cuervo.pdf)

本轮 `evaluate` 也返回 wrapped value 与 `arithmetic_ok`。复合表达式的 flag 同时包含子表达式状态和本次运算状态，后续运算不能清除已有失败：

```text
x = 255, modulus = 256
evaluate(x + 1) = (0, false)
evaluate((x + 1) - (x + 1)) 的 flag 仍为 false
```

`evaluate_flag_correct` 把这个 flag 与独立定义的数学范围语义对应。flag 是 guard 求值的显式结果，不是源程序中隐含的全局状态，也不承诺 CompCert IR 可以直接引用 CPU flags。

condition 有三个结果：`Some true`、`Some false`、`None`。`NoOverflow(e)` 是一个显式测试，因此可以正常返回 false，并被 `not` 取反；普通比较若因计算失败返回 None，其外面的 `not` 必须仍返回 None。二者不能混淆：

```text
x = 255
not NoOverflow(x + 1)          → Some true
not ((x + 1) = (x + 1))       → None
```

第二个数学公式为假。如果先把溢出失败变成 false 再取反，就会错误接受。`and/or` 通过显式条件分支实现短路；不需要执行的右侧检查可以跳过。首阶段采用保守策略：若已经执行的左侧检查失败，整个 condition 失败。

## 三个新增 rewrite

1. **分支条件恒假。** `if x<x then emit/trap else result:=7` 改为 else 分支。优化前提是 `True`；条件表达式恒假支持实际删除分支。
2. **前提下的死分支。** `if word_add(x,1)<x then emit/trap else result:=0`，在编码后的 `NoOverflow(x+1)` 下删掉 then 分支。`x=255` 必须回退，原程序的事件和错误出口都保留。
3. **优化前提恒假。** 前提 `x≤5 ∧ 10≤x` 永远不成立。即使局部正确性证明可因前提矛盾而成立，生成的 guard 也永不接受，候选代码永不执行。它验证的是回退路径，不算一次有收益的分支删除。

前两个情况中的“分支条件”和第三个情况中的“优化前提”，处于不同层次。本轮同时保留，避免把死代码消除与 vacuous correctness 混成一个例子。

## 当前可运行的连接

- [Presumption.v](../theories/Presumption.v)：语法和独立数学语义，含区间分离的含义证明。
- [Synthesis.v](../theories/Synthesis.v)：flag 语义、编码契约、condition 合成和对应定理。
- [ConditionalRewrite.v](../theories/ConditionalRewrite.v)：无溢出及无别名的编码证明、三种 rewrite、带事件和错误出口的完整程序实例。
- [CompCertArithmetic.v](../theories/CompCertArithmetic.v)：用 `Int.add / Int.sub / Int.ltu` 实现 unsigned checked addition，证明与合成器的算术原语一致。
- [ClightEncodedRule.v](../theories/ClightEncodedRule.v)、[ClightNoWrap.v](../theories/ClightNoWrap.v)：编码、lowering、局部正确性组成插件证书；`NoOverflow(x+1)` 的合成结果对应实际 Clight `x <= UINT_MAX-1`。
- [ClightExprRule.v](../theories/ClightExprRule.v)、[CommonRewrites.v](../theories/CommonRewrites.v)：完整入口快照上的表达式证书；`Equal(Scalar,Literal)`、`NoOverflow(Scalar+Scalar)`、Truth 的实际 lowering 和局部正确性。
- [CompCertMemoryRule.v](../theories/CompCertMemoryRule.v)：Disjoint 编码与实际 `Mem.load_store_other` 前提的对应，及合成检查下的局部 load-hoisting 端点。
- [GuardCompiler.v](../theories/GuardCompiler.v)：两种真实 passes 的 `Csem → Asm` 定理和规格保持。
- [synthesis_demo.py](../prototype/synthesis_demo.py)：独立可执行模型，生成 condition AST 并比较原程序与版本化程序。不是 Rocq 提取。

真实 IR 已有多个受限 lowering、分支和表达式版本化 passes，已提取执行两个 C 示例；完整 condition DSL 的 lowering、任意候选片段接口和可执行内存检查仍未完成。真实 Clight 证明不采用有限宏转移假设；独立 `GuardedRegion.v` 路径仍保留该假设。接口及证据边界见 [common-rewrites.md](common-rewrites.md) 和 [接入说明](compcert-integration.md)。
