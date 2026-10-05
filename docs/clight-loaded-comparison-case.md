# 普通表达式／load 的有条件比较 rewrite

2026-10-05。本阶段将 [逐步求值宿主](clight-stepwise-head-case.md) 的规则从两个寄存器 cast 扩展到实际 signed32 操作数，包括普通 load、计算表达式和常量。它补充条件的表达能力及检查安全实例，没有建立整个循环的有限域或跨迭代稳定性。

## 规则模板与使用方式

[ClightOrderedInequality.v](../prototype/interface/ClightOrderedInequality.v) 暴露 `ordered_inequality_rule left right LEFT RIGHT`。`left`、`right` 是实际 Clight 表达式，两个类型证书均要求 `typeof operand = type_int32s`。模板定义：

```text
source    = left != right
candidate = left < right
condition = left <= right
```

源、候选和检查结果类型都是 signed32。前提解释为当次两个实际机器 word 的 signed 值有序，不是源表达式的数学整数模型。模板从两个操作数及类型证明生成真实检查和 `readonly_expression_rule` 证书，使用者仍决定从程序哪里取得它们、选择哪些位置和如何遍历。

类型／形状选择器核对根是 `One`、两项实际类型及完整结果表达式。它没有把 unsigned、float、long 或指针比较纳入这个模板。float 的 unordered／NaN 以及指针比较安全需要自己的性质和证明。表达式宿主仍只支持 assignment／set／return 根和具体 skip/break 头部；它不自动搜索任意嵌套上下文。

本例直接使用既有 `readonly_expression_condition` 将“检查有定义”和“检查接受建立前提”包装为共用核的只读证书。这里是一个有证明的专用检查生成器，不是从任意 `Prop` 自动生成程序。与已注册 Boolean 原子、顺序检查阶段相同，它最终输出 `readonly_condition`，局部及全局框架不需要了解其操作数的具体语义。

## 检查怎样安全读取内存

检查域 `comparison_domain` 是两个表达式在当次入口实际求出 `Vint`。`comparison_source_values` 从实际源 `!=` 的求值反向得到这两项依据，因此没有预设内存权限 metadata 或上界不变。

`comparison_condition` 用这两个真实求值构造实际 `≤` 检查，证明所有可达测试安全、可用、入口状态不变，接受建立当前 signed order。`comparison_local` 再用表达式确定性和机器比较定理证明完整 `val` 双向一致。全局桥接使用已有逐步宿主及完整 Csem→Asm 端点，无需新的循环进展协议。

普通 Clight `eval_expr` 是只读求值。即使操作数包含 load，guard 与本次候选／回退使用同一入口内存。这个实例会重复求值操作数，不能把这项局部确定性扩展为两次循环头部之间的内容稳定；body 可以改变它们下一次读到的值。

## 实际改变 bound 的 alias 例子

```c
int i = start;
for (; i != (int)*bound; ++i) {
  *out = (unsigned int)i + 1U;
}
```

当 `out == bound`、`start=0`、入口 `*bound=5` 时，源执行一次 store，将 bound 改成 1，然后退出。检查在每次头部读取当前值：入口 `0≤5` 接受，下一次 `1≤1` 接受并使用 false 的 `<`。整个过程中从未缓存入口 5，也没有假定 non-alias。

入口 bound 为 unsigned 表示的 `-3` 或 `INT_MIN` 时，第一次 `0≤(int)*bound` 拒绝，原 `!=` 仍执行一次 store，随后 bound 为 1，第二次头部退出。这是检查时点的重要例子：它不能使用原 `i<*bound` 空路径的结论来删掉 `!=` 的 body。

## Volatile 的边界

C 前端将真正的 volatile load 降为带事件的 builtin。新规则不在 guard 里复制这个操作。fixture 中显式 `(int)*volatile_bound` 先由源代码执行一次 volatile load；后面的比较引用它的 temp 快照。guard 只读该快照，候选／回退引用同一值。实际 Clight 核对 load 恰一次且位于 guard 之前；整体事件运输由既有小步证明保证。

这与把 volatile load 本身作为可以任意重放的普通原子不同。普通内存 load 在 guard／比较中重复，volatile 的源事件保留原位置和次数。

## 验证与未完成项

复现使用 `make interface-equality-head-native` 或 `make interface-common-native`；两个目标还运行同一 [loaded_equality.c](../prototype/interface/tests/loaded_equality.c)。完整接口 184 端点编译／假设审计通过，没有新增全局公理；纯接口 43 个闭合端点、原 Clight 57 个端点不变。十四种提取配置已重建并全部通过原生回归。

独立入口和统一入口各通过 737 次调用／737 行输出，fixture 覆盖 546 次循环网格调用（273 alias、273 分离单元），三次 extreme alias bound、三个 null 空路径，35 次普通 load 的完整比较值、144 次 bitwise 计算操作数、五次源 volatile 快照值和一个 signed 常量头部。所有原生 signed 自增保持在范围内；不执行 C signed overflow。无限外围只编译／检查。

本例没有提供 non-alias 检查、稳定 preload、二维调度、一般运算树 non-overflow 合成或检查成本优化。真正的整段乐观循环版本化仍需要另证明模型对应、持续的前提和调度合法性。没有性能测量。

与 `651e156` 的 19 份既有报告比较，两份 equality-head 程序生成 Clight 增加了预期的 signed 常量头部检查，源码保持相同；另外 17 份源码及 Clight 摘要相同。原头部程序仍各通过 333 次调用／284 行输出，现在有十处实际改写。新增 fixture 与原有 fixture 的证据分别保存在 `build/interface-loaded-equality-native/`、`build/interface-common-loaded-equality-native/` 及原头部报告中，绑定源码、Clight、汇编、提取编译器和证明报告摘要。
