# 逐步宿主：潜在无限循环中的只读头部 rewrite

2026-10-05。本例在每次实际求值位置改写有限表达式，不将整个循环作为完成的宏片段。它与 [固定上界的完整循环版本化](clight-equality-loop-case.md) 是不同用法：这里不需要循环排名，也没有由此得到整段有界多面体实例域。

## 变换与检查时点

源头部是 `(int)i != (int)n`，候选为 `(int)i < (int)n`，检查为 `(int)i <= (int)n`。这里的 `i`、`n` 是 unsigned32 temps，cast 建立实际 signed word view。检查接受时两个比较返回同一个完整 `val`，不只具有相同真假；失败执行原比较。

检查位于每次头部求值位置：

```c
for (; /* 每次到达这里检查当前 i 和 n */ ; i = i + 2U) {
  if ((int)i <= (int)n) {
    if (!((int)i < (int)n)) break;
  } else {
    if (!((int)i != (int)n)) break;
  }
  body;
}
```

这段代码展示分派的等价 C 结构。编译器在 Clight 层插入实际检查，产物由 [ClightReadonlyTestSyntax.v](../prototype/interface/ClightReadonlyTestSyntax.v) 生成，保持 unsigned latch 和 body 原结构。

上界可以被 body 改变，步长也可为 2。每次检查使用当前状态；前一头部接受不成为后续头部的入口事实。odd target／step=2、或 `n` 与 `i` 同时加一时，源可能无限执行，头部仍可以逐次安全 rewrite。源可能发散这一点不靠一个终止执行的 `exec_stmt` 来覆盖。

## 使用者接口

[ClightReadonlyExpression.v](../prototype/interface/ClightReadonlyExpression.v) 为已有语言无关 `GuardedRewrite` 核实例化另一个宿主。命令是 `Evaluate expression` 或有限的 `Dispatch tree yes no`，观察为实际 CompCert `val`，执行为真实 `eval_expr` 与决策树路径。检查仍要求所有可达测试安全，并保持同一个实际 `clight_entry`；这里没有私有 scratch 写入。

使用者交付 `readonly_expression_rule source`：

| 数据／证书 | 要求 |
| --- | --- |
| source／candidate | 两个实际表达式，候选类型与源类型相同 |
| domain／premise | 与实际入口绑定的定义域和接受前提 |
| `expression_check` | 共用核的 `readonly_condition`，检查安全、可用、只读及接受含义 |
| `expression_local` | 共用核的 `conditional_equivalence`，完整结果 `val` 双向对应 |
| `expression_entry` | 每个实际源求值均建立检查域，不依赖外围循环终止 |

`readonly_expression_contract` 把这些证书转成实际小步宿主消费的 expression contract。使用者已有片段检查证书时，`fragment_condition_for_expression` 复用相同的检查语义和安全字段，而不用重证检查。

[ClightEqualityHead.v](../prototype/interface/ClightEqualityHead.v) 是这个接口的使用者。它从实际源比较求值建立两个 temps 的 `Vint` 依据，注册一个只读 `≤` 检查原子，经既有 Boolean 树合成核生成 guard。签名不是从任意 Rocq `Prop` 自动求出检查；本例是带局部正确性定理的规则模板。

## 全局证明为何不需要循环 rank

[ClightReadonlyTestProof.v](../prototype/interface/ClightReadonlyTestProof.v) 提供真实 Clight forward simulation。源比较求值后，目标完成有限只读分派，再执行具有相同结果的候选／源比较，进入对应 continuation。每个源小步对应至少一个目标小步；外围无限执行、调用、事件、break／continue 和 goto 通过原结构关系运输。

当前小步宿主支持赋值 RHS、`Sset` RHS、return 表达式，以及具体 `Sifthenelse test Sskip Sbreak` 头部。其他分支保持结构遍历。这个限制使分派只复制无 label 的叶片，不复制任意分支／label，保持 `find_label` 对应。它不是任意表达式上下文重写器。

宿主证明复用了现有表达式小步宿主的结构，并显式增加头部匹配与分派 case。假设审计使用既有 `ClightTreeRewriteProof.transform_program_correct` 作为 STEPWISE 基线；它比片段的六项基线多 external function 和 inline assembly 的 properties，分别用于完整调用及事件运输，不是新假设。

`compile_readonly_tests_correct` 把这个语言宿主接到完整 Csem→Asm backward simulation。`compile_readonly_tests_after_correct` 允许使用者先运行任意已有 Clight pass，只需提交该 pass 的实际 forward simulation。统一入口现在先做 projected region rewrites，再做逐步头部／值表达式 rewrite；两个 pass 的全局证明组合，而非假定两个局部前提在程序入口同时成立。

## 执行与范围

复现方式：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-equality-head-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-common-native
```

独立入口和统一入口各通过 333 次 C 函数调用、284 行输出、十处实际 guarded expression contexts；完整编译接口 184 个端点审计通过，STEPWISE 基线为现有八项、COMPILER 为现有 35 项，无新增全局公理。fixture 包含步长 2、每次 body 改变上界、signed view 负值／跨边界、unsigned 回绕、null 空路径、volatile body、goto／外围循环，以及 return／assignment 的完整 Boolean 值。两个明确无限的源函数只编译和检查实际 guard／candidate／fallback，不能用有限原生输出验证它们的发散行为；相应保证来自小步模拟定理。

这个功能不允许仅凭某次局部 `≤` 证据将整个循环建模为有限整数域，也不支持在源片段可能无限时把任意调度／tiling 当成宏片段替换。Optimistic Loop Optimization 的整段变换仍需要稳定性、模型对应、依赖合法性及相应上下文证明。没有性能测量。

十四种提取编译器配置在当前审计下重建并全部通过原生回归。与 `3324a6b` 的 17 份既有报告比较，只有统一入口的等式退出程序生成了预期的逐头部 guard，其余 16 份源码／Clight 摘要相同。统一旧等式退出程序也通过 703 次调用，脚本分别确认整段条件与回退头部的后续检查。

后续 [普通表达式比较模板](clight-loaded-comparison-case.md) 将同一选择器扩展到任何类型为 signed32 的实际操作数，不再只取两个 unsigned temp 的 cast。原 `head_constant` 现在也被改写；原调用／输出数保持相同。新增 ordinary load／computed operand／volatile 快照程序在独立／统一入口各通过 737 次调用，完整接口增至 184 端点；十四种配置重建回归通过。与 `651e156` 的 19 份既有报告比较，仅两份头部程序因新增常量 guard 改变 Clight，另外 17 份源码／Clight 摘要相同。
