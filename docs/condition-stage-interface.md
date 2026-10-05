# 带依赖的只读检查接口

本接口复用“前一个检查通过，才能安全执行后一个检查”的证明。它不固定语言表达式、整数、内存或源程序语义。使用者提交检查及语义证书；语言提供检查组合构造器；框架生成按顺序执行的检查，并证明只读、安全、可用及接受含义。

## 语言需要提供什么

[ReadonlyConditionComposition.v](../prototype/interface/ReadonlyConditionComposition.v) 的 `readonly_check_algebra H` 在既有 `guard_host H` 之上增加两个构造器及四个语言定律：

| 字段 | 职责 |
| --- | --- |
| `constant_check b` | 生成返回常量 b 的检查 |
| `then_check first second` | first 接受时执行 second；first 拒绝时直接拒绝 |
| `constant_check_exact`／`constant_check_safe` | 常量检查的实际分派、状态不变和安全 |
| `then_check_exact` | 实际组合执行恰好是接受后执行第二个检查，或第一次拒绝；保留真实中间状态 |
| `then_check_safe` | 第一项安全且其每个接受出口支持第二项安全，则组合安全 |

这些定律需要针对真实语言证明。仅有程序层面的 `if` 并不能自动得到检查语法的组合设施；语言适配器应提供这种构造及其分派证明。框架的只读证书再证明真实中间状态等于原入口，不隐藏事件、未定义访问或发散。

[ClightConditionComposition.v](../prototype/interface/ClightConditionComposition.v) 已用实际 `decision_bind` 实例化该代数。它把第一棵决策树的 true 叶子接到第二棵树，false 叶子保留拒绝，并证明所有可能到达的测试安全。普通 load 可以进入表达式，但规则作者仍须证明它在该阶段入口域内有定义。

## 两阶段使用方式

使用者提交：

```text
FIRST  : readonly_condition H D P first
SECOND : readonly_condition H (D and P) Q second
```

框架的 `sequence_readonly_conditions` 返回：

```text
readonly_condition H D (P and Q) (then_check A first second)
```

第二份证书可以使用 P 来证明读取、地址计算或算术检查安全。它不必在仅有 D 的状态上成立。第一项拒绝后，第二项不会被执行；拒绝只说明没有建立 P，不能被当作 `not P`。

这份组合证书可直接交给原有 `guarded_rewrite_equivalent`，再通过语言宿主接入完整程序。局部源／候选等价仍由规则作者在 `D and P and Q` 下提供；本设施不替使用者选择变换或推断任意最弱条件。

## 任意有限阶段

`condition_stage H` 包含实际检查 `stage_condition` 和建立的性质 `stage_property`。`certified_condition_stages` 要求第一项在 D 上有只读证书，第二项在 D 加第一项性质上有证书，以此类推。

`synthesize_condition_stages A stages` 只读取检查语法列表和语言构造器，生成有限的顺序检查。`synthesized_stages_readonly_condition` 证明接受时列表中全部性质成立，并证明安全性、可用性和入口状态不变。阶段证书用于证明，不会成为查询源执行的运行时 oracle。

列表的顺序是使用者显式提供的。框架不会自动交换有依赖的检查；检查可以是由已有前提公式合成器生成的一整棵树。因此，Boolean 公式组合与带依赖的阶段组合可以共同使用。

## 实际 memory-bound 规则

已有 `i<*bound` 源循环在 body 中写固定的 `*out`，候选缓存上界。新的 [ClightLoadedBoundGuard.v](../prototype/interface/ClightLoadedBoundGuard.v) 使用这套设施组合两个证书：

1. 第一项检查 `i==0`，在源入口域 D 上建立该事实。
2. 第二项检查实际循环头为真，然后才比较 out 与 bound；它的入口域是 `D and i==0`。

D 从实际源头部得到上界 load 的定义性。仅在 `i==0` 且源头部为真时，实际第一轮 source store 才给出 out 的写权限；该权限与 bound 的读取权限共同保证指针相等检查有定义。因此第二阶段的读取安全证书确实依赖第一阶段接受的事实，不能独立要求 out 在所有 D 状态上有效。

第二阶段的接受性质是源头部为真且两个单元分离；框架组合后得到候选局部证明需要的完整前提。生成的 guard 与既有条件树相同，完整编译器消费的是新的组合证书。这个改动复用证明，没有增加运行时检查或性能收益主张。

## 验证与当前边界

三个新增语言无关组合端点闭合证明，纯接口共 43 个端点；Clight 代数、决策树安全及实际表达式证书通过，语言适配层共 57 个端点且不超过既有六项基线。完整编译器 141 个端点的假设审计无新增公理；十二种配置重建并全部通过原生回归。与前一阶段 `efe1870` 比较，15 份原生报告中的源码／生成 Clight 摘要全部相同，包括内存上界与统一 pass 的实际程序。复现使用 `make interface-compiler-proof` 和 `make interface-native-suite`。

代数不保证最小条件、最优顺序或检查代码大小。当前 Clight lowering 会在每个接受叶子接入后续树，多接受叶子的阶段可能复制后续代码；需要单独的控制流共享证明来消除这一成本。源前缀稳定性仍由具体语言／变换实例提供，此接口只运输已建立的阶段事实。
