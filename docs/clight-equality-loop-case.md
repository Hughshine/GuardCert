# 固定上界的等式退出循环

2026-10-05。本例处理 Optimistic Loop Optimization 的有界实例域需求中的一类：把等式退出转换成可用整数区间描述的顺序退出。它消费当前只读 API、实际循环对应和完整程序宿主。它不覆盖所有可能发散的等式退出循环。

## 输入、候选和条件

使用者交给框架的源片段为：

```c
unsigned int i = start;
for (; (int)i != (int)n; i = i + 1U) {
  *out = i + 1U;
}
```

初始化在片段外；条件在循环到达时读取当前 `i` 和 `n`。候选只将头部改为 `(int)i < (int)n`。检查为 `i == 0U && 0 < (int)n`。两项实际 Clight 测试均为只读，短路失败保留原循环。上界没有默认 cap=16，也不在编译时枚举次数。

这里的 unsigned 自增按机器语义回绕；显式 signed cast 只用于头部和 guard。源循环比较的两个 signed word view 相等当且仅当底层 word 相等。候选在接受路径保持 `0 ≤ (int)i ≤ (int)n`，每次活动自增后仍在 signed 范围。这里保留数据运算的回绕，例如 body 可为 `*out = *out + i + 1U`。

[实际选择器](../prototype/interface/ClightEqualityCompiler.v) 从源提出 iterator、bound 和 body，再核对完整 AST，包括 cast、类型、单位 unsigned 自增以及两个标识不同。`memory_body body = true` 要求 body 是有限的普通内存语句／条件／序列，不改变 temps。改变 `n`、步长 2、volatile 写入等源不被本规则改写。源与候选保留相同 body，框架不提供 body 变换算法。

## 使用者的证明

[ClightEqualityLoop.v](../prototype/interface/ClightEqualityLoop.v) 提供域 `equality_domain`：入口的 iterator 和 bound 都是 `Vint`。它来自实际源第一次头部求值，不能仅由函数声明推定任意 Clight temp_env 都有合法类型。这个域不假定 guard 成立、不假定上界为正，也不假定迭代期间没有 unsigned 回绕。

同一模块将两项标量测试注册为有证书的 Boolean 原子，并经 `synthesize_decision_tree` 产生实际 guard。`equality_condition` 证明检查在域下安全、可用、不变更入口状态，并且接受建立 `i=0 ∧ 0<(int)n`。失败只表示本规则拒绝，不能反推出源不终止或一定回绕。

`equality_loop_forward` 用 [generic_active_condition_transport](../prototype/interface/ClightCounterCondition.v) 逐次运输实际 `exec_stmt`：

1. 头部不变式是固定 `n` 和 `0≤(int)i≤(int)n`，在该区间 `i != n` 与 `i < n` 一致。
2. body 的 temps 写界为空，因此实际内存执行不改变 `i` 或 `n`；活动头部另建立底层 word 不同。
3. 自增消费实际执行，利用活动不等式和机器 signed 范围证明下一头部仍满足不变式。
4. loop stop／increment／recursive execution 的运输保持原 trace、完整内存、全部 temps 和控制 outcome。

规则通过 `readonly_forward_loop_rule` 复用已有源完成性／候选确定性设施，得到条件性局部等价；这里没有新私有 temp，不需要单独的投影出口。它随后进入原始出口宿主；统一 pass 通过已有精确规则嵌入复用 projected host。

## 原循环进展为什么不能依赖 guard

宏片段宿主需要源进展。若只在 `n>0` 的优化前提下证明它，unsigned 回绕等回退路径就缺少全局证明。

[ClightCounterProgress.v](../prototype/interface/ClightCounterProgress.v) 因此新增可实例化的 Clight 计数器协议。它保留实际源小步、body cursor、continuation 和完成执行的桥接；计数器事实由语言实例提供：活动谓词、自然数排名、更新、活动时排名为正、更新恰减少一、实际自增求值和标量纯性。框架不内置“计数器在整数上单调增长”这个假设。这个模块属于 Clight 宿主基础设施；语言无关 `GuardedRewrite` 核没有增加整数或 Clight 语义依赖。

[ClightCircularCounter.v](../prototype/interface/ClightCircularCounter.v) 为本例实例化：

```text
remaining(i,n) = (unsigned(n) - unsigned(i)) mod 2^32
```

代码使用两个区间分支表示该距离，并证明相同数学性质。活动时 `i≠n`，排名严格正；unsigned 加一后恰减少一，包含 `UINT_MAX→0`。因为 body 不改 temps，固定上界下的单位步长源在所有有定义的路径上不能无限运行。错误内存操作可能停滞；进展证书不把它变成有效程序。

因此，这个 source progress 不依赖 guard、不依赖 signed 单调性或 no-wrap。`unsigned_equality_progress`、选择器支持性和完整编译定理真正消费这项协议。它不能证明 step=2 且目标不可达的源终止，也不能处理随 body 修改的目标。

## 完整程序和执行证据

`compile_equality_loops_correct` 证明 `compile_equality_loops p = OK target` 时，`Csem.semantics p` 到 `Asm.semantics target` 的 backward simulation。它不是一个新的完整 Clight 双向行为等价定理。统一 pass 的 `compile_common_rewrites_correct` 也消费这个规则及其源进展分类。

复现方式：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-equality-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-common-native
```

独立入口和统一 pass 各通过 703 次 C 调用／703 行输出；完整编译接口 164 个端点的审计无新增全局公理。Clight 核对六个函数中的七处实际 guard／候选／源回退，包括同一函数的两次 rewrite。fixture 覆盖正区间、非零起点回退、短 unsigned 回绕、signed view 跨边界、空循环 null 输出、两次改写间修改上界、RMW 数据回绕、goto 与外围循环。无限外围和不受支持的潜在无限源只编译及检查，不运行。

这个实例补上真实等式退出的局部／全局链条，尚未组合它与二维调度或稳定 memory bound。一般 stride／动态目标以及选中片段本身可能发散时的逐步模拟宿主仍是后续工作。十三种提取编译器配置已在当前审计下重建并全部通过原生回归；与前阶段 `3f3f955` 比较，15 份既有程序的源码／生成 Clight 摘要全部保持相同。没有性能测量。

后续 [逐步头部阶段](clight-stepwise-head-case.md) 将统一入口升级为两阶段 pass；本例的独立入口保持整段版本化，统一入口还在它的 `!=` fallback 中生成逐头部 guard。两个入口仍各通过相同 703 次调用；脚本分别检查实际结构。当前总审计为 180 个端点、十四种提取配置，本页的 164／十三种记录属于 `3324a6b` 阶段。
