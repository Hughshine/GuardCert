# 实际内存循环上界：非循环论证的 guarded 提升

2026-10-05。这个实例补上 [Optimistic Loop Optimization](https://compilers.cs.uni-saarland.de/papers/doerfert_cgo17.pdf) §4.1 的一类需求：被当作循环参数的值来自普通内存读取，源 body 又可能写到同一地址。它消费新只读条件、局部不变式、私有出口及完整程序编译接口。

## 源、候选和检查

使用者 pass 核对实际 Clight 中的源：

```c
for (; i < *bound; ++i)
  *out = i + 1;
```

候选使用目标函数声明的新鲜 temp：

```c
private_bound = *bound;
for (; i < private_bound; ++i)
  *out = i + 1;
```

实际检查先测试 `i==0`，再测试 `i<*bound`，最后测试 `out==bound`。仅在活动且指针不同的路径进入候选；其他路径执行原循环。检查可以读取普通内存，但保持整个入口 temps／memory，并且没有事件。它不会读取 CompCert 权限、block 编号或数学足迹。

`out`、`bound` 都指向 signed Mint32 单元。`bound` 只需可读。两个有效且四字节对齐的不同单元足以建立本例的 non-alias；这包括同一 block 的分离单元，不能直接推广为一般数组区间分离。

此处初值为零只是保守的选择条件。源协议、局部执行运输和候选循环次数都不枚举运行时上界。

## 域、稳定性和进展分别来自哪里

源循环每次到达头部都读取 `*bound`，即使 body 为空也如此。`loaded_bound_domain_from_source` 用实际源头部的求值，导出 iterator 的机器整数、bound 的 typed pointer 及返回整数的真实 `Mem.loadv`。只有活动路径才用第一次实际 store 导出输出指针的访问能力。因此空路径可使用 null 输出指针；null bound 不属于这个源的定义行为。

这个入口域没有假定上界稳定。接受 non-alias 前提后，`loaded_bound_body_preserves` 才利用实际 `Mem.storev` 和既有 `mint32_load_survives_apart_store`，证明每个执行前缀保留参数读取值。指针 temps、私有 cache 和其他公开 temps 的写界分别由实际语句证书运输。

源循环的进展也不依赖上界稳定。[ClightStrictLoopProgress.v](../prototype/interface/ClightStrictLoopProgress.v) 提供一个 Clight 语言设施：使用者为实际测试证明“接受蕴含 signed counter 小于 `Int.max_signed`”；body 必须是有限且只写内存的普通语句。宿主用 `Int.max_signed - Int.signed(i)` 和语句游标作为良基度量。上界可以在每次 body 后改变；每次允许递增仍不会回绕。这里的度量是证明对象，不是生成的扫描代码。

这个协议允许未定义访问卡住，证明的是区域不会产生无限内部步；完整编译定理由 CompCert 的源定义行为与宿主连接处理。它没有覆盖 `i!=*bound`、非严格比较或其他可能无限执行的被选择循环。

## 使用者提供的局部证明

[ClightStableLoopCondition.v](../prototype/interface/ClightStableLoopCondition.v) 的 `strict_loop_condition_transport` 消费实际源循环执行、每个头部的测试运输、每个实际 body 后的不变式，以及实际增量后不变式。它重建候选的真实 `exec_stmt`，保留 trace、outcome、完整内存及出口；不是仅证明两个数学次数相等。

本例将这个不变式实例化为：参数指针保持、实际 parameter load 仍等于入口 word、cache 等于该 word，以及输出单元分离。`loaded_bound_loop_cached` 替换每一次实际源头部。`loaded_bound_forward` 再加入候选 preload 和私有 temp，保留所有原程序 temps／完整内存，允许私有出口不同。

[ClightReadonlyLoadedTreeSynthesis.v](../prototype/interface/ClightReadonlyLoadedTreeSynthesis.v) 让 tree-valued 原子检查使用普通 load。使用者必须在入口域下证明 validity／value 树完成、结果可靠；Clight 表达式确定性将完成路径提升为所有可达节点的安全。Boolean 合成核照常处理组合和 unknown；本例的保守原子在不接受时返回 unknown，因此否定不会将失败路径变成接受。当前 guard 仍是有限树，不支持带私有赋值的扫描检查。

[ClightLoadedBoundCompiler.v](../prototype/interface/ClightLoadedBoundCompiler.v) 给出使用者选择器、完整源／body AST 核对和有证书规则。规则通过 `readonly_projected_forward_loop_rule` 的源完成性、候选确定性及观察运输建立条件性局部等价。

## 完整程序和验收边界

`compile_loaded_bounds_correct` 的端点是 Csem→Asm backward simulation。实际投影 Clight forward simulation 负责 fresh pool、目标 temp 声明、源入口、外围语句和 continuation；它保护所有原程序 temps，没有使用自动 liveness 来隐藏已有变量。局部实例不声称完整 Clight 双向行为等价。

复现目标是：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-loaded-bound-native
```

验收使用提取编译器处理 C fixture，再核对 Clight 中的实际 guard、候选 cache 循环头及原始内存循环头回退；原生输出与 GCC 和独立逐次内存模型比较。外围无限循环只编译及检查内部改写，不执行。

实际验收通过 514 次调用／514 行输出：252 个别名输入、252 个同 block 分离输入、三个空路径 null 输出调用、四个 readonly bound 调用和三个 signed 极值回退。四处实际 guard／cache 循环头已确认；volatile bound、不同 body、不同增量和非严格比较被拒绝。当前十一组原生实例在同一 119 端点审计下重建并通过，报告绑定源码、编译器、Clight 和汇编摘要。

别名反例为 `i=0,*bound=5,out=bound`。源第一次写入 1，下一次头部拒绝，最终 iterator 和输出都是 1；省略 guard 的缓存候选两者都会为 5。这是必须保留的源行为，不能将“bound 不变”放进入口域而排除该输入。

这个阶段处理一个内存上界和 singleton 写集，尚未将内存边界与多维调度、参数 stride 或一般动态数组足迹组合起来；这些仍是主线验收项，没有性能测量。
