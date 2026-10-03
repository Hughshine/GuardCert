# 一般仿射内层边界的完整程序接入

统一入口已接入带稳定参数的有符号仿射内层上界。源表达式、参数读取、数学域、检查树、真实数组执行、候选执行和公开变量出口均有具体 Rocq 证明。入口仍是 `GuardMemoryUnifiedCompiler.compile_memory_unified_regions`，其正确性定理仍为 `compile_memory_unified_regions_correct`。

例如，两个实际数组 `A[200]`、`B[200]` 上的这个源片段可以提交交换、分裂、平移、剪切的调度，或二维分块：

```c
for (; i < N; ++i) {
    K = 2*i + M - P;
    for (j = 0; j < K; ++j)
        B[i*20+j] = A[i*20+j];
}
```

源 AST 的识别仍有范围限制。外层和内层使用标准递增计数循环，内层从零开始；循环体沿用具体的纯写、原地更新、行首读取、跨数组同单元读取及复制形式。数组仍共享固定布局。上界表达式可以由有符号 I32 临时变量、整数常量、加减和两种顺序的常量乘法组成。它可以读取外层边界变量，且参数数量不限于两个。表达式不能读取内层计数器或它正在定义的边界临时变量。非线性乘法和不匹配的类型或 cast 均拒绝识别。

## 条件如何生成

`memory_source_context` 从实际表达式的读取构造无重复参数环境，将外层边界放在首位。`memory_source_loop_expression_value` 证明编码的 Loop 表达式与源数学表达式一致；源代码求值证明保留 CompCert `Int.repr` 的机器含义。读取乘零的临时变量也纳入实际源读取证明。

仿射上界可写为 `B(i)=B(0)+slope*i`。`memory_source_affine_row_extrema` 证明检查两个端点足以约束整个行区间。上述例子的快路条件包括：

```text
i = 0
1 ≤ N ≤ 10
-20 ≤ M ≤ 20, -20 ≤ P ≤ 20
1 ≤ M-P ≤ 20
0 ≤ 2*(N-1)+M-P ≤ 20
实际数组对象的基址互异
```

这些是数学条件。实际检查树还要通过已有机器算术 lowering 的检查，证明每个中间运算可安全执行。候选代码生成同样检查辅助变量和中间算术。检查树依次处理外层头、稳定参数范围、边界端点和数组对象比较。`memory_parametric_named_source_domain` 从原片段的一次有效执行推出该检查树所需的事实，避免在零次外层执行时提前读取边界表达式或数组。

参数区间目前按布局保守生成：外层边界为 `[1, outer_limit]`，其他参数为 `[-stride, stride]`。因此，有效源输入也可能回退，例如 `M=100,P=99`。首行必须非空，用于从真实首个点执行建立数组登记表和比较所需的有效地址；后续行可以为空，但不能有负上界。算法保证条件成立时正确，不保证为所有可变换输入找出条件。

## 候选与完整程序证明

`checked_named_parametric_candidate` 将参数范围和边界条件同时加入源、候选的真实 Loop，再复用实际提取、整数域对应和内存依赖验证。参数前缀由具体环境长度确定。调度生成仍运行实际 CodeGen，保留源指令、域和访问；生成结果再次独立检查。

二维分块候选覆盖布局矩形，并以源仿射上界筛掉域外点。`checked_named_parametric_tiling_correct` 消费真实点空间和调度证书。`memory_parametric_tile_trimming` 证明以向上取整块数替代宽松块数的执行等价。

`memory_parametric_array_candidate_local` 将实际 Clight 源执行、具体数组登记表、NonAlias、已验证候选 Loop 和已检查的 Clight 后端接在一起。结束时按最后一行的源表达式恢复 `K` 和 `j`，再恢复 `i=N`，保留所有公开参数和精确 `Mem`。`memory_parametric_array_candidate_rule` 是完整程序宿主实际消费的规则，不留下未实例化的源或指令语义字段。

## 运行

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make native-memory-parametric
```

三参数环境下，调度点坐标为 `[P;M;N;i;j]`。例如交换：

```text
(schedule ((affine (0 0 0 0 1) 0)
           (affine (0 0 0 1 0) 0)
           ordinal)
          ((swap 0)))
```

测试输入为 `examples/native_memory_parametric.c`，独立模型与编译执行脚本为 `scripts/native_memory_parametric.py`。结果保存于 `build/native-memory-parametric/report.json`。每组检查完整数组内容、公开 `i/j/K`、参数和外围上下文；GCC 参考与独立模型共有 4,378 行输出。错误域映射、错误维数、过大系数、证书故障和资源耗尽也在测试范围内。

提交 `c2bd5dd` 的验证包含主测试十五组配置，每组 4,378 行输出。identity、interchange、fission、shift、skew 和四组二维块大小均接受十个预期函数。非线性边界、无符号 cast、计数器耦合、错误映射、过大系数、错误证书和资源耗尽均保留原片段。缺少语句调度的提案只在静态语句数量匹配时接受。

另一个完整程序 `examples/native_memory_parametric_context.c` 检查一个参数、四个参数、乘零参数读取和重复参数消除。八组配置各比较 2,531 行输出，并覆盖三组块大小和两条故障回退。旧调度回归二十六组及非矩形回归二十一组也通过；新增的 `K=M-i` 已由这条语义路径接受。

该提交的证明审计重新编译 107 个内存适配模块和七个 lowering 模块，完整程序端点仍继承 CompCert 与 validator 的原有 42 项假设并集。实际约束搜索实现不作为正确性前提：不受信任的 Fourier–Motzkin 搜索现在优先利用等式消元，返回的每份证书仍由提取的 LCF 检查。资源耗尽与伪造证书测试使用同一个搜索实现。

这条接入扩大了 C 上界语法，尚未覆盖任意嵌套循环域、一般仿射源访问、不同数组布局的混合操作或指针缓冲区。不同数组间单条复制已由[独立布局实例](memory-different-array-layouts.md)接入。
