# 不同数组布局的完整程序复制变换

本次接入复用统一入口的域检查、依赖验证、共享 guard、内存后端和完整 Csem→Asm 定理。新增的语言实例分别解释源读、写的数组类型、步长和物理地址，不将二者视作同一布局。

例如，在数组和计数器已初始化的上下文中：

```c
int A[220], B[170];
for (; i < N; ++i) {
    K = 2*i + M - P;
    for (j = 0; j < K; ++j)
        B[i*17+j] = A[i*22+j];
}
```

读地址为 `4*(22*i+j)`，写地址为 `4*(17*i+j)`。`memory_layout_copy_statement_inverse` 将真实 CompCert 赋值解码为这两个物理地址上的 load/store；`memory_layout_copy_registry_execution` 证明它与携带独立访问函数的内存指令对应。候选 lowering 也消费各自的数组 descriptor，因此生成代码保留两个布局。

## 前提与证明接口

`memory_common_layout` 取两个布局的最小完整行数和最小步长，供当前保守 guard 使用。上述例子的外层范围是 `1≤N≤10`，行宽不超过 17；实际读、写仍使用 22 和 17。这避免将共同可访问域混同于数组实际地址映射。源输入即使在共同域外仍有效，也可以回退。

源上界沿用有符号仿射表达式和任意数量的稳定参数，先证明 eager reads 和机器编码，再合成行区间端点检查。首行必须非空，随后每一行的宽度可以为零。真实源的第一个点执行提供两个对象的绑定及比较所需的有效地址；不假设任意内存上的数组基址有效。数组关系由安全的运行时比较和已有物理 NonAlias 定理连接。

`memory_layout_copy_source_decode` 证明真实 C 源到参数化 Loop 的执行及公开出口。`memory_layout_copy_source_domain` 证明短路 guard 的求值安全。`memory_layout_copy_candidate_rule` 将源对应、已验证候选、机器 lowering 和出口修复装入完整程序宿主实际消费的规则。源 AST、完整数组类型和循环控制由 `memory_layout_copy_certificate` 核对。

`checked_parametric_instruction_candidate` 和 `checked_parametric_instruction_tiling` 接收内存指令列表及数组名称，不要求具体的操作枚举或统一布局。其证明复用一般点对应、域等价和依赖证书检查。当前不同布局源实例只暴露一条复制指令；这些一般 checker 接口不等于任意 C 语句列表已经识别。

## 运行与范围

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make native-memory-layout-copy
```

`examples/native_memory_layout_copy.c` 包含不同长度、不同步长、相同长度但不同步长、全局数组和外围重复循环。独立模型与 GCC 核对 4,378 行完整输出，包括整数极值复制、零次执行、负边界和范围检查回退。提取编译器的结果记录在 `build/native-memory-layout-copy/report.json`。

本阶段的完整 Rocq 审计通过：118 个适配模块和 7 个 lowering 模块，假设并集仍为 42 项原有假设。14 组不同布局完整程序配置全部通过，五种仿射候选和四种分块配置各接受六个支持的函数；错误映射、维度、系数、资源限制和无效证书走回退。测试同时检查生成的快分支保留两个实际步长。使用同一编译器运行的参数化源 15 组配置和完整程序上下文 8 组配置也全部通过。

这条源实例支持两个名称不同的有符号整数数组间的一条复制和已支持的仿射内层上界。普通同布局操作列表仍走原入口。不同布局的任意混合语句列表、邻居或更广仿射访问、同一对象的布局重映射、指针参数和切片尚未由此证明。
