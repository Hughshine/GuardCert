这条路线把实际 Clight 仿射循环中的多指针变换接入统一的完整程序编译器。`AffineNestUnifiedCompiler.compile_guardcert` 同时保留单指针、矩形循环和条件标量 rewrite 服务；源描述器与候选算法都不受信任。

例如源片段可以是：

```c
for (; i < n; i++) {
  K = i + m;
  for (j = 0; j < K; j++)
    a[512*i + 32*j] = b[512*i + 32*j] + alpha + i - j;
}
```

候选算法提议交换循环顺序，或在保留源域约束的包围盒上分块。源检查器从实际语法提取数组访问、仿射域与稳定参数。区间策略提议控制和地址范围；检查器验证这些范围足以建立数学循环域。依赖验证器检查候选在该域上的对应及执行顺序。运行时守卫检查当前入口落在这些区间内，并检查不同指针的实际访问地址分离。

同一底层数组的两个指针也可能通过检查：只有各自实际访问的单元必须分离。三角域包围盒里未访问的位置不参与扫描，不要求这些位置有有效权限。不同指针的实际访问发生重叠时，守卫拒绝并执行原片段。同一指针内部的依赖则由依赖验证器处理，地址分离守卫不会替它背书。

证明与使用接口如下：

| 接口或定理 | 含义 |
| --- | --- |
| `affine_source_proposer` | 从实际源、公开变量和私有分配池提议源描述；只返回数据 |
| `affine_candidate_request` / `affine_candidate_proposer` | 接收已检查的源 IR、上下文、区间和指针，提议候选 IR 与重索引或分块描述 |
| `check_affine_multi_static_package` | 检查源对应、稳定指针、区间、公开变量和两套私有扫描名字 |
| `affine_reserve_multi_scans` | 数据提议器的包装器，预留两套扫描控制变量和一个结果变量 |
| `affine_scan_all_execution` | 实际 Clight 扫描安全结束，保留内存和公开变量，并精确编码逐对地址检查 |
| `affine_package_scan_capabilities` | 从源的正常执行推出所有实际扫描地址的权限 |
| `affine_multi_guard_nonalias` | 守卫接受推出实际源足迹上的 `NonAlias` |
| `affine_multi_candidate_local` | 接受时，实际候选执行产生同一最终内存和公开变量值 |
| `affine_multi_guarded_region_sound` | 守卫、候选及原片段回退满足通用片段替换契约 |
| `check_affine_multi_region_sound` | 实际检查器每个接受结果都满足该契约 |
| `compile_guardcert_correct` | 所有源与候选提议器均量化为不受信任输入的 Csem→Asm 后向仿真 |

`affine_multi_guard_flag` 是语义模型中的布尔前提：数值条件与源域上的跨指针地址分离。`affine_multi_guard_code` 是实际 Clight 条件程序，包含私有循环及结果变量。条件可以是程序，而不必压成一个无循环的 C 表达式。整数检查拒绝时不运行地址扫描；源路径尚未定义的深层参数也不会被提前无条件读取。

候选执行之后重放纯源控制，以恢复原来的公开 `i,j,k,K,L`。即使源最后一轮子循环为空，也不能直接把候选的循环出口值当成源出口值。

在仓库 Rocq 环境中运行：

```sh
make affine-nest-prototype-proof
make guardcert-compiler
make native-affine-nest-multiple-pointers
make native-guardcert
```

证明审计编译 96 个原型模块；新增扫描及局部证明保持既有六项源语义假设，检查器保持既有十四项假设，统一完整程序定理保持既有四十二项假设。提取、真实汇编执行与 Clight 分支插桩分别记录证据。运行报告位于 `build/native-affine-nest-multiple-pointers/`；插桩报告不能替代汇编执行或证明。

六组实际汇编配置各运行 570 次完整程序调用，共 3,420 次，逐单元比较三个数组和所有公开控制变量。它们包含关闭、identity、交换、分块、错误分块描述和 oracle 资源限制。identity 接受所有五个源函数；交换与分块拒绝有真实同指针依赖的函数。其余安全函数均安装守卫。错误描述和资源限制均不安装候选。

独立 Clight 插桩共运行 1,484 次：222 次候选、1,262 次回退。其中 130 次同数组但实际访问分离的调用走候选，238 次数值检查成立但实际访问重叠的调用回退。54 次未定义深层 bound 参数和 84 次未定义 leaf 参数的用例均要求并观察到零守卫读取。插桩只提供测试路径证据，由 GCC 执行，不计入实际 CompCert 汇编调用。

目前源片段限于已检查的顺序仿射循环和非 volatile 的 int32 数组操作。区间条件保守，不是最弱条件。扫描逐对比较访问，成本是二次的；控制重放也有成本。这里只建立功能和行为保持，不给出加速结论。编译器的默认私有池有 32 个 int32 变量；空间不足会拒绝该变换，完整程序定理本身允许调用者选择更大的私有池。
