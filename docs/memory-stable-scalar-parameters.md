# 稳定 RHS 标量参数

本页记录指针缓冲区及固定数组中的稳定 signed-int RHS 参数路径。源域、参数传递、源和候选的实际 CompCert 执行、依赖验证、guard 和完整程序连接均有具体 Rocq 实现。2026-10-03 的全量审计覆盖 240 个适配模块及七个 lowering 模块：物理登记表没有全局公理，指令继承七项、验证器继承原有 12 项，完整编译器继承原有 CompCert／验证器并集 42 项；没有新增公理。本次正式原生配置见下文。

## 源与使用方式

```c
void axpy(int *buf, int n, int m, int alpha, int beta) {
  int i = 0, j;
  for (; i < n; ++i)
    for (j = 0; j < m; ++j)
      buf[8*i+j] = buf[8*i+j]*alpha + beta + i*j + 7;
}
```

选择外部候选并编译完整 C 程序：

```sh
printf '(tile 2 3)\n' > /tmp/guard-scalar-candidate.sexp
GUARDCERT_LOOP_CANDIDATE=/tmp/guard-scalar-candidate.sexp \
  build/compcert-memory-unified/ccomp \
  -conf build/compcert-memory-unified/compcert.ini \
  -stdlib build/compcert-memory-unified/runtime \
  -S examples/native_memory_scalar.c -o /tmp/guard-scalar.s
```

候选可以是完整 Loop、索引映射、分块或仿射调度。普通 N 参数循环模板由不受信任的辅助生成器补上稳定标量实参，随后完整候选再次独立验证；已经提供 N+E 实参的候选按所提供的实参验证。补参本身不获得等价保证。

调度输入新增 `(coordinate axis)`，例如：

```lisp
(schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0)))
```

这个辅助语法根据解码指令的坐标和标量参数布局提出系数行。它属于不受信任的原生提案代码；生成结果必须通过相同验证器。显式 `(affine (...) bias)` 行仍按用户提供的系数解释。

## 参数与证明

源 Loop 的上下文为次数参数 `N` 项，随后稳定标量 `E` 项。循环叶的环境为反序坐标、次数、标量；实际指令的实参为原序坐标、标量。循环域只读取次数前缀。验证器和机器 lowering 对标量使用完整 `Int.min_signed .. Int.max_signed` 区间；数据表达式保留 `Int.add/sub/mul`，不把乘法或加法改成无界整数运算。

`GuardMemorySourceParameters.memory_source_parameter_inverse` 从实际 RHS 返回整数推出被使用的参数操作数也返回整数。`memory_scalar_pointer_sequence_used_register` 将后续赋值使用的标量类型信息沿只写内存、不修改临时变量的指令列表传回叶入口。`memory_scalar_pointer_source_first_capability` 再沿实际源循环的首次叶执行传回区域入口。这里的前提是原片段实际成功执行；完整编译器由源执行推导这些事实，没有要求调用者预先提供额外的标量类型公理。

guard 保持次数上界、正次数和初始外层计数器检查，不读取指针或标量。零次循环中的未初始化 `alpha` 无需被求值。正次数快路中的标量由上述实际源执行引理获得类型信息，并由 frame 保持到候选中。稳定标量可以同时是一个次数变量：上下文中的两个位置具有相同实际值。

`GuardMemoryInstructionPadding` 将访问矩阵补为 N+E 列，增加的 E 列均为零，并证明补列保持所有实参下的单元、指令和列表执行语义。这样，验证器要求的实参维度与访问矩阵维度一致；标量参与计算值，却不改变数组地址。`checked_memory_scalar_candidate_correct` 验证实际 N+E 实参、域对应和依赖保持。`checked_memory_scalar_tiling_correct` 将相同语义扩展到外层两轴分块及有效块数修剪。`memory_scalar_pointer_candidate_rule` 提供生成 guard、执行快路和恢复公开计数器后的局部契约；`check_memory_scalar_pointer_unified_region_sound` 将这条契约接入现有结构化上下文连接。完整端点仍是 `GuardMemoryUnifiedCompiler.compile_memory_unified_regions_correct`，从 Csem 到 Asm。

条件搜索逐个尝试 `[2147483647; 8; 4; 3; 2; 1]`，每次重新检查源语法、访问范围、完整候选、依赖和机器 lowering。通过的次数区间才进入 guard。没有任何范围通过时保留原片段。

直接调度生成只向 CodeGen 提供次数前缀约束。完整标量范围保留在独立验证器中，不作为候选的可执行 guard：其整数多面体形式含 `-alpha <= 2147483648`，这个数学约束不适合直接用 signed-32 运算执行。生成器的结果仍须独立验证，次数约束、标量范围和候选正确性的证明义务没有因此减少。

## 固定数组实例

同一个 Loop／PolyLang 指令 ABI 也用于局部及全局固定数组。数组对象、读取地址和写入地址由实际 Clight AST 解码；标量只作为计算实参，不扩展地址坐标。多个不同数组及同一数组上的多个访问共用现有物理登记表和依赖验证器。

`GuardMemoryScalarArrayCompute` 证明实际赋值与内存指令执行的对应，并从被使用的 RHS 标量操作数推出其整数类型。`GuardMemoryScalarArraySequence` 顺序组合这些事实；`GuardMemoryScalarArrayAnchors` 从真实源的零坐标访问获得实际对象基址和指针比较的安全证据，再用于同一对象上的邻居偏移。`GuardMemoryScalarArrayBody` 和 `GuardMemoryScalarArrayDomain` 将这些叶事实接到递归规范源循环、标量绑定和运行时 guard。这里的前提仍由真实源执行推出，没有要求调用者提供未实例化的内存或标量公理。

`GuardMemoryScalarArrayCandidate.memory_scalar_array_candidate_local` 将验证后的 Loop 降成真实数组读写，恢复公开计数器并保留实际最终内存及可观察临时变量。`GuardMemoryScalarArrayCompiler` 提供外部候选、直接调度和分块服务，`GuardMemoryUnifiedCompiler.check_memory_scalar_array_unified_region_sound` 接入完整程序宿主。两类内存实例共用 `compile_memory_unified_regions_correct` 的 Csem→Asm 端点。

固定数组 guard 在次数及入口计数器检查之后才比较实际对象基址；它不读取 RHS 标量。零次循环中未初始化的标量不会被提前求值。运行入口为 `make native-memory-scalar-array`，包含局部／全局数组、跨数组计算、读取写入依赖、完整输出及分支诊断。

2026-10-03 的正式固定数组测试通过 16 组配置，每组比较 224 次实际调用产生的 672 行完整数组、参数及公开计数器输出。配置包括恒等、交换、逆序、直接调度、分离执行、三组分块、错误标量实参、错误证书及资源耗尽。10 组分支诊断合计 2602 次调用通过；不同轴长度、负数及 signed-32 极值标量实际进入快路，每一维零次循环、未初始化标量及非零起点正确回退。诊断编译的是带计数标记的 Clight 打印结果；完整汇编输出另行独立验证。

对应正式二进制 SHA256 为 `8de8f273f5ea82cfbdcbbac524443eeb40931e161af44e9c821a413d665d74a7`。不加保护的依赖链逆序与分离执行分别使 `b[0]` 从源的 `159` 变为 `168746` 与 `1470`；验证后，两种配置的链只接受共同次数上界 1，`n=1,m=3` 实际进入原片段回退。

## 当前边界

这两路支持一个稳定指针缓冲区或多个实际固定数组、任意有限数目的实际使用的稳定 signed-int RHS 临时变量、规范矩形 counted loop、已检查的非负仿射地址和有限 `Sassign` 列表。固定数组实例要求每个对象具有源实际访问覆盖的零地址证据。原生辅助计数器池仍决定可实际接受的循环深度。指针逻辑窗口为 1024 个单元，不是预设的实际分配长度。循环体修改标量、非仿射地址及多个不同指针变量仍安全回退；更一般的深层源域、负系数源地址及多指针重叠条件继续推进。

测试入口为 `make native-memory-scalar`。它检查完整汇编输出和公开计数器，使用 GCC `-fwrapv` 与独立 32 位模型比较；单独的分支诊断执行带计数标记的 Clight 打印结果，观察快路、回退和零次循环。后者是运行诊断，不作为汇编语义证明。

## 指针测试及已有路径回归

指针标量测试通过 16 组正式配置，每组比较 195 次调用与一元素分配案例产生的 196 行完整缓冲区、参数及计数器输出。10 组分支诊断共 2626 次调用通过，包括不同轴长度、任意正基址偏移、极值标量、空指针零次循环及未初始化 RHS 标量。错误的标量实参候选、错误证书与资源耗尽均保留源执行。

深层循环在同一二进制上通过 17 组完整配置，每组 2250 行输出；11 组分支回归共 560 次调用通过，新增不同轴长度诊断。四至八维实际接受、九维及辅助计数器资源不足回退均保持完整源输出。

旧指针测试在相同二进制上通过 15 组完整配置，每组 227 行输出；10 组分支回归共 586 次调用通过。其调度测试使用 `(coordinate axis)` 来适配被接受的标量来源；显式仿射系数的解释保持不变。

| 路径 | 完整配置 | 每配置输出行 | 分支配置 | 分支调用 |
| --- | ---: | ---: | ---: | ---: |
| 稳定指针 RHS 标量 | 16 | 196 | 10 | 2626 |
| 固定数组 RHS 标量 | 16 | 672 | 10 | 2602 |
| 旧指针路径回归 | 15 | 227 | 10 | 586 |
| 深层循环路径回归 | 17 | 2250 | 11 | 560 |

完整输出来自提取编译器生成的汇编；独立模型与 GCC `-fwrapv` 给出相同结果。分支计数来自带标记的 Clight 打印结果，未将这项诊断扩大为额外的汇编证明。所有结果对应上述 SHA256 和 `build/guard-memory-proof-report.json`；测试报告位于 `build/native-memory-scalar/`、`build/native-memory-scalar-array/` 、`build/native-memory-pointer/` 与 `build/native-memory-recursive/`。

本页的完整测试快照对应标量提交 `2ccb7c0`。后续 [signed 仿射源地址](memory-signed-affine-access.md) 已扩展正、负及混合系数访问，另有其正式审计、完整测试及共享路径回归记录。
