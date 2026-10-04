# 固定地址参数的边界扫描

本阶段把多轴边界扫描推广到实际地址参数。`p[16*i+j+u+32]` 与 `q[16*i+j+v+33]` 的循环坐标系数相同，参数系数及偏移可以不同；本次片段入口的 `u,v` 固定后，只需要在实际坐标维度构造边界。参数不会成为额外扫描轴，也不会枚举参数范围内未使用的值。

## 条件与接口

输入继续使用 `(per-axis …)` 候选入口。源 package、逐轴次数 cap、地址参数 cap、RHS signed32 范围及候选证书保持同一接口。新的选择发生在访问对的检查代码生成中：比较 `resize d coefficients`，其中 `d` 是当前片段的坐标轴数。相同前缀使用边界扫描，不同前缀使用原来的完整扫描。参数后缀无需相同。

例如 `p[2*i+u+32]` 与 `q[3*i+v+33]` 仍采用完整扫描。对于二维源的内层片段，外层 `i` 是固定参数，比较的前缀只有内层坐标 `j` 的系数；这一选择必须按片段的实际维数进行。

`GuardMemoryParamBoundaryMath.memory_param_boundary_specialize` 将当前参数值代入仿射项。`memory_param_boundary_specialize_value` 证明其坐标值等于原项在 `coordinates++parameters` 上的值。`memory_param_boundary_overlap` 使用真实机器指针偏移的模运算，证明相同坐标系数的重叠有坐标边界见证；不要求参数后缀系数相同。

`GuardMemoryParamBoundaryCells.memory_param_axis_boundary_pair_exact` 在正常源访问提供的有效性、对齐及物理能力下，证明边界布尔检查等于原来的固定参数完整布尔检查。该定理和参数代入的数学端点没有全局公理。这里的源能力前提仍是定理参数，不能省略或视为分配长度假设。

`GuardMemoryParamBoundaryTest`、`Scan`、`Masks`、`Pair` 把等式接到实际 Clight 执行。每个 mask 只选择坐标；实际参数寄存器保留为固定后缀，私有零寄存器处理重复边界坐标。查询安全来自原源片段本次活动访问，检查保持参数、公共 temporary 和内存。`GuardMemoryParamAxisPairChoice.memory_param_affine_axis_pair_choice_execution` 根据坐标前缀相等与否选择这条路线或完整扫描；其结果仍是已有完整检查的布尔值。`GuardMemoryParamAxisScan` 随后组合全部原始访问对，复用已有 NonAlias、候选规则和统一完整程序端点。

## 检查成本与限制

设当前片段有 `d` 个坐标轴和 `P` 个活动点。每个相同坐标前缀的跨指针原始访问对执行 `2^d P` 次查询；不同前缀执行 `P²` 次。参数数量不进入 mask 数。所有 mask 都会执行，包括重复角点；原始访问对也保留重复和只读别名的保守检查。

这个变化保证条件等价，不保证查询次数对每个输入都减少。`P<2^d` 时边界扫描可能更贵。没有加入去重、提前退出或按运行成本选择策略，也不宣称最弱条件、运行时间提升或接受范围扩大。各个参数／次数 profile 仍只选第一个静态验证通过的组合。

## 验证进度

新增七个模块及统一 Csem→Asm 依赖已编译通过。2026-10-03（本地日期）的全量审计重编译 367 个适配模块、七个 lowering 模块和两个核心模块，516 个证明源码哈希一致；抽象核心及条件策略数学端点没有全局公理，指令桥／validator／完整编译器分别精确保持原有 7／12／42 项假设。测试源现有八个核、637 次调用，SHA-256 为 `651feed91d241915346445729b6238285ae7e85c75e519fd033d2890ed464ad0`；新增不同坐标系数的访问核。独立机器整数模型与 GCC 完整缓冲区及公共游标比较通过。

历史版本 `1b6e3fd` 的已审计编译器（SHA-256 `071573d37a616b08c8975daf06d76a24b3b2333b125c93ee78519a0a8abcf930`）已对这份同一源完成 13 组配置、8281 次完整汇编调用，全部一致。它的分支诊断有 4288 次函数调用、1336 次至少进入候选、3840 次接受的片段入口及 1128338 次地址比较。该基线使用 `/tmp/guard-address-parameters-verified/ccomp`，报告为 `build/native-memory-address-parameters/before-report.json` 和 `before-branch-report.json`。

新编译器已构建，SHA-256 为 `0b170f63acb217171e908e5a976b1fadd9b22badf6281aabbe0c91216daefae9`，516 个证明源码哈希匹配。同一源的 13 组配置、8281 次完整 CompCert 汇编调用全部通过；包括直接候选、交换、源序／交换／fission 调度、两种二维块大小，以及无效坐标、资源限制和错误证书的拒绝。完整缓冲区和公共游标均与 GCC 和独立机器整数模型一致。

`scripts/compare_memory_address_parameter_scans.py` 的逐项比较通过：源哈希、片段选择、次数 cap、参数 cap、逐入口参数及实际接受／回退结果都相同。4288 次函数调用中有 1336 次至少接受一个片段、2952 次没有接受；按实际片段入口计算，有 3840 次接受和 9131 次回退。49 个入口的地址参数未定义，全部在参数范围检查及地址查询前回退；诊断将这些参数标记为未定义，不用测试输入数值代替实际寄存器值。

实际地址查询为 `1,128,338 → 231,952`。1095 次函数调用的查询减少，385 次增加，2808 次相同。不同坐标前缀的 `param_different1` 保留完整扫描：69 次调用共 11164 次查询，前后一致。具体样例：

| 输入与配置 | 前后接受 | 旧查询 | 新查询 |
| --- | --- | ---: | ---: |
| 一维源序，`param_linear1(n=32,u=3,v=7)`，两个不同数组 | 均接受 | 2048 | 128 |
| 一维源序，`param_different1(n=32,u=3,v=7)`，两个不同数组 | 均接受 | 2048 | 2048 |
| 二维源序，`param_copy2(n=1,m=1,u=3,v=7)`，两个不同数组 | 均接受 | 2 | 8 |

这些数字来自 GCC 执行带标记的 Clight，独立于完整汇编执行。直接二维配置的 Clight 文本为 `78,086 → 99,794` 字节，汇编文本为 `207,184 → 230,341` 字节；不作为机器代码大小或运行时间。

同一个新编译器的五套普通入口回归完成 12922 次完整汇编调用及 10321 次分支诊断。逐轴入口完成 6230 次完整汇编调用及 3599 次分支诊断；与 `1b6e3fd` 的同一源、片段和范围逐项对照通过，保持 1280 次函数至少接受一个片段，查询 `10,751,100 → 6,771,600`，减少来自参数化内层片段。既有同／异系数选择的 14 次查询计数诊断也通过。全部新报告绑定同一 `0b170f63…` 编译器。

复现当前完整程序及分支检查使用 `make native-memory-address-parameters`。前后成本实验先用已审计历史编译器运行 `scripts/native_memory_address_parameters.py --previous-compiler /path/to/ccomp` 及 `scripts/native_memory_address_parameters_paths.py --previous`，再运行当前完整测试和 `scripts/compare_memory_address_parameter_scans.py --baseline /path/to/snapshot`。两个编译器必须使用同一测试源；比较器要求历史快照具有与编译器哈希一致的 `.guard-build.json`。
