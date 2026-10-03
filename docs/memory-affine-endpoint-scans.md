# 仿射访问的端点扫描

这是对[一般一维仿射地址扫描](memory-affine-alias-scans.md)的检查算法改进。候选变换仍须取得独立的调度依赖证书；减少 alias 检查不能消除 write-after-write 依赖。当前实现对每一对不同逻辑指针的访问分别选择算法，没有改变候选消费的 NonAlias 性质。

## 适用条件与证明

设两个访问的机器地址偏移分别为

```
A(i) = (base_A + 4 * (slope_A * i + bias_A)) mod modulus
B(j) = (base_B + 4 * (slope_B * j + bias_B)) mod modulus
```

活动下标均为 `0 <= i,j < n`。当两个 slope 相等时，任意相等地址 `A(i)=B(j)` 都可以通过减去同一个 `4*slope*min(i,j)`，得到 `A(0)=B(j-i)` 或 `A(i-j)=B(0)`。因此，单层循环检查 `A(0)!=B(k)` 与 `A(k)!=B(0)` 足以建立所有访问对的分离。

这个推导在取模偏移上成立，包含负步长和零步长。它没有要求不同 block 可进行大小比较，也没有要求整数地址区间不重叠。不同 block 使用 CompCert 实际有效指针的不等比较；同一 block 使用偏移相等的语义。原源访问提供有效性、对齐和实际表达式求值证据。

当任一 slope 为零时，同一个单层检查也覆盖全部访问对。其他情况保留已有双层扫描。`memory_affine_pair_fast` 检查源编码出的系数，实际 Clight 表达式仍由源地址表达式重命名而来；不会把数学表达式求值当作真实机器执行。

证明源：

- [GuardMemoryAffineEndpointMath.v](../adapters/compcert-memory/GuardMemoryAffineEndpointMath.v)：取模平移、重合端点见证和单层检查的数学充分性。
- [GuardMemoryAffineEndpointCells.v](../adapters/compcert-memory/GuardMemoryAffineEndpointCells.v)：实际指针位置、编码系数和完整双层检查之间的对应。
- [GuardMemoryAffineEndpointScan.v](../adapters/compcert-memory/GuardMemoryAffineEndpointScan.v)：实际 Clight 单层循环正常执行，检查结果及公共临时变量保持。
- [GuardMemoryAffinePairChoice.v](../adapters/compcert-memory/GuardMemoryAffinePairChoice.v)：算法选择、接受推出完整检查，以及公共状态运输。

数学充分性与算法选择没有全局公理。实际执行继承既有 Clight 语义假设。统一入口首先尝试一般仿射指针路径，使单位步长也能够使用这个检查；资源超限时继续尝试已有路径。

## 成本及复现

单个有向访问对执行 `2*n` 次地址比较，原双层检查执行 `n*n` 次。本例的两个原始访问构造两个有向对，新检查总计 `4*n`。单位步长旧入口只构造一个双层对，因此旧成本为 `n*n`；一般仿射旧入口构造两个，成本为 `2*n*n`。

复现入口是 `make native-memory-affine-endpoints`。`native_memory_affine_endpoints.py` 执行完整 CompCert 汇编，独立模型与 GCC 源执行核对完整数组和公共计数器。`native_memory_affine_endpoints_paths.py` 对 Clight 打印副本加计数，使用 GCC 记录真实分支和比较次数；这部分不是 CompCert 汇编证据。

例子包括相同正／负步长、同一 block 的交错单元、真正重叠的指针、常量地址依赖、源序与反向候选、空循环以及运行时上界之外的回退。源码是 [native_memory_affine_endpoints.c](../examples/native_memory_affine_endpoints.c)。

2026-10-03 全量审计通过：297 个适配模块、七个 lowering 模块及两个有状态核心模块，共 446 个证明源码哈希一致。端点数学充分性、算法选择的充分性及公共状态运输均没有全局公理；完整编译器仍为既有 CompCert／validator 的 42 项假设并集。

提取编译器 SHA256 为 `3d284035b644c2e25b753b9f5eda865c085d6a2ec6093dff34243c83ecfda7fb`。新例子的七组配置均通过，每组 241 次完整汇编调用，总计 1687 次。四组正向／反向分支诊断共 964 次调用通过；源序配置为 137 次候选、104 次回退，反向配置为 96 次候选、145 次回退。常量地址写入的反向候选只在 cap 1 获准；独立模型给出 cap 33 下反向结果不同的依赖见证。

此前已审计的编译器 `3e7fd197…` 在相同 C 输入上通过 241 次完整汇编调用和 241 次分支诊断。旧报告在 `build/native-memory-affine-endpoints/before-report.json` 与 `before-branch-report.json`，新报告为同目录的 `report.json` 与 `branch-report.json`。源序配置的逐调用比较计数如下，候选／回退选择与旧版一致：

| 调用或整套输入 | 旧版地址比较次数 | 新版地址比较次数 |
| --- | ---: | ---: |
| 相同步长／负步长，n=129 | 33282 | 516 |
| 相同步长／负步长，n=512 | 524288 | 2048 |
| 单位步长，n=512 | 262144 | 2048 |
| 单位步长，n=1024 | 1048576 | 4096 |
| 全部 241 次源序调用 | 30556452 | 159384 |

超出 guard cap 的调用执行零次地址比较并回退。反向配置的 241 次调用各执行 119533 次比较。相同输入的完整源序 Clight／汇编文本为旧版 13338／12557 字节、新版 13167／12686 字节；这不是速度测量。

同一新编译器重跑一般仿射访问的 2696 次完整汇编调用、1366 次分支诊断，以及逐元素循环的 1200 次完整汇编调用、600 次分支诊断，全部通过。多指针、单指针、标量、signed 下标及源上下文元数据的另外 19 组配置均在同一编译器上通过。

## 仍需扩展

不同非零步长仍采用平方扫描。多个访问的有向检查对仍可能重复；所有逻辑对象包括只读对象仍要求分离。当前动态扫描只支持一个活动循环轴；多轴、地址参数、依赖驱动的检查对裁剪仍是实现缺口。[既有运行时 alias 工作](runtime-alias-check-literature.md)已经讨论检查生成、范围检查和读写角色，这里不把它们当作新颖性主张。
