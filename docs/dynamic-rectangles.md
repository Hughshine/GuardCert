# 动态矩形循环交换：从源 C 到完整程序

这一实例将固定四点的循环交换推广到运行时决定大小的矩形。编译器从数组类型和访问表达式提取长度、行跨度、系数和偏置，生成入口检查，再构造交换后的真实循环。正确性定理量化所有运行时边界；编译器不枚举运行时迭代点。

## 输入与生成代码

当前接受 ordinary signed32 数组和以下两层严格计数循环。标识符可以不同，常量由源 AST 提取。

```c
int a[120];
/* n、m 是运行时输入；周围程序初始化 i 和数组。 */
for (; i < n; ++i) {
  for (j = 0; j < m; ++j) {
    a[i * 10 + j] = i * 37 + j + 7;
  }
}
```

也接受同一格子的读改写：

```c
a[i * 10 + j] = a[i * 10 + j] + (i * 37 + j + 7);
/* += (i * 37 + j + 7) 由前端生成同一已检查的形状。 */
```

检查的逻辑条件是：

```c
i == 0 && 0 < n && n <= 120 / 10 && 0 < m && m <= 10
```

检查通过后运行：

```c
for (j = 0; j < m; ++j) {
  for (i = 0; i < n; ++i) {
    a[i * 10 + j] = i * 37 + j + 7;
  }
}
```

检查不成立时运行原循环。实际 Clight lowering 使用已有的共享回退结构，所有失败分支汇合到同一份源代码。源程序的 `goto`、外部调用和外围循环仍由完整程序宿主处理。

长度为 105、跨度为 7 的数组生成 `n <= 15 && m <= 7`。负系数和负偏置采用前端的一元取负语法。选择器核对完整源 AST、内外循环结构、类型和控制变量关系；仅识别到相似表达式不能取得证书。

## 前提为何足够，检查为何安全

令数组长度为 `A`、行跨度为 `S`。静态检查要求 `0 < S <= A <= Int.max_signed`，且 `4*A <= Ptrofs.max_unsigned`。运行时前提为 `0 < n <= A/S`、`0 < m <= S` 和 `i == 0`。

这些条件保证每个点满足 `0 <= i*S+j < A`，地址下标的乘加不回绕，指针偏移可表示。不同点的下标不同，因此它们的四字节写入不相交。语言实例提供真实 `Mem.store` 的交换定理。对于读改写，`CompCertMemoryActions` 从实际 `Mem.load` 取得操作数，纯计算产生待写值；三项 Bernstein 条件分别核对 write/write、write/read 和 read/write 不相交。每个点只读取自己写入的格子，因此不同点的三项条件都成立。通用调度核组合交换性质，得到整个矩形的顺序交换证明。

写入值仍使用相同的 CompCert `Int.mul`、`Int.add` 和 `Int.repr`，每个点在两种顺序中产生相同的机器值。这里没有把 payload 运算替换成数学整数运算，也没有添加 payload 不溢出的前提。

检查按 `i == 0`、`n > 0`、外层上界、内层正性、内层上界的顺序短路。源外层执行零次时可能不读取 `m`，所以检查域只在 `i == 0 && n > 0` 后要求 `m` 已定义。这个条件定义性由源执行证明导出，不能作为额外的用户假设。

## 可复用接口与定理

| 层 | 接口或定理 | 提供的保证 |
| --- | --- | --- |
| 语义无关调度核 | `SchedulePermutation.independent_permutation_certificate` | 指令排列加可交换性质产生调度证书；状态、指令和独立性由语言提供 |
| 参数化域 | `rectangular_order_permutation`、`rectangular_schedule` | 任意矩形的行列顺序对应；嵌套迭代与调度执行双向对应 |
| CompCert 内存实例 | `rectangle_interchange_preserves_memory` | 在列宽不超过跨度时，交换保持完整 `Mem`，包括未写区域和权限 |
| 读写内存实例 | `independent_memory_actions_reorder`、`rectangle_memory_interchange_preserves_memory` | 保留实际读取的值与完整 `Mem`；从读写独立性证明交换 |
| 真实读改写 | `rect_update_inverse`、`rect_update_evaluation`、`rectangle_update_region_rule` | 实际 Clight 赋值与 Mem.load/计算/Mem.store 双向对应；完整 AST 核对读地址、写地址、运算与类型 |
| 真实单层循环 | `frontend_parametric_decode`、`frontend_parametric_encode` | 任意次数的 Clight 循环与语言提供的 body 关系对应，并保留声明的 temporary frame |
| 真实嵌套循环 | `rectangle_source_decode`、`rectangle_target_encode` | 动态矩形迭代、内层重置和循环出口与真实 Clight 对应 |
| 检查编码 | `rectangle_guard_primitives` | 通过的检查建立所需前提；源执行允许的入口上检查可安全求值 |
| 局部规则 | `rectangle_region_rule` | 检查前提下，候选与源具有相同完整内存和所有退出 temporaries |
| 完整程序 | `compile_rectangular_regions_correct` | 编译成功时，`Csem.semantics p` 到 `Asm.semantics tp` 的 backward simulation |

这些证明没有增加全局公理。通用排列和迭代对应核没有全局公理；语言实例继承 Clight 和 CompCert 的既有假设。完整程序定理的 35 个假设与当前 CompCert 编译器基线相同。审计保存在 `build/rectangular-proof-report.json`，其中记录证明源码摘要。

## 运行与验证

```sh
opam exec --root="$PWD/.toolchain/opam" --switch=guard -- make native-rectangular
```

编译器输出在 `build/compcert-rectangular/ccomp`。使用普通 CompCert 参数即可编译 C；`-dclight` 导出插入检查和交换后的循环。

原生套件 `examples/native_rectangular.c` 测试两种布局的 225 个正矩形，另测试读改写的 345 个正矩形，以及重叠写入、非零初始下标、空内层、空外层和 signed 极值路径。它逐元素比较数组与 `i`、`j` 的出口，并分别与独立 Python 执行模型和 GCC 结果比较。套件还核对实际 Clight 中的 guard、两种循环顺序和单份源回退。

上下文覆盖局部数组、全局数组、`goto` 和外围循环。零次外层执行测试未初始化的内层边界。读取其他格子的 RHS、volatile 数组和无效跨度必须被拒绝。同格子读改写及复合赋值均实际命中。结果保存在 `build/native-rectangular/report.json`。

## 与完整多面体能力的距离

目前实现的是动态矩形上的一种非恒等仿射调度，循环体限于一个纯仿射值的独立写入或同格子读改写。它已闭合源解码、条件生成、内存重排、候选重建和完整程序证明。

任意仿射域、多个读写语句的依赖验证、保序的跨迭代读写依赖、人工或外部提出的一般仿射调度、skewing、带重排的多维分块、ISS、指针数组的 alias 检查仍未实现。顺序 strip-mining 已通过 private temporary 宿主接入，并与上述交换和读改写组合验证，见 [private-stripmine.md](private-stripmine.md)。当前选择器内置循环交换，没有调用 Pluto 或 PolOpt，没有进行性能测量。后续分块需要新旧迭代点的对应证明、边界运算检查和辅助变量出口证明，不能仅靠排列证明宣称完成。
