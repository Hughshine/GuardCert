# Signed 仿射源地址

本次扩展允许坐标的正系数、负系数及混合系数，例如 `a[8*i+j]`、`a[63-8*i-j]` 和 `a[56-8*i+j]`。数据表达式仍使用实际 CompCert signed-int 运算和稳定 RHS 标量接口。2026-10-03 的正式 Rocq 编译与假设审计覆盖 241 个内存适配模块及七个 lowering 模块；完整 Csem→Asm 端点保持 `GuardMemoryUnifiedCompiler.compile_memory_unified_regions_correct`，继承的 42 项 CompCert／验证器假设不变，没有新增公理。

## 范围编码

`GuardMemorySignedRanges.memory_signed_box_check` 对每个仿射项 `c*x`、`0 <= x < limit` 计算：

- 下界：`min(0, c*(limit-1))`；
- 上界：`max(0, c*(limit-1))`。

各项求和并加上偏置后，独立检查最终索引落在对象的逻辑单元范围内。`memory_signed_box_sound` 证明这个 bool 检查的可靠性；`memory_signed_box_accepts_nonnegative` 证明此前通过的非负系数检查仍然通过新检查。两条定理都没有全局公理。

`GuardMemoryNaryAccessCheck.memory_nary_access_check_sound` 使用新范围定理，保持原有语义契约。`GuardMemoryTripleSyntax.propose_memory_nary_access_cap` 另外给负系数地址提出共同次数上界；这个提案仍需独立检查。非负系数分支沿用原有上界提案。

源地址表达式的中间加减乘仍按 CompCert 的模运算求值。范围证明检查最终数学仿射值；既有源求值定理证明其机器结果是对应的 `Int.repr`。因此，表达式中间回绕且最终地址合法，不需要添加额外的“中间运算一律无回绕”假设。测试的 `signed_address_wrap` 使用会在非零坐标上回绕并抵消的项。这里的语义边界是 CompCert 的既有整数语义；GCC 对照明确使用 `-fwrapv`。

## 实际程序与候选

测试源为 `examples/native_memory_signed.c`，包含反向读取、反向写入、有依赖的反向访问链、重复程序上下文、三维访问、混合系数、地址中间回绕、零次循环中的未初始化标量及多个局部固定数组。

```c
for (; i < n; ++i)
  for (j = 0; j < m; ++j)
    buf[8*i+j] = buf[63-8*i-j]*alpha + buf[8*i+j] + beta + i*j;
```

完整编译入口及外部候选格式保持不变；`make native-memory-signed` 运行实际汇编输出检查和独立分支诊断。2026-10-03 的正式原生测试通过 13 组配置，每组比较 226 次实际调用的完整输出。配置包含恒等、换序、逆序、直接调度、语句分离、三组分块、错误证书和资源耗尽。10 组分支诊断共 5463 次调用通过，覆盖不同轴长度、极值标量、非零基址、每一维零次循环、空指针和非零起点。

编译器 SHA256 为 `026fa36f1712000825a9d49876e2114f37db59a7f16d085e69438d6a52af1c26`。所有完整输出由该编译器生成的汇编给出，与 GCC `-O0 -fwrapv` 及独立 32 位模型一致。分支诊断执行带计数标记的 Clight 打印结果；它不扩大汇编证明范围。报告位于 `build/native-memory-signed/`。

反向依赖链的真实输入为 `[3, 0, 1, 3, 1, 3, -7]`；未经保护的逆序和分离执行使实际打印缓冲区的下标 63（指针基址偏移 3）从源的 `-12449` 变为 `-758` 与 `-8811`。实际验证后的两种候选只接受共同次数上界 1，该输入观察到零次快路命中并保持源结果。

同一二进制对已有指针标量及固定数组标量路径分别通过三组汇编回归：恒等、直接调度换序及分块。它们是本次共享范围检查替换的回归；完整 16 组结果仍属于此前标量版本，见 [标量验证记录](memory-stable-scalar-parameters.md)。

## 边界

负系数检查扩展的是现有递归矩形源路径。固定数组实例仍要求每个对象有源访问给出的零地址证据；`signed_array_no_zero_anchor` 故意缺少该证据，必须保持原循环。一个稳定指针缓冲区的实例不要求固定数组零地址证据，实际指针基址及访问权限由成功源执行推导。多个不同指针变量、深层非矩形源域仍需要后续适配。

`GuardMemoryFootprintRestriction`、`GuardMemoryFootprintCapabilities`、`GuardMemoryPointerCellComparison` 和 `GuardMemoryFiniteFootprint` 是后续多指针工作中的独立证明组件，尚未登记到本次生产编译器或原生能力报告。它们不扩大本页的已实现 C 源范围。
