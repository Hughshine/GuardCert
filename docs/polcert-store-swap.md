# 一个真实 CInstr 重排的完整程序实例

`PolCertStoreSwap.v` 已将下面的两次写入重排接到 Csem→Asm 定理：

```c
a[first] = left;
a[second] = right;
```

候选交换这两条写入。当前下标和写入值是编译时给出的常量，数组为普通 signed32。`pair_parameters_ok` 检查数组 extent、两个下标范围和不同下标；检查失败时选择器返回 `None`，原片段保留。本例使用静态独立性证据，没有运行时 alias guard，也没有性能收益主张。

局部证明消费实际源 Clight 正常执行，从中恢复数组地址和两次真实 `Mem.store`，同时证明 temps 不变。逻辑状态投影到这一个数组，使用空逻辑全局环境；`projected_nonalias` 对该环境证明真实 CInstr `NonAlias`。Clight 自己的环境保持原样，源数组地址既可以来自 locals，也可以来自实际全局符号表。

`instruction_from_store` 构造真实 CInstr 执行。`actual_cinstr_store_swap` 调用上游 `bc_condition_implie_permutbility`，再以 `instruction_to_store` 将候选逻辑执行恢复为两次实际 store。最终关系是双向 `Mem.extends`，覆盖整个物理内存；投影没有隐藏写入或外围变量的内存。

`store_pair_region_contract` 把这段局部证明交给现有区域宿主。`select_store_pair` 消费已证明的序列展平，并用 `ClightSyntaxEquality.statement_eq` 精确绑定写入 AST，包括类型及属性。因此它适配前端空语句和序列结合，同时拒绝证书与源写入不同的情况。这个语法等式检查不依赖全局公理。

`store_pair_program_correct` 给出完整 Clight 小步模拟，`compile_store_pair_correct` 给出实际 Csem→Asm backward simulation。两者使用同一通用宿主；外围仍可包含调用、循环、switch 和 goto。当前全部 temps 精确对应，没有新增 private temporary。

Rocq 例子检查接受、不独立、越界、源式不匹配及前端结合方式。另一个执行例子真正分配八字节内存，构造源和逆序候选的正常执行，并证明候选的两个元素最终为 7 和 8；内存执行用权限和 load/store 定理，未把符号执行的超时当作正确性。

复现入口为 `make polcert-memory-proof POLCERT_SOURCE=.../verified-compilation-v10-driver`。`build/polcert-memory-store-swap-report.json` 将实例的完整编译端点与 CompCert 基线比较。当前尚未提取、运行该实例的原生编译器，也没有接入真实 `PolOpt` 调度算法或循环区域；这是一条具体基本指令重排链的证明，不代表完整多面体编译链已经闭合。
