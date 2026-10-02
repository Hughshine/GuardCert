# 运行时下标的真实 CInstr 重排

`PolCertDynamicStore.v` 对下面的人工候选提供条件正确性证书：

```c
// source
{ a[i] = 7; a[j] = 8; }
// candidate
{ a[j] = 8; a[i] = 7; }
```

普通 signed32 数组的 extent 是静态布局数据；两个下标是运行时 signed32 temporaries。前提为 `0 <= i < count`、`0 <= j < count` 和 `i != j`。这个前提指同一数组内的元素独立性，尚未提供不同数组对象的 alias 检查。

`ClightIndexGuard.v` 实例化五个性质原子。每个原子都有命题解释、可返回 unknown 的判定及实际 Clight 比较。`index_dimension` 证明判定的真、假结果分别给出性质及其否定；`index_primitives` 证明生成代码与该判定对应。`independent_indices` 是这些原子的公式，不是手工拼接的最终 guard 代码。共享三出口合成器生成条件树和 fallback。Rocq 还检查不同下标、逆序下标、重合、负数及越界的条件结果。

局部证明不假定入口 temporary 已初始化。`variable_store_domain` 从实际源地址运算恢复 `Vint` 下标，`variable_pair_domain` 据此建立整个检查域，并证明两次赋值不改变 temps。源执行建立检查域，不代表它已满足候选前提。条件接受后，`variable_pair_constant` 以入口值实例化既有真实 store 证明，调用上游 Bernstein 定理恢复候选执行，出口采用双向 `Mem.extends`。

`dynamic_rule` 复用同一个 `encoded_region_rule` 接口，`compile_dynamic_pair_correct` 经共享区域宿主达到实际 Csem→Asm。局部义务是证明字段，没有新增全局公理。当前原生入口同时尝试静态双写实例和动态双写实例；前端标识符 `a`、`i`、`j` 是普通参数，定理对所有标识符成立。

复现目标是 `make polcert-store-native POLCERT_SOURCE=.../verified-compilation-v10-driver`。证明审计记录在 `build/polcert-memory-dynamic-store-report.json`，原生结果另记在 `build/native-dynamic-store/report.json`。实际编译确认三个区域、共十五个原子比较，以及每个区域的候选和源代码 fallback。四组输入覆盖正序、逆序与两种重合下标；程序输出同时匹配 GCC 和独立计算。不同值和 volatile 两种前端例子保留原代码。

选择器仍要求恰好两条写入的语法子树，包括完整的类型及属性对应。内部循环区域、private temporary、跨数组 alias 和实际 PolOpt 调度算法未完成；外围函数、循环体和 goto 由现有宿主覆盖。未测量性能。

此例也指出调度包的一项设计要求：当机器代码到数学／逻辑指令的解码依赖范围或无溢出前提时，不能要求无条件解码源执行。接口现已把 `bridge_entry_domain` 与 `bridge_assumption` 分开：先取得安全检查所需的入口域，再在接受证据下解码并编码。

`PolCertStorePackage.v` 已给出具体实例。它为下标性质库补充“实际数组地址”的域，复用同一合成器而不增加检查；条件接受后构造真实源 CInstr 指令列、交换证书及 NonAlias 投影，再将真实候选指令列恢复为 Clight 执行。`compile_packaged_stores_correct` 经通用调度包路径达到 C→Asm，直接规则保留作为独立局部证明。提取入口已改用 `propose_dynamic_package → select_schedule_region → package_rule`，同样的十五个原子比较、快路与 fallback 原生检查均通过；报告记录该 proposer 及实际编译器的 SHA-256。
