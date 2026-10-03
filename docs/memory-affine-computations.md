# 多个实际读取与整数计算的源体实例

源前端扩展到一次赋值中的任意有限数量仿射读取，以及常量、两个循环变量、加、减、乘。例如：

```c
for (; i < n; ++i) {
  k = 2 * i + m - p;
  for (j = 0; j < k; ++j) {
    c[i * 24 + j] = a[j * 17 + i] * b[i * 20 + j] + i * j;
  }
}
```

计算右侧可以是非线性的，地址仍需属于已证明的仿射访问子集。指令保存真实读列表和 `Int.add/sub/mul` 计算，不假定读取独立，也不把表达式数值当作数学无界整数。不同数组、重复读取、同数组邻居读取和更新链使用同一依赖验证器。

`memory_compile_source_value` 保留每个访问的原始源表达式，将加载值位置绑定到纯计算表示。检查器核对完整表达式 AST，并要求声明的每个加载位置都被源计算实际使用。后一个义务用于从成功源执行建立所有读取及基址证据；不能加入源程序不读取的假访问来绕过证据要求。

`memory_source_value_loads_exist` 从实际源表达式执行恢复所有实际 load；`memory_source_value_evaluation_inverse` 证明纯计算得到同一个机器整数。`memory_affine_compute_inverse` 将完整赋值对应到这些读取、计算和 store。`memory_affine_reads_resolve` 与 `memory_affine_reads_loads` 证明登记表地址及读取值与实际 `Mem` 一致；`memory_affine_compute_registry` 接到一般指令语义。

`memory_compute_sequence_point_execution` 按源顺序组合全部赋值，`memory_compute_body_model` 具体实例化通用源体接口。源解析器 `describe_memory_compute_region` 返回包含实际源、访问和指令的证书包。它不修改一般依赖验证、调度、分块、候选 lowering 或完整程序宿主。

统一入口的接入、全量假设审计和提取编译器验证均已完成。152 个内存适配模块和七个 lowering 模块重新编译；指令桥继承 7 项、validator 继承 12 项、完整编译器继承原有并集 42 项假设，没有新增全局公理。提取二进制 SHA256 为 `01361eee90bf99fae0bc797c65be69d31d246bc4dd1a2269e7c2b70e44371b95`。测试输入为 [实际 C 程序](../examples/native_memory_affine_compute.c)，包含两个读取、乘法、非线性标量值、邻居更新、同数组访问、混合计算链、全局数组、外围重复循环和乘法回绕。独立 signed32 模型与 GCC `-fwrapv` 已核对 4,263 行完整数组和公开计数器输出。`-fwrapv` 在参考运行中明确采用与 CompCert 整数运算一致的回绕行为。

范围仍是两层规范 C `for`、零起点快路、非负聚合地址系数及偏移，并要求所有对象有源执行建立的零地址证据。读取额外稳定标量参数的计算、一般指针切片和更深 C 循环域尚需接入；非仿射地址和缺少基址证据的读取应安全拒绝。

`make native-memory-affine-compute` 调用相同的 `compile_memory_unified_regions` 完整程序入口。14 组汇编配置全部通过：恒等、交换、分裂、平移、剪切，四组块大小，以及错误映射、错误维度、超大系数、资源耗尽和故障证书。每组核对 4,263 行完整数组、公开计数器和参数输出，另有五组分支诊断核对实际快路和回退。诊断使用 GCC 执行带计数器的 Clight pretty-print；完整汇编验证独立进行。

同数组双读取 `B[20*i+j] = B[17*j+i] + B[31*i+2*j]` 在恒等、分裂、平移、剪切与 `1×1` 分块下的静态外层上限为 16；交换和其余分块在此版本收紧到 1。独立数组的加法、乘法与计算链上限为 25，邻居更新上限为 24。独立模型另记录不加条件重排导致的不同单元，不能把单纯的 validator 拒绝当作错误程序的证据。

运行报告为 `build/native-memory-affine-compute/report.json` 和 `branch-report.json`，全量审计为 `build/memory-affine-compute-audit.log`。
