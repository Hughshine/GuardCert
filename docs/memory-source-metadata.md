# 候选接口中的源维数与参数前缀

候选提议器现在接收 `guarded_memory_request`，由已经核对的源包提供三个字段：

| 字段 | 含义 |
| --- | --- |
| `request_instructions` | 源赋值位置对应的实际内存指令，供候选引用。 |
| `request_coordinates` | 源循环的坐标维数，包括没有出现在访问下标中的维度。 |
| `request_context_arity` | 源 Loop 的参数前缀长度，包括循环边界和稳定参数。 |

这个接口替代从写访问系数和 RHS 使用位置猜测维数、参数数量的旧方式。`GuardMemoryScheduleInput.coordinate_axis` 用实际前缀长度生成参数列的零系数，再放置所选坐标的单位系数。显式仿射系数、直接 Loop 候选、坐标映射和分块提案仍由各自的检查器核对。

例如，下面的源有两个循环坐标，但写访问只使用 `i`：

```c
for (; i<n; i++)
  for (j=0; j<m; j++)
    p[i] = q[i]*alpha + j*beta;
```

旧提议器从 `p[i]` 得到一维，因而拒绝 `(coordinate 1)`。新接口从已核对的循环包取得二维信息，以及边界、`alpha` 和 `beta` 的参数前缀。`p[0]=q[0]*alpha+beta` 也不能因访问没有坐标而丢掉两层源循环。访问冲突和调度合法性仍另行验证；相同地址的写入不会因字段变得准确而自动获得可交换证明。

另一个实例是 `K=i+M-P; j<K`。源上下文包含 `N,M,P` 三个参数，即使写地址只使用 `i,j`，调度行也需要保留三个参数列。源包按原来用于域编码与候选 lowering 的上下文计算这个长度。

完整 `compile_memory_unified_regions_correct` 对任意 `guarded_memory_proposer` 继续成立。候选元数据不替代域、参数、指令、访问依赖、检查安全性或机器 lowering 的证书。当前更改没有放宽这些证明义务。

2026-10-03：269 个适配模块和七个 lowering 模块的完整 Rocq 审计通过，完整程序端点仍为原有 42 项假设。此前 `b8b9dab` 的编译器在三个例子上得到正确输出，却没有生成优化分支；新编译器在六组正常配置中均生成三个可达的优化分支。九组完整汇编配置共执行 828 次调用，全部输出与 GCC 和独立机器整数模型一致；六组分支诊断共执行 72 次调用，其中 18 次进入优化路径、54 次回退。非法坐标、错误证书和资源耗尽配置正确保留源程序。

`make native-memory-source-metadata` 将运行九组完整汇编配置和六组独立分支诊断。输入为 `examples/native_memory_source_metadata.c`。汇编输出按全部数组元素和公开计数器比较；分支诊断通过 GCC 执行加计数标记的 Clight 打印结果，两类证据分别报告。

报告为 `build/native-memory-source-metadata/report.json` 和 `branch-report.json`。编译器 SHA256 为 `8b5e6fe83d77b5a29e66e8b56d459a0e60f838a5f317c15a79a5847016d6eda5`。同一二进制还通过多指针、稳定标量指针、单指针和 signed 仿射地址四类各三组完整汇编回归。便利坐标语法当前限制为 16 个坐标和 32 个上下文参数，超出时拒绝提案；语言证明没有这个上限，原生辅助变量池的既有边界保持不变。
