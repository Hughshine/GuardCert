# 递归 C 源循环与任意有限维模型

这批实现把三层源证明推广成递归构造。`memory_source_nest` 保留每层真实 Clight body AST；独立检查器核对完整 counted loop、子迭代器复位、顺序关联以及叶子赋值。深度由实际语法计算，不以三层作为证明上限。

`memory_recursive_source_decode` 消费叶子单点执行、normal／quiet／temporary frame，以及每层计数器的 signed range。它组合任意有限层的真实源执行和 `memory_nary_iterations`，精确给出所有公开迭代器的出口值。框架组合层不需要展开单点内存语义；`memory_recursive_body_source_decode` 将已有有限多读取整数计算模型具体接到实际 `Mem.load`、`Mem.store` 与任意维矩形 Loop。

`memory_recursive_bounds_domain` 逐层表达检查读取的条件定义性，`memory_recursive_source_bound_words` 从实际源成功执行推出它。`memory_recursive_guard_exact` 证明短路检查树与接受判定完全对应，`memory_recursive_region_source_domain` 用正域的真实源零点访问提供对象基址证据。外层为零或某个内部次数为零时，检查不继续读取更内层的未定义边界。

映射候选、真实源仿射调度与代码生成共用实际域等价和依赖 validator。外层二维分块保留所有内部原维度，使用一般 point witness，并证明从宽泛块范围裁剪到真实块数的执行等价。候选 lowering、private temporary frame 和任意数量公开计数器恢复都已具体实例化；`check_memory_recursive_unified_region_sound` 消费这个区域证书，完整程序保证仍来自 `GuardMemoryUnifiedCompiler.compile_memory_unified_regions_correct`。

语法范围是固定长度的局部／全局 signed32 数组、canonical signed counted loops、复位的内部迭代器和稳定次数 temporaries。所有维度共用从实际访问与容量提出、再独立检查的有限正 box。叶子体是有限赋值列表，地址的聚合仿射系数及常量偏移非负，所需对象有源零地址访问证据，标量值使用机器整数加减乘。数据回绕被保留。更一般依赖外层的深层域、稳定外部 RHS 标量参数、指针缓冲区与负系数访问仍需扩展。

语言和编译器证明允许任意有限维度及足够的新鲜辅助变量。当前原生驱动提供八对辅助计数器：普通八层候选可用满该池，六层源的外层二维分块需要八层候选；九层普通候选和八层源的二维分块会被安全拒绝。这个资源限制由 lowering 检查，不是语义假设。

输入是 [`native_memory_recursive.c`](../examples/native_memory_recursive.c)，入口为 `make native-memory-recursive`。独立模型与 `gcc -O0 -fwrapv` 已核对 750 次完整函数调用／2250 行输出。模型含四、五、六、八、九层源、完整数组和公开计数器、全局对象、外围重复循环、机器整数回绕、未定义但不被源读取的内部边界，以及拒绝用例。未经验证的复制链反转在输入 `n=m=p=1,q=3` 时将 `b[0]` 从 8 改成 29，分裂改成 5。17 组提案／拒绝配置的完整 CompCert 汇编均与独立模型及 GCC 参考输出一致，每组 2250 行。11 组分支诊断共执行 458 次函数调用，核对实际快路、每个零次维度、非零入口、超出 guard 的安全尾部输入、未定义内部边界的短路和辅助变量池不足时的原程序结果。分支诊断通过 GCC 执行加计数器的 Clight pretty-print；它与完整汇编验证分别记录。

原生报告为 `build/native-memory-recursive/report.json` 和 `branch-report.json`。这一批提取编译器的 SHA256 为 `aff9380452d2d3cd73f0664b6168cb90d376c0c85e0af9864720b616490c36c2`。`schedule-*-4` 表示提供四个仿射调度行；行系数会在更长上下文中补零，因此并不限定源维度。恒等／分裂调度还接受部分更深的源；实际生成的每个候选都经过独立检查。交换调度的四层测试接受四层源。

全量审计重编译 192 个适配模块和七个 lowering 模块；完整编译器仍精确继承原有 42 项假设，没有新增全局公理。三层源的 13 组完整汇编回归和七组分支诊断也通过同一编译器。证明没有人为的三层上限，但识别器仍限定上述规范矩形源族；指针切片及更一般的深层仿射域继续实现。
