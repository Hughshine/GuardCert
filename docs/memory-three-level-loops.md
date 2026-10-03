# 三重 C 循环、矩阵乘法与完整程序连接

这批实现把以下真实 C 片段接到统一多面体入口，而不是只验证一个预先给定的三维 Loop：

```c
for (; i < n; ++i)
  for (j = 0; j < m; ++j)
    for (k = 0; k < l; ++k)
      c[i*24+j] = c[i*24+j] + a[i*22+k]*b[k*17+j];
```

识别器核对三层完整 Clight AST、每个计数器与边界的关系、有限赋值列表的完整左右侧表达式，以及数组访问和读取槽位。根据实际数组容量与仿射下标提出一个公共有限正 box；独立检查器证明 box 内每个真实下标有效。识别器、范围提案、外部候选和调度生成器均不被信任。

`memory_nary_body_model` 把源体接口推广到任意长度的坐标列表。具体语言实例负责实际机器地址、完整表达式求值、`Mem.load`／`Mem.store` 和对象登记表；组合层消费单点执行、quiet／normal／temporary frame、零点基址证据及与指令语义的对应。任意维单点与嵌套矩形 Loop 的对应已证明。当前 C 识别器实例化三重循环，不声称任意深度的 C 源识别已完成。

`memory_triple_body_source_decode` 从真实 C 成功执行推出三维 Loop 执行，并精确保留 `i=n,j=m,k=l` 的公开出口。这里快路要求三个次数都为正；零次迭代的源出口仍由原循环执行。

入口检查先确认 `i=0` 与 `0<n<=cap`，再检查 `0<m<=cap`，再检查 `0<l<=cap`，最后执行真实数组基址与对象分离检查。`memory_triple_source_words` 从源执行推出条件式的读取定义性：外层不进入时，不需要内层边界已定义；中层不进入时，不需要第三层边界已定义。`memory_triple_region_source_domain` 进一步用源零点实际访问证明基址比较可执行。`memory_triple_guard_exact` 证明生成的短路条件树与接受条件完全一致。检查不会事先读取三个边界或数组基址。

仿射候选／坐标映射复用实际依赖验证器。直接调度路径从真实源提取 PolyLang，消费外部仿射调度，调用 CodeGen，再独立核对生成候选。两维分块路径在外层 `i,j` 上引入块计数器，保留第三维 `k`；余块 guard、tile witness 与有效块数裁剪均有证明。是否允许重排仍由真实依赖检查决定，单点算术相同并不足以使整个循环重排合法。

候选重建使用一般数组后端和新鲜 private temporaries，执行后复制原边界值恢复三个源计数器。`memory_triple_candidate_rule` 提供局部带条件证书，`check_memory_triple_unified_region_sound` 将它接到已有完整程序宿主，最终仍由 `GuardMemoryUnifiedCompiler.compile_memory_unified_regions_correct` 给出 Csem→Asm backward simulation。原生统一驱动分配 16 个已检查新鲜性的辅助 temporaries，允许这条五层分块候选降低；不足的池会安全拒绝，池大小本身不是语义假设。

输入仍是固定长度的局部或全局 signed32 数组，访问的聚合仿射系数与常量偏移非负，每个所需对象必须有源零地址访问证据。标量计算按 CompCert `Int.add/sub/mul` 的机器语义编码，并不要求数据运算无回绕；guard 限制用于地址、循环边界和生成的辅助计算。稳定外部标量值参与 RHS、指针缓冲区、负系数访问及更深／依赖外层参数的 C 域继续推进。

完整输入见 [`native_memory_triple.c`](../examples/native_memory_triple.c)，测试入口是 `make native-memory-triple`。13 组完整汇编配置均通过，每组 2811 行输出与 `gcc -O0 -fwrapv` 和独立机器整数模型一致，包含完整数组、三个计数器、局部／全局对象、外围循环、机器回绕、复制链、未初始化但不被源读取的内层边界、非零起点与次数条件外的安全源输入。矩阵乘法的共同 guard 上限是 21，独立散布为 8，复制链为 7。

矩阵乘法接受交换、`i-k-j`、调度生成和三组外层二维块大小；反转第三维只接受独立写入，复制链的分裂被拒绝。七组分支诊断另外执行了 278 次源函数调用，确认正域的实际快路、各层零次迭代、非零起点、上限外输入和未定义内层边界的短路回退。未经验证地逆序执行复制链在 `n=1,m=1,l=3` 时把 `b[0]` 从 8 改成 29；编译器拒绝该候选并保留源结果。资源耗尽与错误证书测试使用需要调用 oracle 的交换候选，恒等结构可以不调用 oracle 就得到证明。分支诊断执行插桩的 Clight pretty-print，由 GCC 运行；完整 CompCert 汇编的输出在主套件中分别核对。

`build/native-memory-triple/report.json` 和 `branch-report.json` 记录上述结果。编译器 SHA-256 是 `ae9ddab7c44f6d5d8a767ec04fa5cb5b412524b524589b4ce15ca8504037f1c8`。同一编译器通过多读取计算的 14 组汇编配置／五组分支诊断，以及内层宽度搜索的七组汇编配置／四组分支诊断。全量审计重新编译 180 个内存适配模块和七个 lowering 模块；指令实例继承七项假设，validator 继承 12 项，完整编译器仍精确继承 CompCert 与 validator 的原有 42 项并集。没有新增全局公理，也没有性能测量。
