# 仿射条件域的完整 C 编译路径

`GuardMemoryCutCompiler.compile_memory_cut_regions bi bj` 处理普通 `int` 数组上的参数化嵌套循环，其中叶子由一个仿射条件选择。候选是四层二维分块循环，包含尾块和同一仿射条件，并恢复源循环的公开计数器。

```c
for (; i < n; ++i) {
  for (j = 0; j < m; ++j) {
    if (2*i + 3*j <= 14)
      a[i*10+j] = i*37+j+7;
  }
}
```

循环边界 `n,m` 在运行时变化；系数和条件常量由源 AST 提取。该入口使用实际内存和实际多面体依赖检查。定理 `compile_memory_cut_regions_correct` 将无 alarm 的 `mayReturn (OK assembly)` 接到源 Csem 和目标 Asm 的 backward simulation；源解码、候选进展和机器编码都有具体证明。

## 域限制与执行对应

`GuardMemoryAffineDomains.restrict_memory_instruction` 将仿射约束添加到原域，保留 instruction、schedule、access 和 point-space witness。`flatten_memory_restricted_domains` 证明限制后的实际有限点列表正是原列表按约束过滤的结果，适用于多个 PolyLang 语句和任意附加仿射不等式交集。

`GuardMemoryConditionalLoops.guard_memory_instructions` 给每个叶子添加数学条件。`guarded_memory_trace` 证明新执行序列准确筛选原序列；`conditional_memory_loop_points` 把实际 Loop 执行与筛选后的实际 PolyLang 执行对应起来。有限事件序列只用于证明，不在编译器中枚举运行时迭代点。

`GuardMemoryCutExecution` 给出单个二维条件 `a*i+b*j<=c` 的具体实例。源参数为 `[N;M]`，原点索引为 `[N;M;i;j]`，分块点索引为 `[N;M;ti;tj;i;j]`。附加约束分别是 `[0;0;a;b]` 与 `[0;0;0;0;a;b]`，而不是把新增 tile 坐标误认作原坐标。实际 checker 验证 tiling witness 与双向调度，`validated_memory_cut_tiling` 从源执行构造候选执行，保持实际参数、位置映射和完整 Mem。

## 机器条件和完整程序

`compile_memory_cut_condition` 用已证明的区间分析和 Clight 编码器处理条件表达式的每个中间结果及比较常量。`compile_memory_cut_condition_evaluation` 证明实际有符号机器比较恰好等于数学条件。CompCert 前端在赋值分支保留的 `Sskip; assignment` 也由实际执行解码覆盖。类型、属性、条件、赋值和循环协议全部通过 AST 证书绑定；非可信解析器的判断不能代替这些检查。

`memory_cut_source_clight_decode` 从真实源 Clight 执行得到带条件的 Loop 执行及公开计数器出口。该具体适配器要求 `c>=0`：当运行时 `N,M` 都正时，点 `(0,0)` 确实执行，因而可由源执行证明数组绑定。条件域完全为空时，不能凭空假设存在数组绑定；当前具体入口对此保留源程序。

`GuardMemoryCutTiledClight.memory_cut_tiled_local` 使用实际数组编码器生成候选 Clight，保持完整内存并恢复 `i=N,j=M`。私有临时变量宿主把这一局部规则连接到完整程序。运行时 guard 从数组布局与源入口生成：

```text
i==0 && 0<N && N<=extent/stride && 0<M && M<=stride
```

这个短路检查的读取安全也有证明：外循环为空时不要求未读取的内层上界已初始化。块大小非正、源/候选中间运算无法证明不溢出、语法不支持、证书无效或资源不足时保留源循环。

## 使用与支持边界

```sh
make native-memory-cuts
GUARDCERT_TILE_ROWS=2 GUARDCERT_TILE_COLUMNS=3 \
  build/compcert-memory-cuts/ccomp \
  -conf build/compcert-memory-cuts/compcert.ini \
  -stdlib build/compcert-memory-cuts/runtime -dclight -S input.c
```

具体 C 入口支持普通扁平数组、两个动态边界、静态仿射叶子条件、纯写 payload 和完整程序上下文。它检查规范化后的 typed AST，当前识别的运算形式包括 `i+j`、`2*i+3*j`、仅行或仅列条件。交换路径已有的读改写语句尚未进入这一条件分块入口。

任意附加约束的 PolyLang 定理和一般结构化 Loop 的条件定理，比这个具体 C 识别器更广。C 入口尚未覆盖任意嵌套仿射边界、多个叶子语句、参数参与的 cut、任意 AST 等价形式或外部 scheduler 的完整 C 接入。不能将一般数学定理报告为这些 C 功能已经实现；本页也不报告性能收益。

## 已完成验证

2026-10-03 的 `build/native-memory-cuts/report.json` 记录五组块大小 `1x1,2x3,4x4,5x7,17x13`，合计 4800 个正动态条件域。生成 Clight 中的九个函数具有实际四层分块、入口 guard 和公开 iterator 恢复。每组运行的 1294 行完整输出与 GCC `-O0` 和独立源模型一致，逐元素检查 120 个数组位置，同时覆盖非零初始计数、空循环与未读取的未初始化内层上界。

此外，完全空的负常量条件、非仿射乘法条件、无符号比较和条件中间溢出不被选中。五条独立拒绝路线为零块大小、负块大小、辅助算术溢出、证书搜索资源耗尽和注入错误证书；实际编译、执行结果保持源行为。

`build/guard-memory-proof-report.json` 对二十二个具体内存适配模块和七个 lowering 模块完成重编译与假设审计。新增条件域入口仍精确继承 CompCert 的 35 项与实际 validator 的 12 项的并集 42 项，没有新增公理；域筛选对应与机器条件数学对应均有闭合或原有逻辑假设下的具体证明。
