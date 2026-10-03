# 一般 Loop 提取与外部候选的完整程序接入

这个入口允许人或工具提出循环结构，由已提取的检查器核对后，生成带运行时条件与原片段回退的 C→Asm 程序。候选不需要提供“调度器总是正确”的证明。当前完整 C 源识别仍限于同布局单数组上的矩形混合读写列表；一般仿射结构的执行对应已在 Loop IR 层证明，不能据此声称任意 C 循环都可识别。

## 一般 IR 的执行对应

`GuardMemoryExtractorProgress.memory_extractor_execution_at` 对实际成功提取的任意 Loop/Seq/Guard 树建立：

```text
Loop.loop_semantics source (rev parameters) before after
  iff
PolyLang.poly_instance_list_semantics parameters extracted before after
```

这里的 before/after 含实际 CompCert Mem；入口参数值和整个出口状态相同。证明补全了原上游后向端点之外的源到多面体进展方向。五个模块分别证明静态指令位置、动态点的提取元数据、完整覆盖、唯一性、源时间戳排序与实际指令执行对应。循环可以有负下界、依赖外层 iterator 的仿射上下界、三层以上嵌套及合取的仿射条件。是否接受由实际提取器及表示检查决定；除法、min 和析取域在这个提取入口上保守拒绝。

`checked_memory_loop_equivalence` 对源和候选实际提取，排序域约束行，再调用实际双向依赖检查。`validated_memory_affine_loops_at` 保留同一组参数，并在具体 NonAlias 前提下给出两个 Loop 执行方向。`GuardMemoryPointIsomorphism` 将点表示的双射、时间戳保持和指令执行保持组合为整个多面体程序的表示等价。域约束排序是这个接口的具体实例，已经证明不改变域或执行；它允许合取条件改变书写顺序。

## 前提必须同时进入检查和运行时程序

二维数组的地址 `i * stride + j` 在 `j < stride` 下才为不同迭代点提供不重叠位置。无列界前提时，循环分裂会改变实际跨行冲突的顺序。因此只在 Clight 中生成 `m <= stride`，同时让依赖检查器验证所有整数参数，会错误地拒绝条件下成立的候选。

`memory_array_entry_test` 编码 `0 < n <= outer_limit && 0 < m <= stride`，将这个同一前提包在源与候选 Loop 外。`memory_array_entry_test_at` 证明具体入口范围使 IR 条件为真；`memory_array_assumed_loop_execution` 证明条件下包装前后的执行相同。Clight 的实际短路条件来自已有的 `rectangle_guard_tree`，还检查公开 iterator 为零，并从源执行建立读取安全性。条件的读取、数学域、物理数组绑定及候选 machine arithmetic 都分别有语言实例证明。

## 外部候选怎样使用

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make native-memory-proposed
GUARDCERT_LOOP_CANDIDATE="$PWD/examples/loop-candidates/fission.sexp" \
  build/compcert-memory-proposed/ccomp \
  -conf build/compcert-memory-proposed/compcert.ini \
  -stdlib build/compcert-memory-proposed/runtime -S examples/native_memory_operations.c
```

候选文件是有大小与深度上限的 S-expression。表达式含 constant/var/sum/scale 等，条件含 le/eq/and 等，语句含 loop/seq/guard/instr。文件阅读器只提议现有 Loop 类型的数据。`instr` 引用源指令位置，`each` 为每个源位置实例化一个结构：

```text
(each
  (loop (constant 0) (var 0)
    (loop (constant 0) (var 2)
      (instr current ((var 1) (var 0))))))
```

根环境为 `[n;m]`；进入每层循环后，当前 iterator 加在环境最前面。这个模板把源逐点执行的多条操作分裂成各自的二维循环。读写操作仍来自经完整源 AST 核对的原指令。文件阅读器属于不受信任的提议侧；真正的接受条件还核对指令、实参、点域和内存依赖。源指令被删除、域被更改或依赖顺序不满足时，不生成候选。

`compile_memory_proposed_regions propose private_count` 允许使用任意候选生成函数。`compile_memory_proposed_regions_correct` 的结论是完整 Csem→Asm backward simulation，要求编译返回无 alarm 的 OK assembly。参数 `propose` 没有正确性前提。源码识别、辅助变量的新鲜性与范围、guard、原片段回退及公开 iterator 出口修复全部在证明路径中。

## 范围与复现

`make native-memory-loop-ir` 单独验证一般 IR，包含真实读写的融合／分裂、三维仿射域、非仿射拒绝和错误证书／资源耗尽。`make native-memory-proposed` 编译完整 C，检查外部文件产生的实际 Clight 快路、完整数组与公开 iterator，并与 GCC 和独立模型比较。报告位于 `build/native-memory-loop-ir/report.json` 和 `build/native-memory-proposed/report.json`；当前两份报告均通过：一般 IR 为 21 个提案、1344 次独立执行比较；完整 C 为十一组配置，每组 1564 行完整输出。identity 和 interchange 各命中 10 个函数，安全 fission 命中 8 个函数；行前缀依赖的两种源码布局在 fission 下被拒绝。所有数组与公开 iterator 与 GCC 和独立模型一致。错误证书、资源耗尽、缺少提案、删语句、更改域及非仿射候选均保留源程序。

数组入口的物理 NonAlias 从 `flat_array_locations_nonalias` 闭合，不假定逻辑数组名称自动表示互不重叠的物理内存。多数组指针别名、一般 C 源提取和更广的点坐标对应仍需实现。外部入口现在支持[已经证明的点坐标交换](memory-point-coordinate-correspondence.md)，候选文件可提供 iterator 排列；参数坐标固定，候选时间顺序仍需通过依赖检查。更广的 affine 点对应继续实现。已有内置矩形交换与二维 tiling 入口继续使用其已经证明的具体对应。

这条路径修复了锁定 ExtractorFrontend 的访问维度：系数补齐长度使用指令实参个数，而不是参数加循环深度。对应 ExtractorCorrect 的叶子表示同步更新；两份补丁、源锁定及 92 个依赖文件重新编译记录均保留在仓库和构建输出中。完整 C 编译定理继续继承 CompCert 与 validator 的 42 项假设并集，没有新增全局公理。
