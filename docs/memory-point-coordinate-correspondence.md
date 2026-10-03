# 候选循环的点坐标对应

外部循环交换会改变提取器赋予 iterator 的坐标位置。源循环的点可能是 `[n;m;i;j]`，候选交换循环则是 `[n;m;j;i]`。即使两个循环访问同一批数组元素，严格比较原始域与实参矩阵也会拒绝它。这个接口允许候选附带一串坐标交换，并在依赖检查之前证明表示转换不改变候选执行。

`GuardMemoryCoordinateSwap` 定义相邻坐标交换，证明它是保持长度的自逆函数，固定参数前缀，并与相应系数列交换保持点积、仿射求值和域满足关系。PI 的域、schedule、实参矩阵及 access transformation 同步更名。指令本身的读写函数仍作用于指令实参，不随点坐标修改。

`memory_coordinate_swap_execution` 使用 `GuardMemoryPointIsomorphism`，将点覆盖双射、时间戳不变和真实指令执行保持提升为整个 PolyLang 程序的执行等价。`GuardMemoryReindexedExtractor` 将多个相邻交换组合起来；`memory_reindexed_execution` 保留同一组入口参数和完整 CompCert Mem 状态。成功提取提供所需的 Identity witness 与矩阵宽度，不把任意矩阵当作已满足这些条件。

候选检查步骤为：实际提取两个 Loop，给候选点坐标更名，排序约束行，再执行实际双向依赖验证。坐标对应只建立表示等价；候选的时间顺序仍由依赖验证器核对。`validated_memory_reindexed_loops_at` 给出源与原候选 Loop 的两个执行方向。

## 外部文件

`examples/loop-candidates/interchange.sexp` 描述二维交换：

```text
(reindex (0)
  (loop (constant 0) (var 1)
    (loop (constant 0) (var 1)
      (each (instr current ((var 0) (var 1)))))))
```

`reindex` 的数字从 iterator 坐标前缀开始计数，参数坐标自动保护。`(0)` 交换前两个 iterator；`(0 1 0)` 可以反转三维 iterator 顺序。没有 `reindex` 包装的旧文件继续使用空交换列表。

```sh
GUARDCERT_LOOP_CANDIDATE="$PWD/examples/loop-candidates/interchange.sexp" \
  build/compcert-memory-proposed/ccomp \
  -conf build/compcert-memory-proposed/compcert.ini \
  -stdlib build/compcert-memory-proposed/runtime -S examples/native_memory_operations.c
```

Rocq 的 `memory_candidate_proposer` 当前返回 `option (Loop.stmt * list nat)`。候选及坐标对应都属于提议；完整 C 编译定理不要求生成器正确。若实际对应、域、实参或依赖检查不通过，保留源片段。

独立验证器的 `loops-reindexed` 输入增加 `swaps` 数组。`make native-memory-loop-ir` 包含二维读写交换、缺少对应的安全拒绝、三维坐标反转，以及此前的融合／分裂和仿射域。当前一般 IR 报告为 24 个提案、1632 次独立执行比较，全部通过。完整 C 的测试脚本 `native_memory_proposed.py` 已通过十二组配置，每组 1564 行完整输出与 GCC 和独立模型一致；interchange 实际命中 10 个函数。它检查生成的真实交换循环、数组及公开 iterator。缺少 reindex 或错误实参的候选均被拒绝。

## 当前边界

这条实例支持由相邻交换组成的维度排列。[语义域等价检查](memory-semantic-domain-alignment.md) 已处理约束集不同但相互包含的域表示。一般 affine shear 和 translation 还需其他坐标对应。点双射接口本身可以承载更广的对应；声明接口不等于已经实现那些实例。完整 C 源识别仍限于当前矩形混合读写列表。内置二维 tiling 路径继续使用其单独证明的 tile witness。
