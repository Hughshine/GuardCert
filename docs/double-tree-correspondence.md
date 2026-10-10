# 整树原 Clight／Loop 对应与活动路径观察

本阶段证明已识别的整个 source tree 与同一 shared registry 上的 Loop 模型
具有双向有限正常执行对应，并给出最终 memory 和准确公开 temporaries。
覆盖 skip、真实 IEEE assignment、sequence、不同嵌套深度和 strict ranges；
range 保留 signed I32 literal 起点、global I64 header 与可选 I32 subtraction。
此处 upper 不依赖 ancestor iterator，不能直接把固定 child-exit 证明推广到
任意 triangular／affine child bounds。

**原三个 region 的优化尚未安装。** 原 fusion1、multi-stmt-stencil-seq、tricky3
的冻结 exported Clight 已实例化条件执行对应；动态范围、cell resolution、
活动 header receipts 和 scope 仍由 factory／语言实例闭合。新 path-sensitive
captures、candidate、Csem→Asm 或 native coverage 不由本阶段推得。
当前 native 覆盖保持 22 原例／39 sites。

## 模型、参数与出口

[ModelData](../adapters/compcert-memory/GuardMemoryDoubleSourceTreeModelData.v)
将 global header 在原共享 vector 中的位置编码为 `depth + parameter_position`。
`double_tree_bound_model_value` 在 header membership 下证明数学表达式求值，
`N-2`／`N-3`引用同一 `N`；它不是原 `N` 的 I32 机器编码证明。
Leaf 使用该深度的 control prefix，所有 assignments 用同一 layout registry。

[Model](../adapters/compcert-memory/GuardMemoryDoubleSourceTreeModel.v)的
`double_source_tree_shared_memory` 将实际 Loop execution 递归连接到整树 memory
relation。Point 保留 `DoubleAssignmentInstr` 的 IEEE 运算和真实 `Mem` actions；
sequence 保留中间 memory，loop 保留从 signed lower 开始的 counted iterations。
Registry frame 沿这些实际执行组合，不能用数学 footprint 替代 load／store 权限。

[Exit](../adapters/compcert-memory/GuardMemoryDoubleSourceTreeExit.v)复用已有 fixed
setter、frame、idempotence 与 commute 服务。Sequence 的后一个 child 决定同名
iterator 的最终值，允许兄弟循环重用 iterator。Range 自身总执行 initializer，
最终值为 `max(lower,upper)`；空 range 不设置未到达 child 的 temporaries。
Ancestor freshness 由 source checker 提供。Child bounds 不依赖 iteration value，
因而可将重复完成的 child setter 合并为一次；这是该证明的适用条件。

## 状态与真实 source bridge

[State](../adapters/compcert-memory/GuardMemoryDoubleSourceTreeState.v)分开记录：

| 接口 | 内容与责任 |
| --- | --- |
| `double_source_tree_shared_layout` | 每个实际 leaf 的共享 layout certificate；decoder 自动生产。 |
| `double_source_tree_scope` | Language/site 排除实际 leaf 的 global symbols 被 locals 遮蔽。 |
| `double_source_tree_model_facts` | Domain 提供 reached range 的 I64 bound 范围和所有 reached points 的 cell resolution；没有 C 执行正确性 callback。 |
| `double_source_tree_header_words` | Language/capture 提供指定 header 的真实 global binding 和 `Mint64` load receipt。 |
| `double_source_tree_entry` | 原 control words 与 header receipts 的状态关系，不等于可运行 guard 或任意入口安全。 |

`double_source_tree_active_headers` 只列数学活动路径需要的 headers。空 outer
仍需要自己的 header，但无需 child 的 load；未活动 parameter slots 可以有
任意模型值。这个集合由证明使用，不是已经发射的动态 capture 算法。
Factory 后续必须在真实 machine state 上安全构造并运输相应值。

`double_source_subtree_raw_header_frame` 支持 subtree 自身不使用的后部 header。
它消费 enclosing region 继承的 write exclusions，复用实际 raw assignment 和
Clight structured-frame 服务，保持 loads／permissions；不借用 accepted point
resolution、范围或 no-wrap。这补足了旧整树 frame 对 header membership 的限制。
`double_source_tree_entry_preserved` 同时运输 ancestor control words 和这些 observations。

[Source](../adapters/compcert-memory/GuardMemoryDoubleSourceTreeSource.v)的
`double_source_tree_execution_memory` 递归消费上述服务、实际 initializer／test／
increment、leaf execution bridge 与 range-settle theorem，取得原 raw/canonical
Clight execution 的双向对应和公开出口；`double_source_tree_source_Loop` 再接
共享参数的完整 Loop execution。两者都有明确动态入口前提。

[Correspondence](../adapters/compcert-memory/GuardMemoryDoubleSourceTreeCorrespondence.v)
的 `checked_double_source_tree_source_Loop` 将 `checked_double_source_tree`
的接受接到原 statement，自动闭合语法重建、layouts 和活动 header exclusions。
实例化者仍生产 scope、model facts 和实际 header receipts；源码用户不交逐 leaf
semantic callbacks。Header word 的 `repr` 对应与实际 signed／no-wrap 事实、
以及 candidate backend 的 I32 参数编码是不同义务。

[Syntax](../adapters/compcert-memory/GuardMemoryDoubleSourceTreeSyntax.v)从 checked
tree 证明 quietness、normal completed outcomes 和 temp writes。它不取代前序
独立 strict progress protocol；有限正常执行对应不能扩大成任意正常终止或
divergence 保持。

## 验证与保留的失败

八模块 858 行，36 queried endpoints：16 closed，最多继承六个 globals，
无新增 global assumptions。审计追踪 270 reachable sources、9,979 bindings；
21 次 compilation attempts 中八次成功、十三次失败，均保留 snapshots／logs。
固定摘要见[double-tree-correspondence.json](double-tree-correspondence.json)。

[原源实例化脚本](../scripts/check_double_tree_correspondence.py)直接复用前序冻结
的 `Original.v`／`Probe.v`，不再次调整源计算或 frontend。三个 complete marked
regions 的 decoder acceptance 接到本次条件执行 theorem，原源及其 IEEE／scalar
计算保持。结果在 `build/double-tree-correspondence/source-attempts/source-v2/report.json`。
首 probe 已证明对应，但 helper 因 Events 假设短名拒绝；改用 qualified Events
references 后三例成功，初始 proof／helper snapshot 单独固定。

[BoundaryCases](../adapters/compcert-memory/GuardMemoryDoubleSourceTreeBoundaryCases.v)
验收共享 `N`、深度二参数位置、兄弟 iterator 最后写入、空 outer 的观察集合与
child temp frame。`tree_empty_outer_actual_execution` 取得实际 raw Clight 执行，
仅假设 outer 的 binding／load，不要求 child header 的 binding／load／范围或
source execution。直接计算 symbolic temp tree 的失败触发 Rocq stack overflow；
后继用已有 `PTree` 定理证明，失败与成功输入分别保留。

## 当前必须接上的消费

下一步生产 path-sensitive capture 和 accepted model facts：从原 reached
comparison 取得读取许可，经先前 subtree raw effects 与 temp-read footprint
运输到入口，未到达 child 不读取。安全调用、private writes、拒绝运输与接受
后的范围／参数编码分别闭合；证明中的 source execution 不是运行时预执行。

同一 whole-region factory 随后实际消费该 bridge，运行 phases/codegen，验证
最终 candidate、机器 lowering 与准确公开出口，接当前 intermediate program
的 host／Csem→Asm backward simulation。原 region 不拆成独立 sites 来替代
fusion。OLO compact conditions、顺序 configurations、原 benchmark tiers 和
包含 guard／fallback 的完整调用成本继续在完整 goal 中。
