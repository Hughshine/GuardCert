# 等式消元前置的投影服务与完整编译入口

本阶段按 narrative 的三方责任边界处理真实 codegen 障碍。2026-10-10 再次
读取远端 `topdown/research-positioning`：`8ce9c8b`，正文与 main 相同。没有新的
kernel API；本阶段扩展的是多面体 domain 库与现有常量源实例。

## 动机与算法

前序完整语料的 `fusion10` tiled 编译在真实调度／分块 phase 后发生 stack
overflow，64 MiB 栈重试仍失败。该重试的完整 backtrace 经过
`ASTGen.generate_loop_many`、`Projection.PolyProjectImpl.do_project`、
`Canonizer.VplCanonizer.canonize`，最终在 `VplInterface.poly_to_Cs` 的 list map
中溢出。原算法先形成 Fourier–Motzkin 的正负约束两两组合，再调用化简器。
`fusion2` 同一阶段存在 180 秒 timeout；其具体热点不能仅由另一个例子的
backtrace 推定。

[EqualityReducedProjection](../theories/EqualityReducedProjection.v)复用已有
`simplify_poly` 的显式等式替换，在消除第 `n` 个变量前处理 `0..n` 的等式，
再执行原 Fourier–Motzkin 算法。证明逐项满足已有 `ProjectOperator`：消除指定
变量、不引入原来缺失的变量，以及 scaled exact projection。其含义是原
`isExactProjection` 的正整数缩放／存在见证语义，不能称为一般整数 Presburger
量词消去。它也不提供机器算术、安全指针观察或可执行 guard 的正确性。

## 接口与实际消费

[ProjectionASTGen](../theories/ProjectionASTGen.v)和
[ProjectionCodeGen](../theories/ProjectionCodeGen.v)把原生成器的投影服务变成
module 参数，保留原算法及其证明。它们保留原版权声明；这两个文件主要是已有
证明的参数化后继，不据行数主张新证明负担减少。
[ProjectionPreparedCodegen](../theories/ProjectionPreparedCodegen.v)复用原
`PrepareCodegen` 的维度准备和 source instance-list 对应，只重新连接依赖投影
服务的 raw／cleaned codegen 正确性。

实际常量源路线如下：

```
原 Clight 常量循环
  -> 原 source Loop／共同 schedule 坐标的 PolyLang
  -> 实际外部 phase、affine checker、tiling witness checker
  -> 新投影服务与 prepared codegen
  -> 既有 source-aware adaptation 和 final generated-Loop checker
  -> 既有 residual Clight lowering、private constant capture、公开出口恢复
  -> 当前完整程序的 selected host、后续既有 passes、CompCert backend
```

[GuardMemoryEqualityReducedPrepared](../adapters/compcert-memory/GuardMemoryEqualityReducedPrepared.v)
实例化新服务，保留 affine 和 tiled transition checker。最终候选仍经
`checked_double_shifted_tiling_choices` 检查；新增投影实现没有 extraction
semantic override。新的完整入口是
`ReducedLiteralCombinedDoubleCompiler.compile_selected_reduced_literal_combined_double_program`，
其 `_correct` 定理建立实际源程序 Csem→Asm backward simulation。后续 passes
消费本次变换后的真实程序。其他既有源路线的 codegen 尚未改为新投影。

## 验证责任与本阶段边界

| 层 | 本阶段责任 |
| --- | --- |
| Kernel | 既有局部 guarded correctness 与证书组合；无新增义务 |
| Domain 库／优化实例 | 投影契约、生成器正确性、实际 phase／candidate 验证、常量 source/model 对应和 static intervals |
| Language／host | 复用实际 I64/I32 conversion、private capture、frame、control/progress、placement、public exits 和完整程序安装 |
| 普通 C 使用者 | 输入标注的源程序和策略；不提供 semantic callback |

[证明摘要](equality-reduced-codegen.json)绑定十个后继模块、1,984 行和 19 个查询
端点，五个 closed，最大 42 项既有 globals，无新增 globals。数字包括已有证明的
参数化和重复接线，不是 kernel 或每实例人工负担的测量。失败的 proof attempts
与提前启动的 audit v1 均保留；全部模块完成编译后 audit v2 才通过。

证明／提取成功不等于修复原语料。原生构建、重点病例、actual tiling 和完整
语料结果必须各自绑定。OLO local obligations→compact entry condition→safe
machine check 与 accepted/refused state transport，仍需独立交付与成本验收。

## 重点原生重跑与实际执行

新 compiler 的 `fusion10`、`fusion2`、`nodep` 各三配置均完整输出匹配。前两者
`tiled` 分别约 3.10／1.99 秒完成；前序失败日志和完整语料结果保留。单次时间
不能建立受控的编译加速或运行收益。

最终 selected Clight 中，前两例各有八个 `for`、最大嵌套深度四，即分别分块的
两个原 nests。整体 source 的 raw codegen 已完成，但 `tiling-pipeline-1` 的
`tree-adaptation-refusal.txt` 记录 verified floor-membership service refused
unsupported bound。后续单 nest 候选实际安装；尚未安装整体 fused candidate。
该限制是下一具体功能 blocker，不能以独立 nests 的分块代替。

[新 nodep 执行观察](reduced-nodep-execution.json)在未改 assembly 上记录三个
配置各 400 次原 update，indices 2..401 各恰好一次。Tiled 中 `$ecx` 与 `$r11d`
分别在所有 update 处匹配 `(4*i+j)/32`、`i/32` 的整数 floor，覆盖 13 tile
组；完整输出在 debugger 内匹配。候选深度二／四、selected Clight 条件数
五／17；前序候选为十／72。第一次 observer 因 sandbox ptrace 被拒绝而保留，
第二次在允许 ptrace 的环境完成。两个版本的源码和 assembly 均未修改。

本常量路径没有动态 header／alias entry guard refusal；candidate membership
简化、compile-time static refusal、runtime versioning 是不同验收。

## 完整配置对照

[绑定结果](equality-reduced-codegen-results.json)覆盖全部 62 个原例、两个披露的
initializer adaptations 和三配置，共 192。186 个完整输出匹配：原例 180/186，
adaptations 6/6。原 `corcol3`、`pca` 的六个 frontend 拒绝保持；没有 compiler
timeout、native mismatch、link failure。每个 input hash 与前序完全相同，status
仅改变上述两个 tiled 编译失败。前序 184/192 和失败日志仍冻结保留。

完整输出匹配不等于全部配置的 requested transformation 已保留。Focused AST
检查与 nodep 的运行观察另行绑定；旧 shape counters 不计入新 literal 支持率。
一般多 piece／ISS、整体 fusion 候选 floor-bound 适配、原 CGO17 contexts／tiers、
compact entry 条件、完整成本和同例作者责任比较仍在 active goal。

验证记录：Rocq 编译／assumption audit、native build、重点和完整 replay、GDB
观察均完成。默认 staged whitespace check 列出两个继承生成器中的 17 行行末空白；
保留已经编译、审计与运行绑定的 source bytes。除行末空白之外的 staged whitespace
检查通过，不将这个格式检查描述成默认零警告。
