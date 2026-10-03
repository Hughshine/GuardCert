# 多语句 tiling 的真实执行进展

`GuardMemoryTilingMultipleProgress.validated_memory_multiple_tiling_progress_at` 已把真实 tiling 验证器的接受结果连接到多条 PolyLang 语句的源到候选执行。这个端点保持具体入口参数、实际数组位置映射和完整 CompCert Mem，不假设候选进展，也不把这个义务留给调用者。

前提为参数数目与 context 相符、入口物理 nonalias，以及 `validate_memory_tiling_equivalence` 无 alarm 返回 true。源与候选具有相同的 context 和变量表；结构检查要求源点 witness 为 identity，逐语句 tiling witness 合法且块大小正。语句数量、深度、域、访问、指令和各自 witness 均由实际检查器绑定。结论是：给定源程序在这些具体参数和状态上的真实 PolyLang 执行，就能得到候选在同一参数和状态上的真实执行。

## 点对应和整个程序

`indexed_lift_before_shape` 为任意语句编号建立点提升与逆映射；编号始终保留。不能把单语句证明中的编号 `0` 直接套到整个程序。不同语句可以有各自的深度和合法 tiling witness。

`multiple_lift_shape` 与 `multiple_lift_project` 在整个语句表上证明双向对应。`multiple_lift_flatten` 构造有限的 retiled 点列表，证明完整域覆盖、唯一性和编号／点坐标排序。`before_to_retiled_multiple_progress` 保持原时间戳与每个点的真实指令执行，因此从整个源执行构造 retiled 执行。实际双向依赖检查再将 retiled 执行连接到候选调度。

这里的有限点列表只出现在证明中；提取的编译器不会枚举运行时迭代点。一般候选仍可以拒绝，包括保守依赖检查无法证明的有效候选。

## 验证结果和边界

2026-10-03 的完整审计重编译二十三个具体内存模块和七个 lowering 模块。多语句正向端点的假设精确等于原 validator 的 12 项；完整编译器仍是 CompCert 与 validator 的并集 42 项，没有新增公理。

`build/native-memory-validator/report.json` 记录 35 组提案和 1309 组独立 32 位机器整数执行比较。新增接受项包括两条和三条存在读写依赖的连续更新、带仿射条件的多语句域以及超过域大小的稀疏块。生成错误语句顺序的候选被拒绝，并有独立执行反例；第二条语句的域损坏被结构检查拒绝。故障证书与资源耗尽测试继续通过。

原生运行的是实际提取的符号域与依赖检查器。这一节不声称已经有多语句完整 C 源提取、候选 Clight 编码或新的 C→Asm 多语句编译入口；那些具体桥接仍在实现。已有单语句矩形和仿射条件域的完整 C 分块路径单独记录。
