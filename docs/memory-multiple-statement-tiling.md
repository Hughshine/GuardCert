# 多语句 tiling 的真实执行进展

`GuardMemoryTilingMultipleProgress.validated_memory_multiple_tiling_progress_at` 已把真实 tiling 验证器的接受结果连接到多条 PolyLang 语句的源到候选执行。这个端点保持具体入口参数、实际数组位置映射和完整 CompCert Mem，不假设候选进展，也不把这个义务留给调用者。

前提为参数数目与 context 相符、入口物理 nonalias，以及 `validate_memory_tiling_equivalence` 无 alarm 返回 true。源与候选具有相同的 context 和变量表；结构检查要求源点 witness 为 identity，逐语句 tiling witness 合法且块大小正。语句数量、深度、域、访问、指令和各自 witness 均由实际检查器绑定。结论是：给定源程序在这些具体参数和状态上的真实 PolyLang 执行，就能得到候选在同一参数和状态上的真实执行。

## 点对应和整个程序

`indexed_lift_before_shape` 为任意语句编号建立点提升与逆映射；编号始终保留。不能把单语句证明中的编号 `0` 直接套到整个程序。不同语句可以有各自的深度和合法 tiling witness。

`multiple_lift_shape` 与 `multiple_lift_project` 在整个语句表上证明双向对应。`multiple_lift_flatten` 构造有限的 retiled 点列表，证明完整域覆盖、唯一性和编号／点坐标排序。`before_to_retiled_multiple_progress` 保持原时间戳与每个点的真实指令执行，因此从整个源执行构造 retiled 执行。实际双向依赖检查再将 retiled 执行连接到候选调度。

这里的有限点列表只出现在证明中；提取的编译器不会枚举运行时迭代点。一般候选仍可以拒绝，包括保守依赖检查无法证明的有效候选。

## 验证结果和边界

提交 `6160c37` 的审计重编译二十三个具体内存模块和七个 lowering 模块。多语句正向端点的假设精确等于原 validator 的 12 项；完整编译器仍是 CompCert 与 validator 的并集 42 项，没有新增公理。

`build/native-memory-validator/report.json` 记录 35 组提案和 1309 组独立 32 位机器整数执行比较。新增接受项包括两条和三条存在读写依赖的连续更新、带仿射条件的多语句域以及超过域大小的稀疏块。生成错误语句顺序的候选被拒绝，并有独立执行反例；第二条语句的域损坏被结构检查拒绝。故障证书与资源耗尽测试继续通过。

这份独立 IR 报告运行实际提取的符号域与依赖检查器。它的执行比较不替代下面完整 C 程序的检查。

## 多语句完整 C 编译入口

`GuardMemorySequenceCompiler.compile_memory_sequence_regions bi bj` 已接通完整的 Csem→Asm backward simulation，定理为 `compile_memory_sequence_regions_correct`。接受要求仍是实际依赖验证无 alarm 且编译返回 `OK assembly`。

当前 C 输入范围是非空的纯写赋值语句列表、同一个普通定长数组、共同的 extent/stride 和规范双层动态矩形循环。每条语句可以有不同的 payload 系数和常量，也允许不同位置出现相同指令。`check_array_family` 重新检查完整 typed AST、循环协议、全部赋值、标识符及数组布局；不依赖不受信任识别器的判断。

`GuardMemorySequenceClight.array_family_source_clight_decode` 从真实源执行恢复整个逻辑循环及准确的行／列出口。数组绑定来自入口第一个实际赋值，不作为调用者提供的证明字段。`GuardMemoryIndexedTrace` 保留静态语句位置，即使指令相同也不会合并两个位置。

`GuardMemorySequencePolyhedral` 的源点为 `[N;M;i;j]`，源时间戳为 `[i;j;site]`；分块点为 `[N;M;ti;tj;i;j]`，时间戳为 `[ti;tj;i;j;site]`。`GuardMemorySequenceOrder` 证明实际循环轨迹顺序、完整点覆盖与唯一性，并构造符合 PolyLang 要求的编号／坐标排序。`GuardMemorySequenceExecution.validated_memory_sequence_tiling` 消费实际多语句 checker，得到源 Loop 执行到候选 Loop 执行，保持相同入口参数与完整 Mem。

`GuardMemoryArrayFamilyBackend` 将每条已绑定的纯写指令编码到真实数组赋值。它与原有嵌套循环 lowering 组合，生成四层循环、尾块条件和八个私有 signed32 temporary。`GuardMemorySequenceTiledClight` 恢复源程序可见的行／列出口，证明所有原 temporaries 一致和 Mem 精确相等；原有 guarded 区域宿主随后组合到完整程序。入口检查依然从实际布局得到 `i==0 && 0<N && N<=extent/stride && 0<M && M<=stride`，求值安全和原片段回退由同一条件框架保证。

2026-10-03 的新审计重编译 32 个内存适配模块和 7 个 lowering 模块。新增逻辑端点继承原 validator 的 12 项假设，完整编译器假设集合仍精确等于 CompCert 的 35 项与 validator 的 12 项的并集 42 项，没有新增公理。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_guard_memory.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/build_memory_compiler.py --sequences
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_memory_sequences.py
```

`build/native-memory-sequences/report.json` 已记录五组块大小（1×1、2×3、4×4、5×7、17×13）、4125 个正动态矩形和 8 个实际 guarded 函数。每组 1138 行完整输出与 GCC 和独立模型相同，逐元素检查数组、非零入口的源回退和公开计数器出口。实际 Clight 快路检查四层循环及两／三／四条赋值的完整数量和顺序，重复指令的位置没有被合并。另检查两个数组布局、goto、全局数组、外层循环及外层零次执行时未读取未初始化内层边界。

非法块大小、辅助边界溢出、资源耗尽和错误证书这五条路线均拒绝候选并执行原程序。当前范围外的读改写、多数组、偏移写及临时变量赋值列表也在完整程序上验证了源回退。这里没有性能测量。

完整依赖目标为 `make native-memory-sequences`。本入口尚未支持多数组、读改写列表、条件域中的多语句、一般嵌套仿射边界或任意外部调度。前面的 PolyLang 多语句进展定理比这个 C 识别器更广。
