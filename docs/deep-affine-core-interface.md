# 深层片段使用通用有状态核心

`StatefulGuard.stateful_guard_preservation` 不解释整数、指针、循环域或候选算法。语言实例提供状态、命令、检查、观察，以及检查后执行所选命令的条件构造。编码器证明检查安全执行并保持实例指定的 frame；规则证明前提足以保持源观察。核心随后组合检查、候选与源回退。

[AffineNestFlagLanguage.v](../prototype/affine-nest/AffineNestFlagLanguage.v) 为真实 Clight 提供另一种条件形状：检查是 `(statement, expr)`，先执行语句，再从检查后的状态求布尔表达式；条件代码为 `Ssequence check (Sifthenelse condition candidate source)`。这与现有深层编译器的结果变量形状一致。状态是包含全局环境、局部环境、temporary map 与 CompCert 内存的 `clight_entry`；观察保留 live temporaries 和 `memory_equivalent` 的内存结果。

`affine_flag_guard_preservation` 从语言无关核心推导上述条件的观察保持。它用 source 的 scope 与写入范围证明 source observation 能跨越公开 frame 运输，不假设检查后的所有临时变量都与入口相同。

[AffineNestMultiRegion.v](../prototype/affine-nest/AffineNestMultiRegion.v) 中的 `affine_multi_stateful_execution` 提供具体编码器和局部证明。source 的正常执行建立检查域；数值检查与真实源足迹扫描产生私有结果变量，并保持公开状态和内存。前提在检查后状态携带一个入口 witness：它与当前状态保持公开 frame，且已证明的数学 guard 在该入口为真。候选证明使用原有受检域、依赖证书和实际机器 lowering；不会由框架重新解释地址或重新假设交换定律。

[AffineNestRegion.v](../prototype/affine-nest/AffineNestRegion.v) 的 `affine_single_stateful_execution` 使用同一核心。它的检查额外保持参数、根控制变量与公开变量构成的 frame；前提保留这份更大的 frame，以便复用单指针机器 lowering 的入口要求。

原来的 `affine_multi_guarded_region_sound` 与 `affine_guarded_region_sound` 现在调用对应的执行定理，将观察恢复为宿主需要的 `projected_region_contract`，再接入既有完整 Csem→Asm 定理。区域合同针对有限、静默、正常结束的受支持源片段；宿主另行证明源进展、外围控制流及程序级 simulation。仅有核心观察保持本身不能支持任意发散片段、非局部退出或任意 C 控制流。

这一轮调整单指针与多指针深层路径的证明，生成的检查与候选 AST 不变。旧矩形和标量路径仍有各自的语言实例与证明入口；不能因此声称所有路径已统一到同一个语法或同一套条件发现算法。审计覆盖该语言实例、区域执行定理及原完整程序端点；源端、区域端和完整程序端的全局假设分别保持原有的 6、14、42 项。本轮正式审计覆盖 104 个原型模块；最后的证明改动只涉及这一语言实例与两份区域证明。三套编译器重新提取后均与 `9c97b9b` 保存版逐字相同，并刷新为 715 个证明源码绑定，既有运行证据保持其原始报告，不改写历史验证数量。
