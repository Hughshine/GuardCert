# PolCert 接入目标与当前缺口

2026-10-02。用户要求将真实 PolCert 多面体优化器通过 guarded transformation 框架接入 CompCert，并获得完整 C 程序到汇编的行为保证。当前尚未完成这项集成。

## 所需链路

```text
完整 C 程序
  → Clight 源片段识别与检查
  → 在入口前提下对应真实 PolCert Loop
  → 实际 PolCert 优化器产生候选 Loop
  → 机器算术、内存与出口要求的条件编码及安全检查
  → 候选 Loop 重建为 Clight，失败路径执行原片段
  → CompCert 后端与完整 Csem→Asm 正确性
```

语言实例提供整数、内存、访问与交换性质。框架组合检查和证明，不把这些性质默认为成立。支持的片段与前提表达子集必须明确；从给定前提生成检查，与从任意源／候选发现前提，分别报告。

## 已有组件与缺口

| 部分 | 当前状态 | 接入所需工作 |
| --- | --- | --- |
| 实际优化器及端点 | `PolCertOptimizer.optimize_version` 在 Loop 层调用 `Core.Opt_prepared` 并复用其正确性 | 在原生 C 编译流程中调用，保留成功／拒绝语义 |
| 完整程序组合 | `PolCertOptimizerRegion.compile_optimizer_result_correct` 有参数化 Csem→Asm 定理 | 提供具体可执行实例，闭合 bridge 的所有证明字段 |
| 状态与参数入口 | 新 CInstr 只读参数实例有非空数组和真实内存执行见证 | 使用同一实例构造 POLIRS、优化器、源解码与候选编码，避免模块类型错配 |
| 源解码 | bridge 中仍是 `optimizer_decode` 字段 | 从实际源 Clight 执行建立原始 Loop 执行及内存 view |
| 候选进展 | bridge 中仍是 `optimizer_candidate_progress` 字段 | 证明接受前提下候选可执行；后向优化器端点不能单独提供这一性质 |
| 候选重建 | 已有仿射、嵌套 Loop→Clight lowering 与 raw CInstr 数组实例 | 接入同一优化器语言实例，绑定实际输出，补齐目标运算与公共／私有 temporaries |
| 原生运行 | 直接 Clight 矩阵与 CInstr 双写样例可运行 | 运行实际优化器产生的循环候选及 guard 快路／回退路径 |

锁定 CInstr 的旧 `CState.valid` 在非空声明下不可满足，已有机械化审计。新语言实例需要真实入口与执行见证；该问题不改变集成目标。上游工作区保持只读，适配和兼容变更在 GuardCert 内记录。

## 首个接入实例的验收

1. 输入是含数组循环及周围代码的实际 C 程序；编译时真实调用 PolCert，并记录输入和输出 Loop。
2. 至少一个接受输入产生非恒等的循环候选；候选来源是优化器实际返回值。
3. 检查成立运行候选，检查不成立保留原循环；拒绝或不支持的输出不能进入快路。
4. 源解码、候选进展、候选编码与出口对应均有具体证明，完整程序定理不把它们留作未实例化字段。
5. 实际提取的编译器生成可运行汇编，验证快路、回退及外围可观察结果；报告准确的片段范围和假设。

`compile_scheduled_regions` 的固定四点调度以及真实 CInstr 的双写交换，保留为检查和组合机制的回归实例。它们不能单独满足以上验收。
