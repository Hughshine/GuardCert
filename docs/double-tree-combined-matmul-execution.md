# 原始 matmul：实际分块路径与完整调用诊断

本阶段核对组合 compiler 的一个实际变换路径，避免把安装计数当成分块支持。
输入是保存的原始 matmul，保留 IEEE double 表达式、三个 96 循环维度及实际
数组计算。使用同一已证明的
`CombinedDoubleTreeResidualCompiler.compile_selected_combined_residual_double_program`
及其 Csem→Asm correctness endpoint，没有新增 compiler 或语义假设。

[固定摘要](double-tree-combined-matmul-execution.json)绑定原语料报告、assembly、
native binaries、observer 和成本 helper。它与完整语料中的 186/192 输出匹配
计数是不同层次的证据，没有重定义整个 corpus 的变换支持数量。

## 已观察的路径

Observer 重新链接未改动的保存 assembly，保留局部符号，用 GDB 在实际 point
loop 初始化指令上观察 tile entry。依次得到 `[0,2]^3` 的全部 27 个 tile triples，
tile 次序为 `i,k,j`，tile size 为 32。首次候选 update 的原坐标为 `i=j=k=0`，
GDB 运行中的完整输出匹配原保存结果。后者包含所有 modeled 数组／标量的摘要，
不是所有 C machine state 的穷尽观察。

目标未插入额外计数代码，也未修改 assembly。观察只计 tile entries 和首次
candidate update，没有计数全部 updates。原始常量 96 输入未测试 runtime guard
拒绝，动态输入和 fallback 保持其单独验收义务。

## 同 backend 的完整调用成本

新的可复现 helper 使用完整 corpus 保存的三个原始 binaries；源码和数值计算
保持。七个 batches 各随机排序 unmarked、untiled、tiled，共 21 次调用，全部
输出匹配原 GCC reference。子进程 CPU 包括启动、初始化、kernel、digest 和
printing，没有 CPU pinning；只测 target child，不计 corpus 绑定审计开销。

| 配置 | 进程 CPU median，ms | 每个 batch 相对 unmarked 的 ratio median |
| --- | ---: | ---: |
| Unmarked source，经相同 CompCert backend | 6.088 | 1.000 |
| Untiled | 4.765 | 0.783 |
| Tiled | 5.244 | 0.820 |

这是当前常量 96 tier 的小样本诊断，不是隔离 guard 成本、受控 kernel-only
speedup 或跨程序／更大输入结论。早先未保存 helper 快照的 21 次 one-off 诊断
也被绑定保留，ratios 约 0.740／0.784；本文数字取自上述新 helper，不能混合
两组样本或抹掉差异。

复现使用已有 frozen corpus，另起一个 attempt 保存所有输出和 helper 快照：

```sh
python3 scripts/measure_combined_original_matmul.py --attempt new-attempt
python3 scripts/summarize_combined_matmul_execution.py --validate
```

Source/model、candidate correctness 与 host 安装仍来自既有 compiler 证明，
机器观察补充这个原例实际路径的证据。接下来继续逐配置核对 retained
transformations、动态接受／拒绝、缺失源族和 sequential phases；OLO compact
condition、接受域与完整成本，以及原 CGO17 程序仍是独立验收目标。
