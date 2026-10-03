# 优化器端点到完整程序的证书接口

`PolCertOptimizerRegion.v` 提供参数化的完整 Csem→Asm 定理，直接消费真实 `PolOptCorrect.Opt_prepared_correct`。它接通了证明接口；尚未实例化完整循环证书，也没有在原生 C 驱动中调用 impure 优化器。

`optimizer_loop_bridge source original optimized` 将源 Clight AST、原始 Loop IR 和候选 Loop IR 绑定起来。具体语言实例需要提供：

- 源区域的真实小步进展协议与入口检查域；入口域必须由实际源执行建立。
- 性质维度、可执行检查原语与公式；公式接受蕴含变换所需前提。
- 在接受前提下，将实际源执行解码为原始 Loop 执行；拒绝路径直接执行源 Clight。
- 原始 Loop 结果在 `State.eq` 下唯一，以及候选 Loop 的终止执行存在性。
- 将候选 Loop 执行编码为实际候选 Clight 执行，保持公共 temporaries。
- 数学结果的内存 view；等价结果的物理内存必须双向 `Mem.extends`。

`optimized_loop_preservation` 使用通用 `endpoint_refinement_to_preservation`，结合实际优化器的后向端点、源结果唯一性和候选进展，得到前向条件保持。之后 `actual_optimizer_region_rule` 复用性质公式合成、真实 Clight 检查代码和区域宿主。`compile_optimizer_result_correct` 给出完整程序的 backward simulation。

选择器核对整个源 AST，而不是仅核对一个标签；`optimizer_source_is_selected` 证明证书对应的源区域确实被选择。证书不能被用于另一个源片段。

## 保证与边界

这是一个有实际端点支撑的证书构造，不是无条件的优化器集成。候选进展、源解码、固定宽度算术和出口 frame 是必须证明的字段，不是默认成立的事实。尤其是上游目标终止执行到源执行的定理，不能独自保证候选会执行或终止。

当前内存出口允许双向 `Mem.extends`；公共 temporary 出口必须相同。此接口尚不支持新增 private temporary 的函数声明与状态投影。没有声称支持所有 tiling 输出。

假设审计要求新增完整程序端点的假设集合恰好等于实际优化器端点与 CompCert 编译器端点的并集：42 项、35 项及其 75 项并集。没有增加全局公理。报告为 `build/polcert-optimizer-region-adapter-report.json`。

```sh
make polcert-optimizer-proof POLCERT_SOURCE=/path/to/verified-compilation-v10-driver
```

后续主线是实例化这些义务，并在原生 C 驱动中实际调用 PolCert 优化器，见 [接入目标](polcert-integration-target.md)。具体语言实例可以调整状态表示，但必须使用真实 PolCert 算法与正确性端点；直接实现矩阵调度不能代替这项接入。
