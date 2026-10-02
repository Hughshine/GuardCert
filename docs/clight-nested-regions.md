# 直接基于 Clight 的嵌套循环区域

新的源进展路径直接使用 CompCert 的 statement、temporaries、内存和真实小步关系。它不经过 CInstr，也不要求源程序与 PolCert 的状态模型相同。

`ClightFragmentProgress.v` 的 `framed_progress source protected` 给出一个可以立即完成的片段协议、当前 temps/memory view、入口工作量上界，以及每一步保持指定 temporary 集合的证明。这个上界只计算片段内部步骤，与外围 continuation 无关；`Sskip` 可以作为一个已经完成的组件。

`ClightSequenceProgress.v` 合成两个片段的协议。在左片段完成后，对应真实的 `step_skip_seq`，再进入右片段；完成性质重建真实的顺序执行。`ClightNestedProgress.v` 与 `ClightNestedFrontendProgress.v` 将 body 的不透明协议装入严格 signed32 循环。语言实例证明 body 保留外层计数器和边界，循环自己更新计数器，并向外提供新的 frame 与步数上界。这使内层循环可以修改自己的计数器，同时保留外层控制所需的 temps。

通用 `SilentRegionProtocol.v` 不解释这些值、AST 或内存。外层协议消费小步覆盖、frame 和下降性质；具体 Clight 实例承担循环规则及机器整数证明。步数上界是证明中的度量，提取的编译器不运行它，也没有据此声称机器时间复杂度。

## 语法识别与完整程序接口

`ClightStructuredProgress.v` 从源 AST 生成可复用的协议存在性证据。它支持有限结构化片段的非受保护 temporary 更新、顺序组合，以及 canonical／真实前端包装的嵌套严格循环。循环检查核对整个 AST、signed 类型、步长、不同计数器和边界；body 检查保护外层计数器与边界。递归证书构造使用 AST 大小作为 fuel，不限制运行时迭代次数。

默认 `AdaptiveRegionCompiler.compile_progress_regions` 已消费这个识别器，继续使用已有区域宿主、性质编码与条件合成。完整 Csem→Asm 定理覆盖外围调用、事件、循环、switch 和 goto。新增区域仍是静默、无 label、正常出口的结构；卡住的非法访问并不会被进展协议变成合法执行。

基本运行时规则在入口比较为假时跳过整个循环。它只读取外层计数器和边界，源执行建立该检查的定义性。候选证书与源进展证书保持分离；[新的矩阵实例](native-matrix-interchange.md) 复用同一宿主实现带动态检查的 2×2 循环交换，并在外层条件接受后才读取内层边界。一般调度和 tiling 尚未实现。

## 实际检查

`ClightNestedProgressExamples.v` 证明两层、三层、混合 AST 形状和非受保护 temporary 更新可被接受；修改外层计数器、外层边界、内层计数器及复用计数器被拒绝。完整嵌套循环的 AST 替换也通过计算证明。

`native_nested_regions.c` 使用提取后的实际 C→Asm 编译器，验证普通、goto、外围循环、指针和数组五个完整外层循环的 guard。七组输入包含 signed 最大／最小边界、负值、正迭代以及内层／外层零次迭代。输出核对迭代次数、内层计数器最终值和实际数组写入；空指针 body 在零次路径上安全；两种外层 frame 违例不被替换。

```sh
make check-integration
```

原生报告为 `build/native-nested-regions/report.json`，协议及完整程序假设审计为 `build/region-protocol-report.json`。其中 `nested_array` 现在选择矩阵交换检查，其余四处仍是零次迭代检查。完整编译器端点仍只继承 CompCert 的 35 项基线假设。没有性能测量或原生 PolOpt 调用；调度变换只覆盖单独文档限定的模板。
