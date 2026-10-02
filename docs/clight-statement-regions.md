# 从局部语句证书到完整 Clight 程序

`ClightRegionRewriteProof.transform_program_correct` 将条件语句片段替换接到真实 Clight 小步语义；`RegionCompiler.compile_property_regions_correct` 将它组合进实际 Csem→Asm backward simulation。共享宿主不检查优化使用了哪种语义性质。

作者接口是 `ClightRegionRule.encoded_region_rule source candidate`。语言实例提供性质维度、检查原语和前提公式，作者证明源片段的定义执行建立检查的入口域，以及前提成立时候选片段产生同一最终 temps、memory 和正常出口。共享合成器生成短路条件树，unknown 和拒绝都进入原片段。`encoded_region_rule_sound` 提供宿主需要的局部小步证书。

宿主目前接受由 `Sskip`、`Sassign`、`Sset`、`Ssequence` 和 `Sifthenelse` 组成的源区域，拒绝单独的 `Sskip` 替换位置和带 label 的候选。完整函数的其他部分仍可以有循环、调用、外部事件、switch、label 和 goto。区域内不能有调用、break、return、goto 或循环；这是当前证明使用的有限静默区域类，不代表框架可以替换任意 Clight 语句。

组合证明不把整个区域当作一个假定完成的原子步骤。它记录源区域的内部 continuation 和已执行前缀，暂时将目标保留在区域入口，并证明源的每个内部步骤严格减少剩余语句工作的自然数度量。源区域正常结束时，前缀证书重建完整局部执行，局部正确性证书运行目标到对应出口。这个严格下降排除无限的模拟停顿，因此外围程序的发散也包含在完整小步模拟中。遇到源的未定义执行不会产生额外的 guard 入口假设。

当前宿主要求最终 memory 和全部 temps 精确相等，并且不扩展函数的 `fn_temps`。PolCert 数组桥接提供 mutual `Mem.extends` 和 live-frame 关系；将这一关系接入完整程序仍需进一步的宿主运输证明。这里的有限区域宿主也尚未覆盖 PolCert 的计数循环。

`ClightRedundantSet.v` 提供一个具体规则：

```c
result = x + 1U < x;
x = 7U;
```

入口检查 `x == 7U` 成立时，只执行第一条；否则执行原区域。读 `x` 的源计算建立 guard 所需的整数入口域。证明不能默认所有 Clight temporaries 都含已定义整数：如果省掉读操作而直接测试任意被覆盖的临时变量，会引入源没有的失败。

该规则通过 `register_dimension`、`register_primitives` 和 `Fact tt` 合成条件树，并保留原始语句 AST 作为 fallback。`ClightStraightLine.v` 证明忽略空语句和序列结合方式的识别对应实际正常执行，适配 CompCert 前端产生的嵌套 `Ssequence`。规则拒绝两个临时变量重合，以及不符合类型和表达式形状的输入。它是完整语句接入的执行示例，不作性能收益主张。

复现入口为 `make check-integration`；实际提取入口改为 `RegionCompiler.compile_property_regions`，继续组合既有表达式和分支规则。Rocq 定理以形式化 Csem 和 Asm 为端点，原生 C 文件另经过 CompCert 的既有解析、打印、汇编和链接工具边界。
