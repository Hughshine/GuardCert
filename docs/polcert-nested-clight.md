# 实际 Loop 的嵌套循环与 temporary frame

`PolCertNestedClight.v` 使用同一真实 `InstrTy.INSTR`／`Loop` 和基本指令插件，将 `Instr/Seq/Guard/Loop` 递归编译为实际 Clight。调用者提供每层一对 iterator/bound；支持的深度由这个 scratch pool 限制，池不足时拒绝。顺序片段复用同一个池。

这一步仍使用已证明的区间分析与入口 range guard。仿射边界和操作数的中间结果均须通过分析；除法、取模、min/max 目前不支持，因此还不能覆盖实际 tiling 生成器的全部输出。

`compile_nested_raw` 和 `checked_compile_nested_raw` 只接收一个指令翻译函数，没有运行时语义参数。已有带证书接口调用同一个纯翻译函数，`checked_compile_nested_raw_agrees` 证明两种入口一致。具体的 [CInstr 数组实例](polcert-array-clight.md) 已供给指令执行证书。

## 公共与私有 temporaries

旧单层接口要求 body 保留所有 temporaries。嵌套循环会更新内部 iterator/bound，因此递归接口改为保护参数 layout、外层计数器和调用者声明的 live frame。基本指令插件仍保留 temporaries，只通过内存 view 修改状态。

`ClightTempFrame.v` 定义 `temp_agree live before after`，并证明受限结构化代码只改变指定 temporaries。`ClightFramedLoop.v` 的计数循环允许 body 改变自己的 scratch，要求每次迭代返回时保留当前 iterator/bound 和公共 frame。公共参数与入口快照的对应沿各次迭代保持，供内层仿射表达式求值使用。

`scratch_check` 在编译时核对整个池：没有重复标识符，也不与 layout／live frame 冲突。`checked_compile_nested_correct` 组合这个检查与 range guard，并证明最终 `temp_agree (layout ++ live)`。内层输出不要求恢复 scratch 的旧值。

完整程序宿主仍须证明提供的 live 集合覆盖外围读取，并将私有标识符加入实际函数的 temporary 声明。当前检查不能自行发现任意 continuation 的所有读取，也没有隐含一个已验证的 liveness 分析。

## 已证明的端点

`compile_nested_correct` 将每次真实 Loop 执行变为正常、无迹的 Clight 执行，保持源／目标内存 view 和公共 temporary frame。证明支持嵌套、顺序复用和 guards。

`checked_compile_nested_steps` 将该结果提升为实际 Clight 的 `star`：可处于任意函数和 continuation，结束于同一函数／continuation 的 `Sskip`，且保留公共 frame。这个定理是 Loop→Clight 的片段 lowering 端点；它本身不是源 Clight region→候选 Clight region 的完整程序 simulation。

编译证明中的例子包含内层上界依赖外层 iterator 的两层循环，以及 live temporary 冲突、重复 scratch、深度不足三种拒绝。例子调用实际算法并通过 `vm_compute`。

```sh
make polcert-nested-proof POLCERT_SOURCE=/path/to/verified-compilation-v10-driver
```

报告为 `build/polcert-nested-report.json`，假设审计只允许继承 Clight statement／小步端点的假设及三个 `INSTR` 类型／语义字段。基本指令执行证书仍是显式参数。具体 C 指令与内存 view、源区域提取、候选进展、支持 tiling 边界运算和完整程序区域模拟仍需完成。
