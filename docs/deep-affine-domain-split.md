深层仿射候选可通过 `AffineSplitEvidence conditions steps positions` 描述域切分。`conditions` 是切面测试列表，`steps` 提议候选坐标如何映回源，`positions` 提议候选静态站点如何恢复源展开后的排列。所有这些内容都是待检查的数据。

这条路径先证明一个保持源执行顺序的展开，再验证候选是否可以改变顺序。对源叶子 `S` 与切面 `P`，展开为：

```text
sequence {
  guard P     { S }
  guard not P { S }
}
```

`affine_split_pair_execution` 在实际 Loop 语义中证明该展开与 `S` 等价：每次入口恰好选择一份。`affine_partitioned_source_execution` 把展开放在所有原循环头之内，保持每个源点的相对顺序。`affine_partitioned_sources_execution` 对有限切面列表迭代此构造；两切面得到四种完整符号组合。数学证明支持任意有限列表，当前 native 数据接口限制最多两个切面。

实际展开将 `a≤b` 的互补条件正规化为整数半空间 `b+1≤a`，而非保留提取器不支持的否定节点。`affine_complement_test_value` 证明其 Bool 求值等于原测试取反。其他测试的数学互补保持 `not`；不能由现有提取器表达的展开拒绝。候选机器 lowering 还须证明 `b+1` 等运算安全，数学等价不会绕过机器范围检查。

候选可以把各部分移入独立循环。`checked_affine_split_candidate` 将已证明完整的源展开与候选交给现有域、站点与依赖检查器。`checked_affine_split_candidate_correct` 最终返回原源 Loop 的 `memory_bounded_source_certificate`，因此后续守卫编码、实际内存候选执行、源公开出口和 Csem→Asm 组合无需更换契约。

这分别核对两个问题：源展开覆盖每个原点一次；候选对这些点采用的新顺序保持依赖。漏片或重复片会破坏静态站点／域对应。完整的反序切分也可能破坏依赖，并非只要覆盖完整就允许任意顺序。

外部数据格式为：

```text
(split-domain
  ((le (var 1) (constant 0)))
  candidate)
```

测试在原叶子坐标环境中解释，内层游标先于外层游标。外部工具可在 `candidate` 内使用已有 `map-index` 或 `site-order` 描述。切面测试的数学求值是纯的；候选的真实机器检查和 lowering 仍必须通过范围及语法验证。不被提取器或后端支持的测试安全拒绝。

`external_affine_candidate.py` 提供 `split-one`、`split-two`、`split-reverse`、`split-drop` 和 `split-duplicate` 数据产生模式。它重用实际源循环与指令，但不受信任。`native_affine_nest_domain_split.py` 使用含真实 producer/consumer 与未来迭代读取的二层、三层程序；独立 Word 模型为两切面重排、反序、缺片和重复片提供具体行为反例，实际编译器负责拒绝危险候选并保留原程序。

这是以 PolCert 的 ISS 基本功能为参照的一条重实现路线。它连接实际 CompCert 源与候选、运行时前提及完整程序，不声称复制了现有 PolCert 的 witness 格式，也不据此提出新的文献贡献。

提交 `a4f40b4`（2026-10-04）验证：完整 affine audit 编译 100 个模块，编译器 stamp 记录 711 份证明源和 8 份 native 源。半空间互补定理无假设；源执行、检查器和整程序定理沿用各自已有假设，未引入新的全局公理，整程序审计仍为原有 42 条。

七种配置各运行 492 次，合计 **3,444 次实际 CompCert 汇编调用**，完整数组和公开循环出口与独立 Word 模型一致。identity 和单切面接受全部四个函数；双切面及反序接受两个独立函数和逐点依赖函数，拒绝未来迭代依赖函数。缺片、重复片和资源限制配置均不安装候选。实际汇编验证包括守卫外输入、重叠地址和源不执行数组访问的路径。

单独对发出的 Clight 插桩并用 GCC 运行 **1,722 次**，观察到 **288 次候选、1,434 次原片段回退**；其中包括 184 次同一存储块上的不相交地址快路径和 232 次数值检查成功但实际地址重叠的回退。这项诊断只观察分支，不替代实际汇编验证。

同一统一编译器版本的完整回归共 **18,750 次汇编调用、9,185 次 Clight 分支诊断**；条件搜索入口另有 **10,212 次汇编调用、5,181 次诊断**。两份编译器分别固定并保存哈希，不将不同二进制的调用数合成一个编译器的覆盖。该阶段的域切分尚不支持与分块证据组合；没有性能提速结论。
