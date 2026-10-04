# 多轴仿射边界扫描

这是对[多轴活动访问扫描](memory-multi-axis-alias-scans.md)的算法替换。候选仍须通过同一域与依赖检查；检查接受后建立的 NonAlias 前提、完整访问分离布尔结果和局部候选契约都保持相同。

## 从重叠见证到边界坐标

设两个地址使用相同系数向量 `a`、不同 bias 和基址：

```text
A(i) = (base_A + 4 * (dot(a,i) + bias_A)) mod modulus
B(j) = (base_B + 4 * (dot(a,j) + bias_B)) mod modulus
```

各轴坐标属于同一活动矩形。对每一轴减去 `min(i_k,j_k)`，两侧新坐标都仍在矩形中，且至少一侧为零。两侧地址偏移减去同一个量，因此 `A(i)=B(j)` 推出新的边界地址也相等。

用一个 bool mask 决定每轴哪侧保留非零坐标，另一侧取零，便能覆盖所有这类重叠见证。生成每个 mask 的实际私有矩形扫描。任意 mask 中的两侧坐标又都是源矩形中的坐标，所以原完整扫描为真时，全部边界比较也为真。

这证明了在源地址能力成立时，两种检查的布尔结果相同。证明覆盖机器指针偏移的取模语义，不要求不同 block 的地址可以进行大小比较；查询仍只使用源实际活动的有效、对齐单元。

## 实际代码与证明接口

- [GuardMemoryAxisBoundaryMath.v](../adapters/compcert-memory/GuardMemoryAxisBoundaryMath.v) 提供差坐标、mask 完备性、取模平移和数学检查充分性。
- [GuardMemoryAxisBoundaryCells.v](../adapters/compcert-memory/GuardMemoryAxisBoundaryCells.v) 连接实际 CompCert 位置，证明 `memory_affine_axis_boundary_pair_exact`。
- [重复重命名](../adapters/compcert-memory/GuardMemoryAxisRepeatedRenaming.v)、[实际地址](../adapters/compcert-memory/GuardMemoryAxisRepeatedAddress.v)及[坐标名字](../adapters/compcert-memory/GuardMemoryAxisBoundaryNames.v)允许多个轴共用一个私有零值，同时保留实际机器表达式求值证明。
- [实际比较](../adapters/compcert-memory/GuardMemoryAxisBoundaryTest.v)、[单面扫描](../adapters/compcert-memory/GuardMemoryAxisBoundaryScan.v)、[各面组合](../adapters/compcert-memory/GuardMemoryAxisBoundaryMasks.v)及[完整访问对](../adapters/compcert-memory/GuardMemoryAxisBoundaryPair.v)证明正常 Clight 执行、检查结果、完整内存与公共 temporary 保持。
- [GuardMemoryAxisPairChoice.v](../adapters/compcert-memory/GuardMemoryAxisPairChoice.v) 根据两个已编码地址的完整系数向量选择算法。不同向量继续调用旧完整扫描；选择定理提供原访问对执行接口。

边界算法复用现有私有池中的一个计数器作为零值，不增加新的声明要求。当前源包、公共状态关系、次数条件、候选检查与 `projected_region_contract` 没有改变。统一 Csem→Asm 路径消费新的实际执行定理。

这提供了同一前提的两个可替换编码算法。通用有状态核心不解释这些地址；具体语言实例提供执行和状态运输证明，候选继续消费既有前提。

## 成本和限制

设维数为 `d`、活动点数为 `P`。单个原始跨指针访问对的完整扫描执行 `P²` 次比较，边界算法执行 `2^d * P` 次。维数固定时，后者关于活动点数线性；代码包含 `2^d` 个矩形扫描，因此随维数增长。

小矩形可能执行更多比较。当前选择依赖静态系数向量，没有按运行时活动点数选择算法，也没有对 mask 去重或在标志为假时提前结束。原始访问对仍可能重复。不能由这个渐近界直接推出每次调用更快。

原生驱动的双向私有池检查仍限制这条路线最多七轴；此算法未因此扩大原生可接受深度。共同 cap、逻辑窗口 1024、原始访问预算 32、规范矩形源以及地址参数的限制也保持相同。放宽只读别名仍需要扩展候选使用的内存性质。

## 本阶段验证

以下数字绑定 `21d17fe` 阶段的 `f49df2…` 编译器及当时的 469 个证明源码。后续[逐轴范围条件](memory-per-axis-bounds.md)已接入 340 模块的完整审计；普通候选仍使用本节算法。测试目录可能随当前编译器重新验证而覆盖，请以报告中的 compiler／source SHA-256 区分证据。

2026-10-03：320 个适配模块、七个 lowering 模块及两个有状态核心模块全量审计通过，469 个证明源码哈希一致；指令桥、validator、完整编译器分别保持既有 7／12／42 项假设，没有新增全局公理。边界数学充分性、mask 范围、实际单元检查的布尔等价没有全局公理。统一编译器已提取并重建为 SHA-256 `f49df2ba998d50fa1b6affbf2dbcb5c1c412076583508ece571f94cedca8cd9e`。多轴源的 14 组配置共 4270 次完整汇编调用、11 组共 2135 次精确分支／查询计数诊断通过；与旧编译器的源码哈希、guard cap、618 次快路与 1517 次回退逐配置一致。

`make native-memory-axis-alias` 将在审计及提取之后执行完整汇编和精确查询次数诊断。诊断分别计算完整扫描和边界扫描的查询次数，并要求与实际插桩结果逐调用相等。

旧版 `3e14333` 的已审计编译器快照保存了同一 C 源的 14 组完整配置及 11 组精确分支诊断。比较入口为：

```sh
python3 scripts/compare_memory_axis_scans.py --baseline /tmp/guard-axis-verified
```

该命令要求已有相应基线快照，核对源码哈希、编译器身份、guard 上界、实际候选／回退及逐配置查询数。报告写入 `build/native-memory-axis-boundary/comparison-report.json`。完整 CompCert 汇编、加标记 Clight 查询次数与执行时间分别看待；没有执行时间声明。

实测地址比较总数为 `35,537,690 → 854,960`，仅适用于该相同源码与配置集合。部分源序样本如下：

| 实际源调用 | 旧完整扫描 | 新边界扫描 |
| --- | ---: | ---: |
| 二维复制 `16×16` | 131072 | 2048 |
| 二维复制 `61×1` | 7442 | 488 |
| 二维复制链 `9×9` | 78732 | 3888 |
| 三维复制 `15×1×1` | 450 | 240 |
| 四维复制 `7×1×1×1` | 98 | 224 |

小输入的恶化已保留在报告中。完整 C 源的代码体积也增加：二维源序 Clight／汇编分别为 `31721 → 45141`／`31284 → 45197` bytes；四维源序分别为 `20734 → 47940`／`22961 → 41270` bytes；生成源序同时处理五个函数的汇编为 `41075 → 79477` bytes。这些文件大小与查询次数都不是运行时间测量。

`make native-memory-axis-pair-choice`（脚本 `scripts/native_memory_axis_pair_choice_paths.py`）另用 14 次实际 Clight 调用核对同向 `multi_copy` 与反向 `multi_reflected`：前者执行 `8P` 次，后者执行 `2P²` 次；范围拒绝和外层为空时查询为零。独立模型同时核对完整数组和公开循环变量，相关完整汇编由 multi-pointer 全套覆盖。

同一新编译器还通过 multi-pointer、一般一维仿射、端点及逐元素四套完整汇编与分支回归。加上多轴套件为 12922 次完整汇编调用和 10321 次既有分支诊断；上述 14 次算法选择诊断另计。私有扫描、完整源解码、候选验证和程序上下文同时进入实际提取路线。

指针、稳定 RHS 标量、signed 地址及源元数据另有 15 组选择性完整汇编配置通过；这些报告与五套完整回归都绑定同一 `f49df2…` 编译器哈希。
