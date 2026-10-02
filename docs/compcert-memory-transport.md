# 等价内存与宿主执行的运输性质

PolCert 的 `CState.mem_eq` 使用双向 `Mem.extends`。它保证可观察的内存行为一致，不要求 CompCert 内存记录逐字段相同。为了将这类出口接到宿主，语言实例必须证明外围执行会保持所选关系。

`BilateralTransport.v` 提供两个不依赖具体语义的定理：

- `action_mutual_transport` 消费动作的单向模拟和确定性，以及观察改善关系的反对称性。两个输入状态相互扩展时，动作可产生相同的观察，并保持结果状态的双向关系。
- `observation_mutual_transport` 对 `S -> option O` 形式的观察，消费成功观察的单向运输与观察改善关系的反对称性。双向状态关系给出完全相同的 `Some` 或 `None` 结果。

核心不知道状态是内存，也不需要知道扩展关系怎样定义。两个定理没有全局公理。语言实例负责给出上述性质；不能把只在抽象 `State.eq` 意义上确定的指令，直接当作具有逐值、逐状态确定性。

`CompCertMemoryEquivalence.v` 将这个接口实例化为双向 `Mem.extends` 和 `Val.lessdef`。已证明普通 load/store、loadv/storev、字节 load/store、分配、释放及整组释放的运输。外部调用固定本次 trace 后，用 CompCert 的已有扩展兼容性和确定性性质，得到相同返回值、相同 trace 与等价的结果内存。这里继承了 CompCert 对外部函数和 inline assembly 的既有语义及性质假设。

`CompCertOperatorEquivalence.v` 使用 CompCert 已有的通用 injection 性质，将 cast、单目、二目运算及布尔解释的整个 `option` 结果证明为相等。双向内存关系保持 pointer validity 和 weak validity；因此指针比较和指针的布尔解释也被覆盖，无需把所有操作限制为无内存依赖的整数计算。

`ClightMemoryEquivalence.v` 提供真实 Clight 表达式、lvalue、bitfield、内存复制赋值、两种函数入口及条件树的运输性质。结果值、局部环境和 temps 保持精确一致；更新后的内存使用双向关系。

`ClightMemorySteps.v` 的 `memory_related_states` 保持代码、函数、continuation、局部环境与 temps 完全相同，仅放宽 memory。`step_memory_transport`、`star_memory_transport` 和 `plus_memory_transport` 已覆盖完整 Clight 小步关系及有限路径，包括函数调用、外部事件、分配释放、循环控制、switch 和 goto。这是具体语言提供的宿主运输性质。

`PolCertMemoryModel.v` 的 load/store 运输现在复用这个通用核及 CompCert 实例，继续使用真实 `CInstr/CState`，没有指令执行 oracle。

`ClightRegionRewriteProof` 已将这一性质用于区域宿主的入口、内部暂停和出口关系。`region_contract` 与 `encoded_region_rule` 现在允许候选产生双向扩展等价的最终 memory；该关系保持到下一次区域、调用和返回，并已组成完整 Csem→Asm 编译定理。现有规则使用等价关系的自反性，继续保留原执行行为。

全部 temps 仍要求精确一致。private temporary/live frame 以及包含循环的源区域还需要独立证明；真实 PolCert 优化器也尚未成为原生编译入口。因此不能据此称完整多面体优化已进入 C→Asm。
