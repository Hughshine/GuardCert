# 多个条件方案与语言接口

同一个源片段可以有多个充分条件及候选。框架按顺序执行条件检查，选择第一个通过的候选；全部失败时执行原片段。不同方案不必有相同的前提、检查定义域或状态关系，但必须保留同一源片段的观察结果。

## 抽象核心暴露的接口

`theories/StatefulGuardVersions.v` 的 `stateful_verified_version language source` 接收以下证据：

| 字段 | 语言实例提供的内容 |
| --- | --- |
| `version_domain` | 检查可执行所需的状态性质 |
| `version_presumption` | 候选成立的语义前提 |
| `version_frame` | 检查前后状态之间允许的变化 |
| `version_encoding` | 在定义域内检查能够执行，产生 bool 和后状态；满足 frame；接受推出后状态上的前提 |
| `version_source_domain` | 正常源执行提供检查定义域的证据 |
| `version_source_transport` | 在 frame 允许的变化后，原片段仍能执行并产生同一观察 |
| `version_candidate_preservation` | 前提成立时，候选保留原片段的观察结果 |

语言提供命令、检查及各自执行关系，以及条件选择的构造和执行证明。核心不知道整数、指针、NonAlias、访问交换或 overflow flag 的含义。例如 NonAlias 足以交换哪些操作，应由具体语言的性质库和候选规则证明；核心仅消费该规则。若语言状态包含 overflow flag，语言实例还需证明检查如何读取或更新它、这些变化属于哪种 frame，以及所得到的前提足以支持候选。

`stateful_versioned_command` 构造有限方案列表。`stateful_versions_preservation` 证明：原片段产生某个观察时，该方案列表也能产生同一观察。这个核心定理没有全局公理。前一个检查失败后，通过 source transport 获得检查后状态中的正常源执行，下一方案再由自己的 source-domain 证明推导定义域；不要求不同方案共用一种抽象不变量。

核心只要求接受可靠。False 不必意味着前提为假，安全但保守的条件也是允许的。具体语言可以另行提供条件的 exactness 或接受完整性；不能从核心正确性推导最弱条件或最优检查成本。

## CompCert 实例如何使用

`GuardMemoryStatefulVersions.memory_projected_verified_version` 从具体 `memory_projected_private_rule`、检查编码及源 scope 构造核心方案。这里的 frame 保持公共 temporary、环境及原内存，允许私有检查寄存器变化。源到候选的 memory equivalence 和公共游标对应由具体规则证明。

`GuardMemoryVersionFamily` 提供两层接口。`memory_verified_version` 保留完整证明接口；可执行的 `memory_version_components` 只是一对 `(check,candidate)` Clight 语句。`memory_version_components_valid` 证明这对语句具有相应规则和安全检查编码；证明不会成为运行时数据。`memory_version_components_statement` 组合列表并保留原片段回退。`memory_version_components_sound` 和非空列表端点把核心结果提升成实际 `projected_region_contract`，进入已有完整程序宿主。

`GuardMemoryParamVersionComponents`、`Services` 从已验证的 mapped／调度／tiling 检查器获得这些组件。组件的结构提取只接受检查器真实返回的 guarded target；它的有效性来自源 package、机器 lowering、依赖证书和实际 guard 执行证明，不能仅凭任意 AST 具有相似外形就认为有效。

统一编译器继续对任意不受信任提案器成立。`request_runtime_versions` 是提案元数据，不是可信条件。任何候选、源包或证书验证失败，都不会产生未认证的运行时方案。

## 当前具体实例与用户入口

```text
(versions (per-axis (schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0)))))
(versions (per-axis (tile 2 3)))
```

候选文件继续通过 `GUARDCERT_LOOP_CANDIDATE` 提供。当前实例为稳定地址参数的规范矩形指针片段：将地址 cap `64、16、8、4、1` 分成五组，在每组选择第一个静态验证通过的逐轴次数方案，再组成运行时列表。静态失败的组被跳过，所以实际列表可能少于五项；没有有效组件时保留源代码。

旧 `(per-axis …)` 入口继续使用单方案。新入口第一项来自同一最高可用参数 cap 的首个验证通过方案；后续项可能在较小参数范围下允许更大的循环次数。实际覆盖需要比较同一提案与输入；框架的正确性不保证不同 oracle 调用一定返回相同提案或证书。

每个方案仍先检查根游标、逐轴次数和参数范围，再查询实际活动坐标的物理地址。空循环在检查未定义的参数和指针前拒绝。相同坐标系数前缀使用固定实际参数的边界扫描，不同前缀使用完整扫描。原始访问对、依赖验证、机器整数模型及公共出口约束保持同一接口。

这不是所有合法输入的范围并集，也不是最弱条件：每个 cap 组仍只选一个静态 profile，次数 box 的生成仍采用有限启发式。多个失败方案可能重复查询同一足迹；当前没有共用别名结果、按成本调度条件或去重。不能仅凭接受增加推断运行时间加速。

## 一个实际条件选择例子

`param_linear1` 的真实访问是 `p[2*i+u+32] = q[2*i+v+33]*alpha+i*beta`。候选的第一项检查根游标为零、`0<n<=464`、`0<=u,v<64`，再检查活动地址不相交。第二项使用 `0<n<=488`、`0<=u,v<16` 和相同语义的实际地址检查。其余项分别采用参数 cap `8、4、1` 与次数 cap `492、494、496`。

因此在 `start=0,n=465,u=3,v=7` 且数组物理分离时，第一项因次数范围失败，第二项通过。新编译器的直接映射配置已经运行该输入：完整 CompCert 汇编输出与独立 word 模型及 GCC 源执行相同；单独的 Clight/GCC 观测器报告第二项命中、实际地址比较 1860 次。二维 `n=60,m=1,u=3,v=7` 也进入第二项，三维 `n=3,m=2,s=2,u=v=0` 进入第四项。观察器证据与完整汇编输出证据分开报告。

## 完整验证与实际代价

主入口已通过全量审计：372 个适配模块、七个 lowering 模块、三个抽象核心模块，以及 522 个证明源码哈希。抽象核心没有全局公理；指令、validator、完整编译器分别精确保留原有 7、12、42 项继承假设。编译器已提取、构建并运行，SHA-256 为 `cdb457783993cfcd20b9b576b15ae2200e9dc5d0e81aa8d36efb6046c0f35f3a`。

测试使用八个循环内核、637 组输入的 `native_memory_address_parameters.c`，Source SHA-256 为 `651feed91d241915346445729b6238285ae7e85c75e519fd033d2890ed464ad0`。13 组配置含直接映射、交换、调度、分裂、两组分块、非法坐标、资源耗尽及非法证书；新入口完成 8281 次完整汇编调用，完整数组和公开游标均与独立 word 模型及 GCC 源执行一致。分支和查询计数来自单独的 Clight/GCC 观测器，不能解释成汇编性能测量。

与已验证的单方案版本 `432945c` 在相同源码上的逐入口对照如下：

| 指标 | 单方案 | 多方案 |
| --- | ---: | ---: |
| 完整汇编调用 | 8281 | 8281 |
| 分支诊断函数调用 | 4288 | 4288 |
| 至少一次进入候选的函数调用 | 1336 | 1810 |
| 进入候选的片段入口 | 3840 | 4330 |
| 实际物理地址查询 | 231952 | 735722 |
| `direct-identity-2` Clight 文件字节数 | 99794 | 355263 |
| 同一配置的汇编文本字节数 | 230341 | 410017 |

第一方案的所选片段、次数／参数范围、逐入口接受结果和查询次数逐项相同。474 次函数调用新增接受、490 个入口新增接受，原先接受的入口没有丢失。各方案命中次数为 `[3840,283,179,28,0]`；第五项在这一批输入中没有独立收益，不能据此推断所有输入下都冗余。49 个地址参数未初始化的空入口均未评估参数范围或执行地址查询。

旧单方案地址参数入口在同一新编译器上完成 8281 次完整汇编调用和 4288 次分支诊断；逐轴入口完成 6230 次完整汇编调用和 3599 次分支诊断。两者的全部原生及分支报告，除编译器哈希外，与固定基线完全一致。五套普通入口另完成 12922 次完整汇编调用和 10321 次分支诊断，分支报告也与基线完全一致。

这些结果同时揭示代价：多个失败方案重复查询同一足迹，使查询总数增至约 3.17 倍；Clight 文件及汇编文本也增长。没有运行时间加速、最弱条件或最优方案保证。检查前缀与提前回退的成本改进还在独立证明原型中，尚未进入这个编译器。

可复现命令为 `make native-memory-parameter-versions`。与单方案版本的对照使用 `python3 scripts/compare_memory_parameter_versions.py --baseline /tmp/guard-parameter-boundary-verified`；固定基线目录含编译器、构建哈希与完整报告。当前验证版本另保存在 `/tmp/guard-parameter-versions-verified`，以便后续修改后继续同源对照。
