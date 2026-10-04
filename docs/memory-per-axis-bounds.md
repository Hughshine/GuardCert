# 每个循环轴使用自己的范围条件

这条路线将[多轴边界扫描](memory-axis-boundary-scans.md)的共同 cap 替换为与源轴对齐的 cap 列表。源访问检查、运行时条件、候选依赖验证和候选机器 lowering 使用同一列表。该阶段源语言是规范矩形指针循环；地址外部参数和依赖外层的深层域没有因此接通。后续[仿射地址参数](memory-affine-address-parameters.md)另行接通稳定地址 temporary 和内层片段。

## 用户入口

在已有候选外加一层 `per-axis`。例如：

```text
(per-axis (schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0))))
(per-axis (tile 2 3))
```

环境变量 `GUARDCERT_LOOP_CANDIDATE` 指向这个候选文件。提案是未验证输入；编译器从实际源 AST 检查出源包，生成逐轴范围条件，再检查候选的域、依赖与机器表达式。编译时不支持或检查失败时保留源片段；运行时条件失败时执行原片段。普通候选格式沿用既有路线。

语言实例向统一请求暴露实际指令、坐标数、参数列数、已检查的 cap 列表及是否来自逐轴包。原生提案器用最后一个字段选择入口；完整程序正确性定理仍对任意提案器成立，框架不信任提案器根据这些字段返回的结果。

## 条件如何生成和证明

源访问提出一组正 signed32 cap。当前提案算法从各轴 1 开始，按外层至内层的顺序尝试扩大某一轴；每次用现有仿射访问 box checker 检查全部真实读写，搜索至多 1024。随后还尝试单轴收紧到 8、4、1 及全 1。提案算法不承担正确性证明；最终源包再次独立检查轴数、源形状、cap、访问编码、范围和稳定参数。

运行时先检查源外层初始游标为零，再按源嵌套顺序检查各轴 `0 < count <= cap`。定义性具有条件性：只有先前轴通过才要求下一轴的界是实际整数。正常源执行提供这项证据，外层为空时不会读未定义的内层界或指针。

范围通过后扫描实际源地址。相同系数向量沿用 `2^d P` 边界策略，不同向量沿用完整枚举；source-derived load/store 能力保证每次实际查询有效且对齐。检查改变私有 temporary，保持公共 temporary 与原内存。接受给出逐轴范围和受限源足迹 NonAlias；候选规则由此连接实际源执行、Loop／依赖验证、实际候选执行及公共出口恢复。

## 提供的接口

- `GuardMemoryVectorPointerSyntax` 的源包和 `check_memory_vector_pointer_region`：源 AST、每轴 cap、实际读写与参数的已检查表示。
- `GuardMemoryVectorBounds`、`GuardMemoryVectorGuard`：布尔前提、条件定义域、实际检查树及范围 soundness／编码 exactness。
- `GuardMemoryVectorPointerBody`、`GuardMemoryVectorPointerDomain`：实际源执行到 Loop 的对应，以及被使用参数的实际整数类型。
- `GuardMemoryVectorChecker`、`GuardMemoryVectorTiling`：任意给定参数区间下的候选证书与提取检查器。区间列表同时用于域与依赖验证。
- `GuardMemoryVectorPointerBounds`、`GuardMemoryVectorPointerProjectedCandidate`：将相同范围传给机器 lowering，连接受限内存与真实内存及候选执行。
- `GuardMemoryVectorAxisFootprint`、`Pairs`、`Scan`、`Frame`、`Guard`：实际源足迹、私有地址扫描、状态运输和接受后的语言性质。
- `GuardMemoryVectorAxisCompiler`、`Services`、`Describe`：局部程序契约、mapped／调度／分块服务及有限范围提案搜索。

这些模块具体实例化既有有状态核心。核心只消费检查执行、状态关系和候选规则；它不解释仿射下标、CompCert 指针或每轴 cap。

## 覆盖与取舍

新 cap 仍描述一个 box，当前每个片段选择第一个验证通过的 profile。增大外层可能缩小内层；新 profile 不保证包含普通入口的全部快路。原型没有将多个 profile 合成运行时分支，也不声称最弱条件或对任意前提合成条件。

原生私有池、逻辑窗口 1024、32 条原始访问预算和保守只读别名分离保持既有范围。多个稳定 RHS 标量仍采用完整 signed32 范围；将它们用于地址的非零系数还需要另外的源类型、范围和地址编码证明。

## 验证状态

2026-10-03（本地日期）：20 个新增模块接入统一 Csem→Asm 正确性定理。340 个适配模块、七个 lowering 模块和两个有状态核心模块的全量审计通过，489 个证明源码哈希一致。范围数学及编码辅助端点没有全局公理；完整编译器仍精确继承已有 CompCert／validator 的 42 项假设。新提取编译器 SHA-256 为 `2a98b41c32034cac344a6b087f9ea5d21592668303136fc702d6c894ea5864ac`。

新源 `examples/native_memory_axis_bounds.c` 保留原多轴核和调用包装，增加各轴范围附近、长窄、较大三／四维输入。445 次源调用已与 GCC 及独立机器整数模型一致，模型对每次实际读写断言物理缓冲区内的索引。源 SHA-256 为 `cc2f27ee22c2e660488bae8a3a16f25bd854163a67d242d41188e10b28b1c399`。旧 `21d17fe` 编译器快照和新编译器分别完成相同源的 14 组配置，各 6230 次完整汇编调用通过；包括直接候选、调度生成、fission、两种 tiling、无效坐标、资源限制及错误证书的源回退。

完整 CompCert 汇编验证与 GCC 加标记 Clight 的分支／查询计数分开报告。同一 3115 次分支诊断由 698 次快路、2417 次回退，变为 1072 次快路、2043 次回退；逐调用比较有 502 次新增接受、128 次新增回退。实际查询总数由 880,720 增至 6,450,000；扩大接受的较大输入也扩大检查工作量，不据此宣称加速。

| 候选与核 | 普通 cap | 逐轴 cap | 观察到的取舍 |
| --- | --- | --- | --- |
| 二维源序复制 | `[61,61]` | `[64,15]` | 接受 `[64,1]`，而 `[16,16]` 回退 |
| 二维交换复制 | `[16,16]` | `[64,15]` | 长窄输入扩大；原 `[16,16]` 快路丢失 |
| 三维源序复制 | `[15,15,15]` | `[16,8,8]` | 外轴扩大，内轴 9 的部分输入丢失 |
| 四维源序复制 | `[7,7,7,7]` | `[8,4,8,4]` | 外轴扩大，第二／第四轴 5 的部分输入丢失 |
| 二维链的 fission | `[1,1]` | `[64,1]` | 依赖验证收紧内轴，外轴保留 64 |

例如二维交换的完整测试从 48 次快路变为 101 次，新增接受 62 次、新增回退 9 次。四维源序测试从 29 次快路变为 28 次，新增接受 6 次、新增回退 7 次。比较报告保留每个具体调用，避免总数掩盖丢失覆盖。新旧同一源序二维配置的 Clight 文件均为 59,773 bytes，汇编文件为 137,112／137,187 bytes；这只是生成文件大小，不是运行时间或机器代码大小。

普通候选入口的五套完整汇编及分支回归在同一新编译器上全部通过，共 12922 次完整汇编调用、10321 次既有分支诊断。同／异系数算法选择另有 14 次查询计数诊断；指针、稳定 RHS 标量、signed 地址和源元数据另有 15 组选择性完整汇编配置通过。上述报告均绑定同一 `2a98b41c…` 编译器。


`make native-memory-axis-bounds` 运行当前编译器的完整汇编和分支诊断。旧快照比较使用 `scripts/native_memory_axis_bounds.py --previous-compiler /tmp/guard-boundary-verified/ccomp` 及 `scripts/native_memory_axis_bounds_paths.py --previous`；`scripts/compare_memory_axis_bounds.py` 对照同一源码的 profile、实际快路与回退以及查询数，并保留新增回退列表。历史快照是本次实验环境文件；已有 `before-report.json` 与 `before-branch-report.json` 才能运行比较。当前源码并不会重新生成旧编译器。

后续参数路线允许为外层候选拒绝的源继续检查内层片段。因此当前回归脚本还记录片段根、实际 count 标识符、地址参数和每次入口；当前报告可能含额外内层 guard。上面的新旧覆盖与查询比较绑定 `4d1c5fd`／`2a98b41c…` 阶段。重跑历史比较需要当时的编译器和报告；当前报告的片段集合不同，不能冒充同一历史实验。
