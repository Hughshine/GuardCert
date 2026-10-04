# 仿射地址参数的 guarded transformation

本文记录 `1b6e3fd` 阶段的能力及验证数据。该版本的测试源为七个核、568 次调用；随后[固定地址参数的边界扫描](memory-parameter-boundary-scans.md)扩展为八个核、637 次调用，并使用同一新源重新建立前后对照。本文中的完整扫描成本及历史报告不能视作后续版本的当前结果。历史证据保存在 `/tmp/guard-address-parameters-verified`。

这条路线处理实际指针循环中稳定的地址参数。例如 `p[16*i+j+u+32] = q[16*i+j+v+33]*alpha+i*beta+j`。`i,j` 是循环坐标，`u,v` 是地址参数，`alpha,beta` 是普通 RHS 标量。地址参数现在进入源表示、运行时检查、依赖验证和候选机器 lowering 的同一语义接口。

## 用户入口和运行行为

沿用逐轴候选入口：

```text
(per-axis (schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0))))
(per-axis (tile 2 3))
```

`GUARDCERT_LOOP_CANDIDATE` 指向候选文件。编译器从实际 Clight 片段提出循环包，独立检查完整源 AST、所有读写表达式、参数使用和范围。随后检查任意候选的域、依赖、机器表达式与私有寄存器。任何静态检查拒绝时保留源代码。

运行时先检查外层初始游标为零，再按源嵌套顺序检查 `0<count<=cap`，之后检查各个地址参数 `0<=parameter<parameter_cap`，最后扫描本次实际活动坐标的地址。所有检查通过才执行已验证候选；失败时执行原循环。

空循环在检查内层界、地址参数、RHS 标量和指针之前回退。地址参数没有无条件整数类型假设：正常源执行第一次实际访问所需的表达式，提供其值是机器整数的证据。只用于 RHS 的标量保留完整 signed32 区间，不被地址参数的范围条件误限制。一个参数同时用于地址与 RHS 时只占一个参数列。

所选片段可以是内层循环。统一宿主在外层候选拒绝后继续访问子片段：外层 `i` 在某次内层片段内稳定，自动成为地址参数，而非该片段的循环坐标。因此一维候选可变换二维源的内层 `j`，保留外层源顺序；二维候选也可变换三维源的内两层。片段的参数和接受次数必须按每次入口计算，不能将整函数的足迹当作这些局部片段的足迹。

## 语言实例暴露的接口

- `GuardMemoryParamPointerSyntax` 的 checked source package：循环、各轴 cap、地址参数和各参数 cap、RHS 标量、真实指针与操作。`check_memory_param_pointer_region` 独立校验提案，并产生包含源对应和所有范围义务的证书。
- `GuardMemoryPointerDefinedIndex`、`GuardMemoryPointerSourceWords`、`GuardMemoryParamPointerBody`：由真实源执行推导被使用地址寄存器及 RHS 寄存器的实际整数值，再连接完整机器整数运算和 Loop 指令。
- `GuardMemoryParameterRanges`、`GuardMemoryParamPointerHeader`、`GuardMemoryParamPointerDomain`：参数前提、布尔检查、短路定义性、实际 Clight 执行的 exactness，以及检查接受后的范围 soundness。
- `GuardMemoryParamPointerBounds`、`GuardMemoryParamPointerProjectedCandidate`：同一坐标、参数、RHS 区间传给依赖验证和机器 lowering，并建立真实源、受限足迹、候选执行及公共循环游标之间的对应。
- `GuardMemoryParamAxisFootprint`、`Pairs`、`PairScan`、`Scan`、`Frame`、`Guard`：固定实际参数值，仅枚举活动循环坐标，检查真实物理地址；由源 load/store 能力证明查询有效和对齐。接受产生足迹上的 NonAlias，保持公共 temporary 和原内存。
- `GuardMemoryParamAxisCompiler`、`Services`、`Describe`：实际局部程序契约、mapped／调度／外两轴分块入口，以及不受信任的源描述和有限参数 profile 提案。

有状态核心仍只消费检查执行、状态关系和候选规则。仿射参数、CompCert 指针和具体 NonAlias 定义由语言实例处理。统一编译器请求增加 `request_address_limits`，同时提供已检查的逐轴 cap 和总参数列数。完整程序定理对任意提案器成立；提案器读取这些字段不进入可信边界。

## 条件表达能力与当前边界

地址表达式允许常量、正负常量系数的循环坐标和稳定地址 temporary；参数值在本次循环内固定。当前入口为参数提出共同 cap `64,16,8,4,1`，对每个参数 profile 提出逐轴 cap，并选第一个静态验证通过的组合。源 checker 再次独立校验。没有最弱条件、最优 profile 或接受范围包含关系的保证。

参数是固定后缀，不能成为扫描的额外轴。若循环维数为 `d`、活动点数为 `P`，当前新参数路线对原始跨指针访问对采用完整 `P²` 查询。既有无地址参数路线的边界扫描仍保留在自己的入口；尚未将边界策略推广到新参数路线。没有去重、提前结束或只读别名放宽。

限制仍包括规范矩形片段、片段根的零初始游标、最多七个源轴、逻辑窗口 1024 和至多 32 条原始访问。负地址参数可以在源循环中合法执行，但当前检查将它们送回源代码。`parameter*i` 的动态步长、依赖外层的深层指针循环域、片段根的非零循环起点及任意前提合成尚未由这条路线实现。逻辑窗口用来限制编码；不会要求整个窗口已分配。每次实际查询的物理有效性来自正常源执行的实际访问。

## 本阶段验证

2026-10-03（本地日期）：20 个新增证明模块接入统一 Csem→Asm 模块。360 个适配模块、七个 lowering 模块及两个抽象核心模块全量重编译与假设审计通过，509 个证明源码哈希一致。抽象核心、范围数学及编码辅助端点没有全局公理；完整编译器仍精确继承已有 CompCert／validator 的 42 项假设。新提取编译器已构建，SHA-256 为 `071573d37a616b08c8975daf06d76a24b3b2333b125c93ee78519a0a8abcf930`；完整运行验证已经通过。

`examples/native_memory_address_parameters.c` 有七个源核及 568 次调用，涵盖一至三维地址参数、负地址系数、连续写依赖、同一个参数同时用于地址和 RHS、未使用参数，以及外层空循环中的未定义地址参数。GCC 执行与独立机器整数模型已一致；模型对每次物理读写断言缓冲区内索引，比较完整缓冲区和公共游标。

上一阶段 `4d1c5fd` 的编译器快照（SHA-256 `2a98b41c32034cac344a6b087f9ea5d21592668303136fc702d6c894ea5864ac`）已经完成当时相同七核源的一至三维直接候选和二维分块四组配置，共 2272 次完整汇编调用。结果一致，但这四组配置均未在七个核中产生 guarded transformation。历史报告是 `/tmp/guard-address-parameters-verified/address-parameters-before-report.json`。这是新增能力的对照基线，不是新入口运行通过的证据。

新入口的 13 组配置完成 7384 次完整 CompCert 汇编调用，全部与 GCC 和独立机器整数模型一致；包括直接一至三维候选、交换、源序／交换／fission 调度、两种块大小、无效坐标、资源限制和错误证书。源 SHA-256 为 `423531c840f6581aa999c81c43e1605dcc0765d120030bd965f6d7f02aafe685`。

独立分支诊断完成 4219 次函数调用，其中 1315 次至少进入一个候选片段、2904 次没有进入。按片段实际入口计数，3819 次接受、9083 次回退；657 次函数调用具有内层 guard，共执行 1117174 次物理地址查询。6124 次片段入口因地址参数范围拒绝；未使用参数为负时仍有 20 次片段接受。不同配置的范围和早期拒绝层次不同，报告保留逐入口数据。上述分支和查询证据来自 GCC 执行带标记的 Clight，独立于完整汇编执行。

例如一维候选可在 `param_copy2(start=1,n=3,m=2,u=3,v=7)` 中接受两个内层片段，执行 16 次查询；二维整个循环巢的候选在相同输入上因非零根起点回退，执行零次查询。两者都保持完整缓冲区及公共 `i,j,k`。三维源的直接二维候选也能接受内两层，其外层 `i` 自动成为稳定地址参数。

链式核即使使用不同物理数组，任意 fission 或交换仍可能错误。独立机器整数模型给出两类具体反例；实际候选证书将交换的外轴收紧到 1、fission 的内轴收紧到 1。此处的正确性同时消费范围、NonAlias 和依赖验证，不能用 NonAlias 替代依赖证书。

同一编译器的五套普通入口回归完成 12922 次完整汇编调用及 10321 次分支诊断。逐轴入口完成 6230 次完整汇编调用及 3599 次分支诊断：新地址参数能力额外覆盖 484 次内层片段所在函数调用，观察到 1280 次函数至少进入候选、10751100 次实际查询。这个当前回归含新增内层片段，不能用它覆盖上一阶段 `4d1c5fd` 的固定历史比较报告。检查成本仍可较高；这些结果不宣称性能提升。 同／异系数选择另有 14 次查询计数诊断通过；指针、RHS 标量、signed 地址和源元数据另有 15 组选择性完整汇编配置通过。所有当前报告均绑定同一 `071573d3…` 编译器。

`make native-memory-address-parameters` 运行完整 CompCert 汇编执行和另外的分支观测。`scripts/native_memory_address_parameters_paths.py` 用带标记的 Clight 观察实际快路／回退和指针查询数，与独立前提及足迹模型比较；这个诊断单独报告，不冒充汇编执行证据。

本阶段仍使用锁定的 CompCert 3.18 与 Rocq／Stdlib 9.2。2026-10-03 重新核对[官方下载页](https://compcert.org/download.html)及 [v3.18 变更记录](https://github.com/AbsInt/CompCert/blob/v3.18/Changelog.md)：官网当前最新公开版本为 3.18，变更记录明确支持 Rocq 9.2。GitHub 的 `releases/latest` 跳转仍指向 3.17，不能单靠该跳转判断最新源码版本。
