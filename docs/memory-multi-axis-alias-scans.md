# 多轴活动访问扫描

此扩展沿用[有状态语言核心](memory-affine-alias-scans.md)，把动态 NonAlias 检查从单个计数轴推广到任意有限深度的规范矩形源循环。每个轴有独立的实际动态上界；多个轴也可以共享上界变量。候选仍消费已有的局部内存与依赖证明，统一入口通过同一个 `projected_region_contract` 接到 Csem→Asm。

## 给编译器一个候选

用户或工具提供候选描述，编译器检查它并生成 guard 与回退。例如，交换前两个循环轴：

```sh
printf '%s\n' '(schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0)))' > /tmp/guard-axis-interchange.sexp
GUARDCERT_LOOP_CANDIDATE=/tmp/guard-axis-interchange.sexp build/compcert-memory-unified/ccomp -conf build/compcert-memory-unified/compcert.ini -stdlib build/compcert-memory-unified/runtime -dclight -S -o /tmp/guard-axis.s examples/native_memory_axis_alias.c
gcc /tmp/guard-axis.s -o /tmp/guard-axis
/tmp/guard-axis
```

候选是不受信任的输入。编译器从实际 C 源生成源包，尝试次数条件，验证候选的域与依赖，再生成检查代码。用户不必提供 alias 假设；运行时检查建立候选使用的实际活动足迹分离。候选证书无效、资源不足或源结构不支持时保留源片段。

## 检查对象与实际代码

检查对象是原源循环实际活动的矩形足迹。对每一对不同逻辑指针的源访问，生成两份私有计数器向量，分别遍历两侧的活动坐标，并查询从源表达式重命名得到的实际地址。任一比较失败将私有标志清零；其他比较继续执行，结束后决定运行候选或原片段。

零次循环或次数条件失败，在地址检查之前回退。检查只使用源实际访问的有效、对齐单元，不把逻辑窗口 1024 当作分配长度，也不使用不同 CompCert block 之间的大小比较。

设活动点数为 `P = n_0 * ... * n_(d-1)`，一个有向原始访问对执行 `P²` 次地址比较。检查代码随维数和原始访问对数量生成，未把所有迭代点展开成代码。单轴仍优先使用已有[端点策略](memory-affine-endpoint-scans.md)；多轴当前没有相应线性策略，不宣称这次扩展改善了检查的渐近执行成本。

## 证明接口

- [GuardMemoryBooleanRectangle.v](../adapters/compcert-memory/GuardMemoryBooleanRectangle.v) 证明递归布尔扫描等于矩形点集上检查的合取。
- [GuardMemoryBooleanRectangleExecution.v](../adapters/compcert-memory/GuardMemoryBooleanRectangleExecution.v) 证明实际 Clight 嵌套计数循环正常执行，公共状态与内存不变，私有标志表示检查的结果。叶子检查提供坐标绑定、公共状态保持和布尔结果证明。
- [GuardMemoryAffineAxisRenaming.v](../adapters/compcert-memory/GuardMemoryAffineAxisRenaming.v) 和 [GuardMemoryAffineAxisAddress.v](../adapters/compcert-memory/GuardMemoryAffineAxisAddress.v) 将源轴映射到私有计数器，并连接仿射系数编码、机器整数求值和源地址能力。中间整数运算可以取模；最终地址的逻辑单元必须属于已验证的源足迹。
- [GuardMemoryAffineAxisPairScan.v](../adapters/compcert-memory/GuardMemoryAffineAxisPairScan.v) 组合两份扫描，证明实际指针比较的结果与完整访问对检查一致。
- [GuardMemoryAxisPointerFootprint.v](../adapters/compcert-memory/GuardMemoryAxisPointerFootprint.v)、[Pairs](../adapters/compcert-memory/GuardMemoryAxisPointerPairs.v)、[Scan](../adapters/compcert-memory/GuardMemoryAxisPointerScan.v)、[Frame](../adapters/compcert-memory/GuardMemoryAxisPointerFrame.v) 与 [Guard](../adapters/compcert-memory/GuardMemoryAxisPointerGuard.v) 连接源矩形足迹、跨指针分离、检查列表执行和公共状态运输；接受推出检查后状态的 NonAlias。
- [GuardMemoryAxisPointerCompiler.v](../adapters/compcert-memory/GuardMemoryAxisPointerCompiler.v)、[Services](../adapters/compcert-memory/GuardMemoryAxisPointerServices.v) 与 [Describe](../adapters/compcert-memory/GuardMemoryAxisPointerDescribe.v) 检查私有名字、次数区间、源包和候选证书，并接入统一完整程序入口。

新的 guard 实际实例化 `memory_projected_private_rule_stateful_sound`。通用核心消费语言提供的检查执行、公共状态关系、前提和条件构造证明；这里的具体实例负责 Clight 表达式、整数、内存和循环语义。

扩展一个新的检查算法时，它需要证明实际生成语句的执行结果、公共状态保持，以及接受推出同一前提。当前足迹和候选契约可以继续复用。扩展候选时，mapped、schedule、tiling 服务分别提供证书检查入口，检查成功推出 `projected_region_contract`；统一区域宿主再把局部契约接到完整程序。地址检查并不替代调度依赖证明。

## 候选及次数条件

mapped、直接生成的 affine schedule 和外层二维 tiling 都使用同一动态扫描。编译器依次尝试 `[1024,64,32,16,8,4,1]` 请求上界，实际源包的共同上界还由访问系数与逻辑窗口限制。每次重建并检查源包及候选；接受的是通过验证的次数条件，未通过则继续尝试更小范围和既有路径。

这是有限条件搜索。一个上界仍共同限制各轴，因此可能拒绝安全的长窄矩形。例如在步长 16 的布局上，候选可能需要内层 `m<=16`，而外层可以更大；当前小共同上界也会限制外层。它不等于自动发现任意关系式前提，也不是完整的每轴最优条件合成。

## 复现与当前验证

入口为 `make native-memory-axis-alias`。源 [native_memory_axis_alias.c](../examples/native_memory_axis_alias.c) 包含二维 signed 地址和复制链、三维与四维缓冲区循环。独立模型核对所有数组、机器整数值以及四个公开源循环变量，包含外层为空、内层为空、起始值不满足入口前提和空指针零次调用。

2026-10-03：310 个适配模块、七个 lowering 模块和两个有状态核心模块全量审计通过，459 个证明源码哈希一致；指令桥、validator、完整编译器分别保持既有 7／12／42 项假设，没有新增全局公理。新增矩形枚举对应、轴重命名布局、活动足迹、访问编码及检查状态运输均没有全局公理。审计复用已锁定的 92 文件 optimizer profile，没有在这次审计重编译整个 profile。

新编译器 SHA256 为 `6180edd256e46d6a4ff8852a661e8aeb6691ecf45bbd537ba4b2ef224ce881a2`。14 组配置、每组 305 次完整 CompCert 汇编调用通过，总计 4270 次。11 组 GCC 加标记 Clight 诊断共 2135 次调用通过：618 次候选、1517 次回退，327 次候选调用超出旧共同上界。诊断逐次核对真实分支和实际指针比较数，共 35537690 次比较；完整数组和四个公共出口分别与独立模型一致。错误坐标、无效证书和资源耗尽保留源循环。

上一版已验证编译器 `3d284035…` 在完全相同的 C 源和输入上通过三组配置、915 次完整汇编调用及 418 次分支诊断。基线诊断没有测量旧比较成本。其观察到的共同上界与新版本如下：

| 源访问 | 旧共同上界 | 新源序上界 | 新交换上界 |
| --- | ---: | ---: | ---: |
| 二维复制／负地址复制 | 4 | 61 | 16 |
| 二维复制链 | 3 | 61 | 8 |
| 三维复制 | 3 | 15 | 8 |
| 四维复制 | 2 | 7 | 4 |

复制链的 fission 只在共同 cap 1 获准。独立反例表明，在不同 block、无跨指针 alias 的 `2×2` 输入上，任意 fission 会改变结果；这也验证了 alias 前提不能替代同一指针内部的依赖检查。

同一完整源文件的文本体积：

| 配置 | 旧 Clight／汇编字节 | 新 Clight／汇编字节 |
| --- | ---: | ---: |
| direct-identity-3 | 563471／362585 | 17978／21265 |
| direct-identity-4 | 274441／165124 | 20734／22961 |
| schedule-identity-2 | 1343154／891891 | 48408／41075 |

这些数字没有给出运行速度结论。源序 `16×16` 二维复制实际执行 131072 次比较；`33×1` 执行 2178 次，`61×1` 执行 7442 次。交换配置因共同 cap 16 拒绝后两种长窄输入，在回退之前执行零次地址比较。

同一编译器已重跑旧多指针的 3069 次完整汇编调用及 5256 次分支诊断、一维端点的 1687／964 次、一般仿射的 2696／1366 次及逐元素路径的 1200／600 次。连同新例子，共 12922 次完整 CompCert 汇编调用和 10321 次独立分支诊断通过。

报告位于 `build/native-memory-axis-alias/`：`before-report.json`／`before-branch-report.json` 是旧版，`report.json`／`branch-report.json` 是新版。完整 CompCert 汇编与 GCC 加标记 Clight 诊断分别报告。

## 仍未覆盖

原始访问条数预算仍为 32。原生驱动当前提供 16 个私有变量，因此这条双向扫描最多支持七个轴，超限继续尝试既有路径或回退；数学和执行模型支持任意有限深度。源语法仍要求规范矩形计数结构，较深的依赖外层仿射域、地址中的稳定外部参数、更弱的只读别名条件、每轴独立的条件搜索与更低成本的多轴检查都仍待实现。
