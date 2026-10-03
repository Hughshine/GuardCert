# 真实指针缓冲区与完整程序接入

这条路径接受由调用方传入的一个稳定 signed32 指针。源和候选使用该指针的实际 CompCert block 与基址偏移执行 `Mem.load Mint32` 和 `Mem.store Mint32`。基址可以非零；源不再需要固定数组对象或零地址访问锚点。

`memory_pointer_buffer_locations` 把逻辑单元映射到 `(base + 4*index) mod Ptrofs.modulus`。`memory_pointer_buffer_locations_nonalias` 在有限逻辑窗口内证明不同单元的物理地址不重叠，包括地址回绕。这个窗口用于访问和依赖表示，不宣称实际分配有相同长度。源成功执行提供读取和写入的定义性；候选执行由验证器证明。因此，一元素分配上的一单元变换可以成立。

`FramedNestedClightFor` 增加可由语言实例提供的稳定 temporary 能力接口。指针实例保护保存实际 `Vptr block base` 的 temporary，并把这个能力逐层传给候选指令执行。框架组合层只需要能力在 temporary frame 下保持的证明。`memory_recursive_source_decode_framed` 和 `memory_recursive_first_leaf` 分别提供完整递归源解码及首个实际叶子执行；指针实例从首个实际解引用得到入口基址，不假设检查可以读取未使用的指针。

源体是有限赋值列表，包含多个仿射读取及机器整数加减乘。`memory_source_value_inverse` 通过可实例化的读取关系证明源表达式与指令值的对应；指针实例给出实际 load 的唯一性和反向解码。源数组赋值、物理单点、实际指令、整个循环、候选 lowering 和公开计数器出口都已有具体证明。

`check_memory_pointer_caps` 依次尝试默认索引窗口提出的次数上界及 `8,4,3,2,1`。每次重新检查源包和候选域、依赖及机器 lowering，取第一个通过的范围，再编码为短路 guard。它是有限条件搜索；没有最弱前提或一般关系式合成的保证。检查只读取初始外层计数器和各维次数，不读取指针。任一维零次或入口非零时执行原片段；更内层未被源使用的次数不被提前读取。

映射候选、仿射调度生成和外层两轴分块接到同一个 `GuardMemoryUnifiedCompiler.compile_memory_unified_regions`。`compile_memory_unified_regions_correct` 提供完整 Csem→Asm 行为保持，guard 失败或源／候选不被支持时保留源执行。

当前具体识别器接受有限深度的规范矩形 counted loops、复位子迭代器、稳定次数参数、非负聚合系数和偏移的仿射下标，以及一个相同的指针 temporary。默认逻辑窗口是 1024 个单元。多个不同指针变量、稳定外部 RHS 标量、负系数源访问及更一般深层仿射域继续扩展。

输入为 [`native_memory_pointer.c`](../examples/native_memory_pointer.c)。`make native-memory-pointer` 构建统一编译器，比较真实汇编、GCC 参考和独立机器整数模型，再单独检查加分支计数器的 Clight pretty-print。用例覆盖非零基址、调用方完整缓冲区、二至四层循环、多个读取、计算链、机器整数回绕、周围重复循环、空指针的零次循环、未使用的内部次数及一元素分配。未经保护的复制链在输入 `offset=9,n=1,m=3` 上产生不同结果：源首单元为 66，反转为 151，分裂为 73。

全量审计重新编译 211 个适配模块和七个 lowering 模块，完整编译器仍精确继承 CompCert 与具体 validator 原有的 42 项假设，没有新增全局公理。提取编译器 SHA256 为 `129db0b48d17474c4aa0db69a431255b46b0698e386a9fdb27d023c2b49721c6`。15 组完整汇编配置全部通过，每组与 GCC 参考及独立模型核对 227 行完整输出；错误证书和资源耗尽配置没有接受任何候选。10 组分支诊断共执行 390 次调用，确认合法范围内的实际快路、非零基址、一元素分配、每个零次维度、超出范围及非零入口的回退，以及未定义内部边界的短路。反转和分裂都将更新链的范围收紧到单点，并在上述反例输入上执行源程序。报告为 `build/guard-memory-proof-report.json`、`build/native-memory-pointer/report.json` 与 `branch-report.json`。任意深度固定数组源的 17 组完整汇编回归及 11 组／458 次调用的分支诊断也通过同一编译器。
