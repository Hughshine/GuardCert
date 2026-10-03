# 多个实际数组对象的 guarded 循环变换

统一入口现在支持矩形循环中的多个实际数组对象。每条源语句可以是纯写、读取自身单元后
更新，或读取本数组的行首后更新；语句列表、数组数量与各语句的算术系数由源 AST 决定。
目前这些数组使用相同的 extent 和 stride。`b[index] = a[index] + payload` 的跨数组读取
和任意指针切片尚未进入这份 C 源识别器。

## 物理内存前提与实际条件

`GuardMemoryMultipleArrays.memory_array_registry` 将逻辑数组和整数索引解析为实际
CompCert block、byte offset 与 Mint32 chunk。`memory_array_registry_nonalias` 在实际
block 列表无重复时证明不同逻辑单元的物理位置不重叠；这个端点没有全局公理。
逻辑名字不同本身不提供这项结论。

运行时 guard 先检查公开 iterator 和参数化数组范围，再比较每对数组对象的基址。
`GuardMemoryArraySeparation` 证明偏移为零且指针有效时，实际 Clight 指针不等比较对应
block 不同。`GuardMemoryRegistryGuard` 将两两比较编码成短路树，证明其结果对应实际
block 列表是否无重复。`GuardMemoryNamedGuard` 把它放在范围检查之后：范围不成立时
执行原片段，不求值数组比较。

条件的可定义性也在证明里。`named_array_operations_source_clight_decode` 从源循环的
实际成功执行提取所有数组绑定；在范围条件成立时，第一次实际迭代的成功 load/store
提供基址有效性。store 保持权限，因此后续语句对某个数组的访问也能建立入口时的有效
指针。这里没有要求调用方预先相信所有逻辑数组互不重叠。

基址比较只用于上述数组对象。两个普通切片指针不相等仍可能表示重叠区间，不能套用
这条证明；当前源码识别会保守拒绝这种输入。

## 源到候选到完整程序

`GuardMemoryNamedOperations` 解码源中的各条真实数组操作和矩形循环协议。
`GuardMemoryNamedRegistrySource` 保留语句顺序与实际 memory action；
`GuardMemoryNamedClight` 将整个源循环接到同一参数、同一实际 Mem 的 Loop 执行。
重复出现的同一数组会在 registry 中去重，重复语句的位置仍由提取器区分。

候选后端 `GuardMemoryRegistryBackend` 按每条指令的读写数组选取各自的 Clight 变量，
执行实际读取、整数计算和写入。`compile_memory_registry_loop_correct` 保留整个
CompCert Mem 及公开临时变量。`GuardMemoryNamedChecker` 对外部仿射候选复用实际提取、
坐标对应、域等价和依赖验证；二维 tiling 继续使用已经证明的 tile witness 进展端点。

`GuardMemoryNamedCandidate` 组合源解码、别名条件、候选执行及公开 iterator 出口修复。
`GuardMemoryNamedCompiler` 核对整个源 AST，然后生成实际 guard、候选和共享原片段回退。
这条路径已进入 `GuardMemoryUnifiedCompiler.compile_memory_unified_regions_correct` 的
完整 Csem→Asm backward simulation。候选生成器仍没有正确性前提。

## 复现与验证边界

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make native-memory-multiarray
GUARDCERT_LOOP_CANDIDATE="$PWD/examples/loop-candidates/interchange.sexp" \
  build/compcert-memory-unified/ccomp \
  -conf build/compcert-memory-unified/compcert.ini \
  -stdlib build/compcert-memory-unified/runtime -S examples/native_memory_multiarray.c
```

63 个具体内存适配模块和 7 个 lowering 模块已完成重新编译和假设审计。指令桥保持原有
7 项假设，实际 validator 保持 12 项，完整编译器保持 CompCert 与 validator 的 42 项
并集，没有新增全局公理。原生测试的报告单独位于
`build/native-memory-multiarray/report.json`，覆盖两个／三个数组、全局数组、外层循环、
零迭代、非零入口 iterator、实际仿射与分块候选、证书／资源拒绝和源回退。
报告已通过十四组配置，每组 2011 行完整输出与 GCC 和独立模型逐项一致。identity、
interchange、冗余条件和四种块宽命中四个支持函数；fission 命中三个函数，三数组的
行首读取依赖导致该候选被拒绝。基址比较和公开 iterator 修复也从实际 Clight 检查。

这个实现扩展的是实际数组对象的完整程序路径。一般 C 源的嵌套仿射边界、跨数组读取、
不同数组布局的共同范围检查以及任意缓冲区的重叠检查仍需继续闭合；不能从一般 IR
提取定理推出这些 C 语法已经被识别。
