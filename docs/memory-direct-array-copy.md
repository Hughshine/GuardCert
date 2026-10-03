# 直接数组复制的完整程序路径

统一编译器现在识别 `b[i*stride+j] = a[i*stride+j]`。它可以单独形成循环体，也可以
与纯写、原地更新、行首读取及跨数组加法混用。同单元跨数组读取的登记表、基址检查、
实际依赖验证和完整 Csem→Asm 宿主都用于这条路径；只读输入也纳入登记表。

`GuardMemoryCopyArray` 证明直接 Clight 复制和实际 Mint32 load/store action 的双向对应。
这里的 action 只在读取值是 Vint 时成功，因为实际 Clight 整数赋值的转换也要求整数值。
没有把可能产生 Vundef 的任意底层读取当作成功的整数赋值。

`GuardMemoryCopyInstruction` 将复制编码成 `AddValue (LoadedValue 0) (ConstantValue 0)`，
证明它与上述部分 action 等价。加零保留所有 32 位整数，包含 INT_MIN 与 INT_MAX；
这个表示让已证明的整数候选后端可以消费复制，无需假定所有内存单元已经初始化。
实际成功的源执行提供所需事实。

源提案只是猜测存储形状。`GuardMemoryNamedCompiler` 仍核对完整源 AST，
`GuardMemoryNamedRegistrySource` 仍从实际执行建立数组绑定、权限和 IR 对应。
复制生成的读写依赖参与同一验证器；例如三数组的 `a → b → c` 链不能因为数组名字
不同就忽略跨语句依赖。候选交换、分裂、分块、剪切和反转仍分别经过域及依赖检查。

73 个具体内存模块和 7 个 lowering 模块的全量编译与假设审计已经通过。指令桥保持
7 项继承假设，验证器保持 12 项，完整编译器保持原有 42 项并集，没有新增全局公理。
同一提取编译器已经通过：

- 16 组多数组配置，每组 4022 行输出。
- 13 组仿射坐标映射配置，每组 4022 行输出。
- 旧统一入口的 12 组仿射、5 组分块和 5 条分块拒绝，每组 1564 行输出。

所有输出逐项与 GCC 和独立模型比较。新函数覆盖只读输入的直接复制、三数组复制链和
整数极值；实际 Clight 检查确认支持函数进入快路、基址比较和公开 iterator 修复存在。
合法候选命中十个函数；fission 和内层反转各自因行首读取依赖拒绝一个函数。
不合法的域、指令删除、映射和证书仍执行原片段。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make native-memory-multiarray
opam exec --root=/tmp/guard-opam --switch=guard -- make native-memory-affine-maps
```

源范围仍是同布局数组对象的矩形操作。一般仿射 C 循环边界、不同布局、邻居访问及
任意指针缓冲区尚未接入这份源识别器。
