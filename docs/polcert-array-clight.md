# 从实际 CInstr 数组到 Clight 执行

`PolCertArrayClight.v` 实例化真实 `CInstr/CState`，为嵌套 Loop lowering 提供具体指令后端。`compile_array_nested` 是纯语法函数：输入数组声明、参数 layout／区间、live frame、scratch pool 和实际 Loop，返回 Clight statement 或 `None`。它不接收运行时状态或环境证明。

正确性定理另行要求运行时证据：参数 temps 与数学环境一致、入口 range guard 接受、局部数组环境与声明一致、真实 Loop 执行，以及具体内存 view。`compile_array_nested_steps` 返回实际 Clight 的正常 `star`，保持同一函数／continuation、公共 temporary frame 和结果内存 view。这里的指令执行由真实 load/store 证明，最终定理没有 `I.instr_semantics` 或额外执行 oracle。

## 已支持的语法与性质

第一版接受局部、普通 signed-32 一维数组。索引为常量或指令操作数；复合 may-affine 索引目前拒绝。右值支持 int 常量、操作数、数组读取，以及整数 unary/binary 运算；浮点常量和 `Oabsfloat` 拒绝。source 的整数运算沿用 CompCert 的机器整数语义。

数组尺寸须满足 `0 < count <= Int.max_signed` 和 `4*count <= Ptrofs.max_unsigned`。实际 `CState.calc_offset` 的成功访问建立 `0 <= index < count`，从而证明 signed 索引、指针偏移和整个 Mint32 访问都可表示。最后一项包括当前 CompCert `loadv/storev` 的 `offset + size_chunk <= Ptrofs.modulus` 检查。没有把数学偏移直接当成机器指针。

`PolCertMemoryModel.v` 的 view 是实际 `CState.eq`，其中内存关系为双向 `Mem.extends`。读取运输保持同一个 value；写入运输构造当前 Clight 内存中的实际 `Mem.store`，并保持结果 view。不同前端的函数环境类型不必相等：本实例只访问局部数组，整数操作和 int 元素大小不依赖 composite 环境。

## 定义性与入口边界

`CInstr.IassignSem` 没有单独执行 Clight 的 C cast，可能把一次未初始化读取的 `Vundef` 写入数组。后端证明成功的整数运算产生 `Vint`，因此接受 `A[i] = B[i] + 1` 等形式；直接 `A[i] = B[i]` 目前返回 `None`，还需一个读取值已定义的证书。这个拒绝也覆盖已初始化的直接拷贝，是明确的保守限制。

当前旧 `CTy` 解码器拒绝标量 `type_int32s`。另一个独立问题是旧 `CState.valid` 不可满足，使非空声明的旧 wrapped Loop 无执行。[入口审计与新实例](polcert-context-audit.md) 给出机械化反证，并定义显式的只读参数快照与存在性数组兼容性；实际分配内存上的 wrapped 执行见证已成立。上游旧语义没有被修改，这个新实例仍需完整源循环与候选桥接。

`CState.NonAlias` 是不同变量位于不同内存块的性质。当前数组后端没有将同块中的 disjoint slices 或任意 pointer 参数编码到这个 state。通用框架允许语言实例提供更精细的 footprint 性质，现有实例尚未实现它。

## 具体例子与验证

`PolCertArrayExamples.v` 检查 `A[i] = B[i] + 1`、单层数组循环和内层上界依赖外层 iterator 的两层循环。拒绝例子包括 direct copy、无效数组尺寸、live counter 冲突和复合索引。

执行例子从真实 `Mem.alloc` 建立两个数组，实际 store 初始化 `B[0]=7`，构造真实 `CInstr` 执行及生成 Clight 的正常执行，并证明结果内存中的 `A[0]=8`。内存访问使用 CompCert 的权限和 load/store 定理；纯编译例子通过 `vm_compute`。这些例子没有提供一个人为假设的 instruction execution record。

```sh
make polcert-memory-proof POLCERT_SOURCE=/path/to/verified-compilation-v10-driver
```

`build/polcert-memory-adapter-report.json` 比较实际 CInstr/CState/Clight 的上游假设与新端点，记录来源哈希与所有证据边界。具体执行端点继承六个 Clight 假设；实际 Bernstein 基线另有上游 proof irrelevance。新增全局公理和指令接口假设均为空。

这仍是具体 Loop→Clight 的片段端点。它尚未证明 source Clight 区域提取、目标进展、私有 temporaries 的完整函数声明及任意外围程序的区域替换 simulation；`Opt_prepared` 也尚未进入原生 C→Asm 入口。共享表达式 lowerer 已支持非负分子除以正常数的 Div；本旧 CInstr 实例尚未重新验证新增能力，Mod/Min/Max 和多维索引的 lowering 仍须扩展，不能据此声称已支持全部 tiling 输出。
