# 实际 CInstr/CState 的数组内存实例

这份隔离输入使用与核心／优化器适配相同的 PolCert v10 提交 `cffdf8112167a6b7b1ef2ca635b04adac1437539`。锁定的闭包是实际 `src/CInstr.v` 与 `polygen/Loop.v` 的并集，共 60 个文件。`source.patch` 保存所需工作树改动；所有原始文件、源码补丁与兼容补丁都有 SHA-256。sibling PolCert 工作树未被修改。

在锁定工具链中运行：

```sh
make polcert-memory-proof POLCERT_SOURCE=/path/to/verified-compilation-v10-driver
```

目标恢复输入，完整重编译 60 个实际证明文件，再编译具体内存 view、数组指令后端和嵌套循环端点。报告是 `build/polcert-memory-adapter-report.json`。核心与优化器适配的 `.vo` 保持独立；共享桥接文件在本 profile 的 `GuardPolCert` 命名空间内重新编译。

新增三份兼容补丁使用当前 `Ctypes.type_eq`、显式 `Z_scope`、当前 operator／value equality，并给上游重复 memory binder 使用不同名字。旧定制 AST 的四个名字交换函数改成 `C_INSTR_NAMES` 参数；它们没有实现内存或指令执行。缺失名字的 exporter 返回 `None`，不再调用 stock CompCert 中不存在的 `free_ident`。`DecimalNames` 为独立例子提供具体数据函数；未验证与 PolCert OCaml 文件交换协议的兼容性。

没有修补 `CInstr` 的实际赋值语义或 `CTy` 的标量解码行为。`CTy.of_compcert_arrtype type_int32s = None` 已由 Rocq 核对，标量符号参数的 `InitEnv` 路径仍须适配。具体数组实例和其他边界见 [数组桥接说明](../../docs/polcert-array-clight.md)。

原始 Bernstein 可交换性、状态等价稳定性和 non-alias 保持性证明均重新编译。假设审计将新增端点与实际 `CInstr`／`CState` 和 Clight 端点比较；当前新增全局公理与抽象指令接口假设均为空。
