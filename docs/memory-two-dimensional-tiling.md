# 实际 C 程序的二维分块

`GuardMemoryTiledCompiler.compile_memory_tiled_regions bi bj` 从实际 C 输入识别纯写矩形循环，构造源与分块候选的 PolyLang 表示，消费真实 VPL 依赖及域对应检查，生成四层 Clight 循环、尾块 guard 和原片段回退，最后调用 CompCert 后端。`compile_memory_tiled_regions_correct` 证明无 alarm 的 `mayReturn (OK assembly)` 建立原 Csem 到目标 Asm 的 backward simulation。

例如 `a[i*10+j] = i*37+j+7`，`a` 有 120 个 int 元素，动态上界是 `n,m`。从数组布局导出的安全入口检查为 `i==0 && 0<n && n<=12 && 0<m && m<=10`，检查顺序沿用源执行的定义性证明：外层不进入时，不读取可能未初始化的 `m`。接受后，候选在 tile 行、tile 列、实际行、实际列四个维度执行；`i<n` 与 `j<m` 的尾部检查跳过不满块中的无效点。结束时恢复源公开的 `i=n,j=m`。辅助计数器和边界使用八个私有 temporary。

块大小是未受信任的编译参数。非正值被拒绝；生成代码的区间检查保证块数计算、块边界和计数器在 signed32 范围内。这个检查静态使用源布局导出的最大动态范围，因此有保守拒绝。真实非负 floor division 的编码由 `ClightPositiveDivision.v` 和 `PolCertAffineClight.v` 证明；不能把任意数学除法直接当成 C 除法。

证明链的具体部分是：

- `GuardMemoryArrayBackend` 把一般结构化 Loop 中的两个下标表达式编码成真实数组写，所有后端字段均已证明。指令限于已绑定数组的矩形纯写 payload；Loop 的下标可含已检查的仿射运算和正整数除法。
- `GuardMemoryLoopTrace` 证明实际 Loop 执行与有限事件轨迹等价。轨迹用于证明，不参与提取编译器的运行。
- `GuardMemoryTiledRectangles` 证明新增 tile 坐标、完整域、尾块、有限点覆盖、唯一性和排序。
- `GuardMemoryTiledExecution` 把真实依赖验证建立的候选 PolyLang 执行重建为实际四层 Loop 执行。
- `GuardMemoryTiledClight` 连接源 Clight、该验证结果、具体数组后端和公开 iterator 出口；`encoded_private_rule` 复用性质编码与完整程序片段宿主。
- `GuardMemoryTiledCompiler` 检查源 AST、分配私有 temporary、消费证书，再连接 SimplExpr、SimplLocals、片段替换及 CompCert 后端。

完整程序宿主保护所有源标识符上的 temporary 值和精确 Mem，允许候选改变新增私有状态，并覆盖调用、goto、switch 与外围循环。依赖检查、范围检查或源匹配失败时保留源片段。这个入口目前支持矩形纯写二维分块；一般仿射域、多语句与读改写的 tiling 仍未实现。既有依赖检查的矩形交换入口另支持同格子更新和行内依赖。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_guard_memory.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/build_memory_compiler.py --tiling
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_memory_tiling.py
```

完整依赖目标是 `make native-memory-tiling`。提取驱动默认使用 4×4，可通过 `GUARDCERT_TILE_ROWS` 和 `GUARDCERT_TILE_COLUMNS` 配置。编译入口的定理量化所有块大小；OCaml 参数读取不承担验证义务。

该矩形分块提交 `be95243` 的审计重编译七个 lowering 模块与十六个具体适配模块；后续统一审计已增加条件域和多语句进展模块。完整 C→Asm 定理的全局假设恰好等于 CompCert 与实际 validator 的并集 42 项，没有新增公理。支持范围、实际执行结果和来源哈希分别记录在 `build/guard-memory-proof-report.json`、`build/native-memory-tiling/report.json` 和编译器 `.guard-build.json` 中。

实际提取编译器已验证 1×1、2×3、4×4、5×7、17×13 五组块大小，共 1125 个正动态纯写矩形；同时比较既有 570 个读改写／行内依赖输入的源回退。六个函数中的实际四层 Clight 候选和共享回退均被检查，包含不满块、整个域位于单块、局部／全局数组、goto、外围循环以及未初始化但源不读取的内层边界。完整数组和公开 iterator 出口与 GCC 及独立源模型一致。非正块大小、可能溢出的块大小、搜索耗尽和错误证书五条拒绝路径均实际编译、执行并保留源行为；没有性能结论。
