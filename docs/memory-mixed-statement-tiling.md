# 混合读写语句列表的完整 C 分块

`GuardMemoryOperationsCompiler.compile_memory_operations_regions bi bj` 将真实 C 矩形循环中的非空语句列表接到多面体依赖检查、四层二维分块候选、运行时 guard、源片段回退和 CompCert 后端。完整入口的 `compile_memory_operations_regions_correct` 证明无 alarm 的 `mayReturn (OK assembly)` 建立原 Csem 到目标 Asm 的 backward simulation。定理量化任意循环体列表长度和所有块大小，没有二／三／四语句的证明上限。

每条语句可以独立选择下列三种模式；数组布局和公开 iterator 相同，payload 的行系数与常数偏移可以不同。

```c
// a 有 120 个 int；n、m 是运行时参数。
for (; i < n; ++i) {
  for (j = 0; j < m; ++j) {
    a[i*10+j] = i*37+j+7;
    a[i*10+j] = a[i*10+j] + (i*11+j+19);
    a[i*10+j] = a[i*10] + (i*23+j+3);
  }
}
```

这三条语句会产生实际依赖。验证器检查真实写地址与读地址，同时将语句位置作为时间戳的一维；同点中的写入、更新和行首读取保留语句顺序。两个文本相同的更新也有不同位置，不能合并成同一个点。前端先提出模式与布局，再对完整、带类型的源 AST 核对，不把模式提议当成正确性证据。

当前入口 guard 从已核对的数组布局生成 `i==0 && 0<n && n<=12 && 0<m && m<=10`。条件求值的顺序具有证明：外层不进入时不读取 `m`，因而允许源未读取、未初始化的内层边界。非零入口、零／负边界或验证失败都保留原片段。块大小和辅助边界另外经过静态 signed32 区间检查；候选使用八个新增私有 temporary，尾块跳过无效点，结束时恢复公开 `i=n,j=m`。

证明链复用一般语句编号、覆盖与排序的 `GuardMemorySequence*` 端点。`GuardMemoryOperationsClight` 将源中每一次实际读取、计算和写入解码到具体 CompCert Mem 上的逻辑指令链。`GuardMemoryOperationsTiledClight` 使用一般单数组 `GuardMemoryFlatArrayBackend` 生成候选中的真实 load/store，保持精确 Mem，并在完整宿主中保护所有源 temporary。条件正确性与检查编码继续通过 `encoded_private_rule` 组合。

37 个具体适配模块和七个 lowering 模块已经统一重编译并完成假设审计。物理数组 nonalias 没有全局公理；指令桥继承原来的 7 项假设，validator 与多语句执行进展继承原来的 12 项，完整编译器恰好继承 CompCert 与 validator 的 42 项并集，没有新增公理。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_guard_memory.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/build_memory_compiler.py --operations
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_memory_operations.py
```

`make native-memory-operations` 复现完整构建与运行验证。提取的编译器路径是 `build/compcert-memory-operations/ccomp`；配置为 `GUARDCERT_TILE_ROWS` 和 `GUARDCERT_TILE_COLUMNS`，默认 4×4。编译器 `.guard-build.json` 绑定证明来源和实际可执行文件。原生报告位于 `build/native-memory-operations/report.json`。

实际提取入口通过 1×1、2×3、4×4、5×7、17×13 五组块大小，共 5325 个正动态矩形；10 个函数实际生成四层快路。每组的 1564 行完整数组与公开 iterator 输出都与 GCC 和独立源模型一致。测试包括两／三／四条语句、重复更新、行首依赖、两个布局、局部／全局数组、goto、外围循环和源不读取的未初始化内层边界。非正块大小、可能溢出的块大小、资源耗尽和错误证书五条拒绝路线也实际编译、执行并保留源行为。

源入口目前只支持上述三类矩形模式在一个固定布局数组上的任意非空列表。一般仿射域、任意源表达式、多个数组、偏移访问和外部调度驱动的完整 C 接入仍需实现；通用后端支持的更多指令不自动扩大源解码范围。该路径没有性能测量结论。
