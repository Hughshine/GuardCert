# 基于 CompCert Mem 的具体多面体指令实例

这个适配实例将一般多面体 validator 的 `INSTR` 参数具体化为实际 CompCert 内存。`GuardMemoryCompiler.compile_memory_regions` 已将真实源循环、实际多面体依赖检查、guard、候选循环与原片段回退接到完整 Csem→Asm 定理。目前完整 C 输入路径支持三种矩形循环体；独立 IR 检查器支持更一般的仿射提案与二维 tiling。两者的支持范围不同。

## 已证明的接口

`GuardMemoryRuntime` 的状态是不可变 cell→物理 location 映射与实际 `Mem`。映射是语言视图；不能在生成的 C 中查询它。一次操作解析实际位置，执行 Mem.load，把加载值交给纯计算，再执行 Mem.store，并保存映射。三项 Bernstein 条件由映射的物理不相交性质推出真实操作的交换。

`flat_array_locations` 只解析某个普通 Mint32 数组的合法一维下标。`flat_array_locations_nonalias` 是闭合证明，没有假定不同逻辑 cell 自然对应不同物理地址。源 Clight 的数组绑定、类型、机器下标范围和偏移仍由具体 bridge 证明。

`GuardMemoryInstr` 实现实际 PolCert `INSTR` 的全部字段。状态关系是映射和 Mem 的精确相等；读写访问函数由结构相等检查绑定到 instruction，实际语义的 footprint 是这些函数计算出的 cell。payload 支持常量、参数、已加载值及 Int.add/sub/mul；失效输入或访问不产生成功执行。`InitEnv` 在这个物理指令实例中只约束参数数量；完整语言 bridge 必须将具体入口 temporaries 与参数值绑定。它没有沿用 CState.valid。

`GuardMemoryRectangles` 从真实 Clight 的纯数组写、同格子读改写、行首读取恢复具体指令执行。`GuardMemoryLoops` 与 `GuardMemoryClightRectangles` 把完整矩形循环的实际执行接到真实 Loop 语义，并重建完整候选执行，保留全部公共 temporaries 和 Mem。

`GuardMemoryPolyhedral` 实例化实际一般仿射和 tiling validator。`guarded_memory_validate_refines` 的输出是精确的状态结果，无遗留 INSTR 语义参数。`validate_memory_equivalence` 对仿射提案进行双向验证；接受时 `validated_memory_equivalence` 给出两种执行方向，因而源执行可以建立候选进展。双向检查是当前可用的构造，不声称是最便宜的算法，也未把它推广到全部 tiling 对应。

`validated_memory_equivalence_at` 保留具体入口参数值；仅用存在量词包装参数的实例级端点不足以建立 Clight 对应。`GuardMemoryPolyhedralRectangles` 证明完整矩形域的点覆盖、唯一性、排序与实际执行对应；`GuardMemoryValidatedRectangles` 用真实双向依赖验证的结果建立 guarded Clight 规则。`GuardMemoryCompiler` 检查源 AST、构造源与交换候选的 IR，消费上述规则并证明 `compile_memory_regions_correct`。定理要求无 alarm 的 `mayReturn (OK assembly)`，结论是原 Csem 到实际 Asm 的 backward simulation。

## 原生检查器与编译器

```sh
# 已有当前 proof profile 和适配模块审计时，可直接执行脚本。
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/build_memory_validator.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_memory_validator.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/build_memory_compiler.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_memory_compiler.py
```

完整依赖构建目标为 `make native-memory-validator` 与 `make native-memory-compiler`。两种提取共用有资源上限的非可信 Fourier–Motzkin 证书搜索；证书由提取的 VPL LCF 检查。错误证书和搜索耗尽均拒绝变换。OCaml 的整数表示转换、文本读取与拓扑排序属于非可信输入侧；检查器验证它们产生的结果。

独立检查器的 JSON 输入经 `scripts/memory_validator_input.py` 转为有大小上限的输入格式；仿射提案执行双向检查，tiling 提案执行实际 `checked_tiling_validate_poly`，验证新增 tile 坐标与域对应。历史的 `AffineValidator.validate_tiling` 只处理同一已有点空间上的调度，不能代替这个检查。独立 IR 接受不构成某个 C 源程序的编译保证。

验证报告为 `build/native-memory-validator/report.json`（25 组提案、847 组独立执行比较）与 `build/native-memory-compiler/report.json`（225 个纯写、345 个读改写、225 个行内依赖正矩形；19 个实际命中 guard 的函数；完整数组及 iterator 出口与 GCC 和独立模型一致）。后者还实际编译、执行资源耗尽与错误证书下保留源循环的程序。

## 构建与假设

已有锁定 optimizer proof profile 时：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_guard_memory.py
```

完整依赖重编译的目标：

```sh
make guard-memory-proof POLCERT_SOURCE=/home/hugh/research/polyhedral/polcert/work/verified-compilation-v10-driver
```

详细报告为 `build/guard-memory-proof-report.json`，构建和假设日志位于 `build/guard-memory-assumptions/`。脚本重编译九个适配模块；直接调用脚本复用此前的 92 文件 PolCert optimizer proof profile，没有重新编译整个 profile。物理数组 nonalias 闭合；指令桥继承 7 项假设，具体 validator 继承其原有 12 项，完整编译器继承 CompCert 与 validator 的并集 42 项。审计要求完整编译器的集合精确等于该并集，没有新增全局公理。默认 C→Asm 编译器的 35 项集合不能直接套到这条路径上。

## 正在接通的边界

一般嵌套仿射域、多语句源循环与任意候选的 C 编码，以及多维 tiling 的完整 C 程序保证仍需闭合。OpenScop export 与 scheduler callbacks 当前安全拒绝；独立检查器直接读取候选 PolyLang 程序，完整 C 编译器自行构造限定矩形的源与交换候选。没有一般多面体 C 编译器或性能结果。
