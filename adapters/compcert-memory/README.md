# 基于 CompCert Mem 的具体多面体指令实例

这个适配实例将一般多面体 validator 的 `INSTR` 参数具体化为实际 CompCert 内存。普通 C→Asm 编译器中的动态矩形与分块规则仍独立可运行；这里推进一般仿射域和外部候选的下一条接入链，尚未替代它们。

## 已证明的接口

`GuardMemoryRuntime` 的状态是不可变 cell→物理 location 映射与实际 `Mem`。映射是语言视图；不能在生成的 C 中查询它。一次操作解析实际位置，执行 Mem.load，把加载值交给纯计算，再执行 Mem.store，并保存映射。三项 Bernstein 条件由映射的物理不相交性质推出真实操作的交换。

`flat_array_locations` 只解析某个普通 Mint32 数组的合法一维下标。`flat_array_locations_nonalias` 是闭合证明，没有假定不同逻辑 cell 自然对应不同物理地址。源 Clight 的数组绑定、类型、机器下标范围和偏移仍由具体 bridge 证明。

`GuardMemoryInstr` 实现实际 PolCert `INSTR` 的全部字段。状态关系是映射和 Mem 的精确相等；读写访问函数由结构相等检查绑定到 instruction，实际语义的 footprint 是这些函数计算出的 cell。payload 支持常量、参数、已加载值及 Int.add/sub/mul；失效输入或访问不产生成功执行。`InitEnv` 在这个物理指令实例中只约束参数数量；完整语言 bridge 必须将具体入口 temporaries 与参数值绑定。它没有沿用 CState.valid。

`GuardMemoryRectangles.rect_memory_write_clight_decode` 从真实 Clight 数组写入恢复这个具体指令的执行及非 alias 性质。它包含实际 Mem.store，保留临时变量，处理同一个 local/global array binding；这仍是单次指令解码，没有把完整循环解码作为已完成结果。

`GuardMemoryPolyhedral` 实例化实际一般仿射和 tiling validator。`guarded_memory_validate_refines` 的输出是精确的状态结果，无遗留 INSTR 语义参数。`validate_memory_equivalence` 对仿射提案进行双向验证；接受时 `validated_memory_equivalence` 给出两种执行方向，因而源执行可以建立候选进展。双向检查是当前可用的构造，不声称是最便宜的算法，也未把它推广到全部 tiling 对应。

## 构建与假设

已有锁定 optimizer proof profile 时：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_guard_memory.py
```

完整依赖重编译的目标：

```sh
make guard-memory-proof POLCERT_SOURCE=/home/hugh/research/polyhedral/polcert/work/verified-compilation-v10-driver
```

详细报告为 `build/guard-memory-proof-report.json`，构建和假设日志位于 `build/guard-memory-assumptions/`。脚本始终重编译四个适配模块；直接调用脚本复用此前的 92 文件 PolCert optimizer proof profile。它没有重新编译整个 profile，也没有提取／执行一般 validator。这里继承 CompCert 和实际 VPL validator 的既有假设；不能将默认 C→Asm 编译器的 35 项假设集合直接套到一般 validator 上。审计分别比较指令性质与 CompCert 基线、适配端点与实际具体 validator 基线。

## 正在接通的边界

一般 validator 的原生提取与 oracle 实现、完整源循环解码、已验证候选循环生成、入口前提编码和完整 Csem→Asm 局部规则仍需闭合。OpenScop export 与 scheduler callbacks 当前安全拒绝；调用者直接提供源和候选 PolyLang 程序。没有原生一般多面体优化或性能结果。
