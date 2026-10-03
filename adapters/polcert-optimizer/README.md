# 真实 PolCert 优化器接入

这条可选路径移植并调用实际 v10 `PolOptCorrect.Opt_prepared_correct`，在 GuardCert 锁定的 CompCert 基础库与 Rocq 9.2 上编译。程序包装器使用 `PolIRs` 自己的 Loop 模块，不会另造一份无法与优化器输入统一的归纳类型。

```sh
make polcert-optimizer-proof \
  POLCERT_SOURCE=/home/hugh/research/polyhedral/polcert/work/verified-compilation-v10-driver
```

不提供 `POLCERT_SOURCE` 时，与核心适配器一样从锁定 Git 仓库读取输入。`source.lock.json`、`source.patch` 和 35 份兼容补丁锁定 92 个实际证明文件，保留指定 v10 工作目录中所需的修改。源码恢复与 `.vo` 构建位于独立的 `vendor/PolCert-optimizer`；不写入原 PolCert 仓库，也不覆盖核心适配器的构建。

优化器桥接所需的两个通用适配器在 `build/polcert-optimizer-adapters` 以 `GuardPolCert` 名称重新编译，算法和证明源来自 `theories/`。这里只有 `PolCertLoopProgram.v` 的依赖 import 被确定地改为这个隔离名称；编译器与标量 Clight 证明继续使用 `Guard`。

## 接口与保证

`PolCertLoopProgramFor I ExistingLoop` 接受调用者现有的 Loop 模块。插件给出性质维度、编码原子、条件公式和入口域证据。metadata 相等由 `metadata_equal` 检查，证明依据来自实际 `INSTR` 的标识符与类型相等接口；不匹配时返回源程序。

`PolCertOptimizer P Core` 使用真实 `POLIRS` 与 `POL_OPT_CORE`。其 `optimize_version` 先调用 `Core.Opt_prepared`，再输出 metadata 检查后的 guarded Loop 程序。`optimize_version_correct` 直接使用实际 `Opt_prepared_correct`，证明：

```text
成功返回 target
∧ 入口域来自 source 的 Compat/NonAlias/InitEnv
∧ target 的 Loop.semantics 终止执行
⇒ source 存在相应终止执行，结果为 State.eq
```

runtime guard 为 false 或 unknown 时运行源 body；metadata 不匹配是优化时的静态拒绝。此定理沿用上游 alarm monad 的成功返回契约，没有声称在 optimizer 报警后仍成功返回源程序。候选进展、无报警保证与原生提取需要另证。

## 兼容范围与待完成工作

35 份补丁包括核心适配的 23 份、优化器兼容的 9 份、访问维度修复的 2 份，以及闭合拓扑排序提案的 1 份。额外补丁恢复标准库名称、数字 notation scope、Proper instance 可见性、replace 的证明方向与显式关系运输。组合 validator 的未使用转发别名被移除，以避免 Rocq 9.2 的 module-substitution 异常；实际字段直接指向原模块。`PolOpt` 中未使用的 `Convert/CInstr` import 被替换为仍需的 `Csyntax` import。访问维度修复将 ExtractorFrontend 的读写系数补齐到指令实参个数，符合 AffineValidator 的检查契约；ExtractorCorrect 的对应叶子表示同步更新。拓扑排序提案函数改为有 256 节点上限的具体定义，其结果继续由原排列和排序检查器验证；不再留下外部提案函数的全局参数。其余优化器算法和正确性端点不变。此次修改后的 92 个依赖文件已重新编译。

`PolCertOptimizerRegion.v` 现在提供[端点到完整程序的证书接口](../../docs/polcert-optimizer-regions.md)：实际优化器后向端点、候选进展、源结果唯一性与语言桥接共同建立局部规则，再复用完整 Clight 区域宿主和 Csem→Asm 定理。选择器核对整个源 AST。这个参数化定理已编译，但具体完整循环证书尚未实例化，原生驱动也尚未调用 `Opt_prepared`。

具体 CInstr/Clight 片段桥接在隔离的 memory profile 中另行验证。[入口审计](../../docs/polcert-context-audit.md) 发现旧非空声明的 wrapped CInstr 语义不可执行；新的只读参数实例提供真实分配内存上的执行见证。后续循环主线允许直接使用 CompCert 语义重新实现，而不受必须保留 CInstr 表示的约束。

源 `Loop.semantics` 的 `NonAlias` 等前提仍然存在。Loop 参数 guard 没有消除这些前提，也不能读取内存 alias。未来外层 Clight adapter 必须在接受路径上建立 Loop 入口关系，并在拒绝路径直接执行原 Clight 区域；不能假定 alias 失败时仍可通过同一 Loop wrapped semantics 描述原代码。

上游 VPL 保留 monad、oracle 与经典逻辑等既有假设。构建比较实际端点与新增适配器的 `Print Assumptions`；新增依赖只允许 metadata 相等所需的 `INSTR` 接口字段，不接受新的全局公理。新增区域端点的假设恰好是优化器与 CompCert 基线的并集。报告为 `build/polcert-optimizer-report.json`、`build/polcert-optimizer-adapter-report.json` 和 `build/polcert-optimizer-region-adapter-report.json`；详细日志为对应的 `*-build.log`。
