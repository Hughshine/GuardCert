# CInstr 入口审计与显式参数实例

对锁定的 v10 `CState.v:597` 的审计发现，旧 `valid` 的定义对所有 block 和 type 作全称量化：同一个变量查找结果必须同时等于所有这些 block/type。取两个不同 block 即可推出矛盾。

`PolCertCompatibilityAudit.v` 机械化证明 `legacy_valid_uninhabited`，该定理闭合于全局上下文；进一步证明旧 `CInstr.Compat` 只能接受空变量声明，旧 wrapped `Loop.semantics` 在非空声明时没有执行。因此，使用非空数组声明的旧 wrapped 语义作为完整程序入口会得到空的适用域。这一问题与旧 `CTy` 不支持标量参数是两个独立限制。

本项目未修改上游源码或锁定输入。现有原生双写重排使用真实的 raw `CInstr.instr_semantics`、Bernstein 定理和 Clight store 执行，不依赖旧的非空 `Compat`，因而不受此入口问题影响。泛化的优化器定理仍成立；具体实例必须证明入口非空且真实可执行。

## 新的显式语言实例

`PolCertReadOnlyContext.v` 是参数化的 `INSTR` 实例构造。状态由只读参数快照和底层指令状态组成，基本指令保留参数快照并使用底层真实执行。非别名、访问检查与 Bernstein 交换证明从底层实例提升；兼容性由语言作者显式提供。

`PolCertCInstrContext.v` 选择真实 CInstr 为底层，使用存在性数组布局与 writable permission 证据作为新的兼容性，并从实际 Clight temporaries 的已定义 `Vint` 建立数学参数快照。快照是证明中的观察，无需在程序里分配额外内存。这个模块定义新的具体语义实例，没有宣称旧 wrapped 语义已被修复。

`PolCertCInstrContextExamples.v` 从实际 `Mem.alloc`、数组权限与 `Mem.store` 构造执行见证：非空数组声明、来自 temporary 的标量参数以及一次循环迭代，共同产生 `A[0]=7`。另外证明相应旧 wrapped 实例没有执行。

审计将新具体证明与实际 CInstr/Clight 基线比较，没有新增全局公理。报告为 `build/polcert-memory-context-adapter-report.json`。这一实例尚未接入完整源循环解码、候选 lowering 或原生优化器驱动。

```sh
make polcert-memory-proof POLCERT_SOURCE=/path/to/verified-compilation-v10-driver
```

主线是以 PolCert 为功能参照，在 CompCert 中实现有动态前提的多面体优化，见 [接入目标](polcert-integration-target.md)。此审计约束复用旧 CInstr 模型的路线；允许采用自建状态与 IR，不要求保留旧模型。任何路线都必须建立非空的真实入口，并完成源循环解码、候选 lowering 与完整程序证明。
