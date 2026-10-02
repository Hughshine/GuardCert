# PolCert 核心接口在当前工具链上的适配

这条可选构建路径使用真正的 PolCert v10 `InstrTy.INSTR` 和 `Loop`，基础库来自 GuardCert 锁定的 CompCert v3.18、Rocq 9.2.0 与 Stdlib 9.2.0。它不再使用 PolCert 仓库中的旧 CompCert、Flocq 和 C 前端副本。

## 输入与复现

`source.lock.json` 锁定 PolCert 提交 `cffdf8112167a6b7b1ef2ca635b04adac1437539`。实际 v10 工作目录还有未提交改动；`source.patch` 保存所需 57 个证明输入相对该提交的变化，每个原始文件都有 SHA-256。`patches/` 保存另外 23 份 Rocq 兼容补丁，两类补丁分别核对哈希。原 PolCert 工作目录保持不变。

在 [工具链环境](../../docs/toolchain.md) 中执行：

```sh
make polcert-proof
```

该目标先检查独立核心和 CompCert 桥接，再恢复锁定输入、完整编译 57 个 PolCert 文件和三个 GuardCert 适配器。默认从锁定仓库克隆；已有 Git 仓库可作为只读对象来源：

```sh
make polcert-proof \
  POLCERT_SOURCE=/home/hugh/research/polyhedral/polcert/work/verified-compilation-v10-driver
```

恢复通过 `git show` 读取指定提交，并应用保存的工作目录补丁，不要求该仓库的当前 checkout 与锁定版本一致。工作副本位于被忽略的 `vendor/PolCert-core`，报告与原始文件副本位于 `build/`。构建不会写入提供的 PolCert 仓库。

成功报告为 `build/polcert-core-report.json` 和 `build/polcert-adapter-report.json`，详细日志为对应的 `*-build.log`。增量构建缓存同时核对输入和 `.vo` 哈希；`make polcert-proof` 明确使用 `--clean`，不接受该缓存作为完整重编译记录。

## 实际接入的证明

| 文件 | 接口与保证 |
| --- | --- |
| [PolCertSchedule.v](../../theories/PolCertSchedule.v) | 直接实例化 `AbstractSchedule`：状态为 `I.State.t`，入口不变量为 `I.NonAlias`，结果关系为 `I.State.eq`，独立性为真正的三项 Bernstein 读写条件。交换性质来自 `I.bc_condition_implie_permutbility`。有限相邻交换证书保持每次源执行的结果模状态等价。 |
| [PolCertLoopGuard.v](../../theories/PolCertLoopGuard.v) | 把实际 `Loop` 实例化为通用条件语言。两个互补的 `Guard` 组成条件选择，证明其执行恰好对应选中的片段。原子检查有 validity/value 编码证书及入口域；通用条件编译器生成 `Loop.stmt`。分别提供 forward preservation 与 backward endpoint refinement。 |
| [PolCertLoopProgram.v](../../theories/PolCertLoopProgram.v) | 提升到实际 `Loop.t` 的 `semantics`，保留原 context 与变量元数据。检查域必须由真正的 `Compat/NonAlias/InitEnv` 入口前提推出。`version_program_refines_endpoint` 接受带条件的候选程序 backward endpoint，并要求元数据一致。 |

`impossible_version` 使用真实 `Loop` 参数测试 `env[0] = 0`，生成 `P ∧ ¬P` 条件。它证明对任意源与候选片段，版本化后的终止执行恰好等于源片段执行，因此候选死分支不需要成立条件以外的执行证明。

`impossible_program` 将同一例子提升到完整的 `Loop.t`。`version_program_refines_unconditional` 可以消费已有的 `Loop.semantics candidate → Loop.semantics source` 证明，但仍要求候选与源的 metadata 对齐；它没有假定真正的优化器自动满足此要求。正向程序定理另外要求同一参数环境下的候选执行证书，不从 backward endpoint 自动推出候选进展。

`metadata_equal_correct` 证明布尔相等检查恰好核对 context 与变量 metadata。`checked_version_refines` 在检查失败时返回源程序，使调用者不必手工给出相等证明。`PolCertLoopGuardFor` 与 `PolCertLoopProgramFor` 允许传入已有 Loop 模块；独立便利实例仍保留原名称。

`Loop.test` 只观察数学整数参数。内存 alias 不能直接变成这种测试；外层语言必须提供可执行检查，并证明接受后建立 `NonAlias` 等入口性质。`encoded_atom` 的域参数允许复用外层已建立的事实，没有把注释当作可信事实。

## 兼容补丁与信任边界

补丁处理旧 tactic、删除或移动的标准库名称、Hint/instance 可见性，以及新版自动化已提前解决的义务。`DomainGCL.build_cdac` 改为显式解构同一带证明规格，避开旧 `Program` 的投影 universe 问题，仍构造同一组实现与正确性字段。没有新增 `Admitted` 或语义公理，也没有削弱原定理陈述。

PolCert/VPL 上游本身声明 impure monad、外部 oracle 等公理，57 文件编译通过并不表示整个上游无公理。三个新增适配器的 `Print Assumptions` 只列出其 `INSTR` 模块参数。加入 metadata 相等检查后，构建核对明确的 19 项接口参数集合；没有额外的全局公理。这是参数化定理，具体 `INSTR` 实例仍须实现这些字段并证明性质。

## 尚需完成

核心路径本身没有调用 `Opt_prepared`；另一个 [真实优化器适配](../polcert-optimizer/README.md) 已提供直接调用与 endpoint 连接。具体 `CState/CInstr` 尚未移植。相邻交换证书不是完整的多面体 schedule validator。`Loop` 版本化定理覆盖终止的 statement 与 `Loop.t` 执行；`Loop.t` 仍是循环 IR 程序，不是完整 C 程序。

要得到完整 C 程序上的多面体优化，还需连接实际优化器证书、证明候选进展、建立数学迭代与固定宽度 Clight 循环的对应、实现可执行 alias/range 检查，并完成区域插入的状态与控制流模拟。已接通 C→Asm 的能力仍是 [条件表达式替换](../../docs/abstract-kernel.md)。
