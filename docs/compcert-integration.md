# 真实 CompCert 接入

最新路径已将通用性质接口生成的短路条件树接入 Clight 宿主，并提取 `RegionCompiler.compile_property_regions` 作为当前 Driver 入口。实际 overflow 取消规则使用这条路径，完整程序定理仍为 `Csem → Asm` backward simulation。新增有限语句区域宿主与局部证书接口见 [clight-statement-regions.md](clight-statement-regions.md)。其他接口、验证结果及未完成的 PolCert 适配见 [abstract-kernel.md](abstract-kernel.md) 和 [validation.md](validation.md)。下面记录的 `compile_common_rewrites` 是上一阶段的可用入口。

2026-10-02：已实现 Clight 分支版本化 pass，并证明扩展编译器从原始 CompCert C 到 Asm 的 backward simulation。提取后的编译器实际编译了 C 文件，生成汇编经 GCC 汇编、链接后运行，输出与 GCC 编译的原程序一致。工具链仍为已锁定 CompCert v3.18、Rocq 9.2.0。

同日扩展：新增表达式版本化 pass 和四个常见 rewrite，当前可执行编译器入口是 `compile_common_rewrites`，先执行既有分支 pass，再执行表达式 pass。两者共享编码／合成证明，完整编译器仍提供不带源程序 presumption 前提的 `Csem → Asm` backward simulation 和规格保持。接口、实例及实际内存雏形详见 [common-rewrites.md](common-rewrites.md)。下面保留首个分支适配器的契约和证据。

## 编译链与定理

```text
Csyntax / Csem
  → SimplExpr
  → Clight semantics1
  → SimplLocals
  → Clight semantics2
  → ClightGuard.transform_program select
  → ClightExprRewrite.transform_program select_common（新入口）
  → Cshmgen → Cminorgen → CompCert 原有后端
  → Asm
```

[GuardCompiler.v](../theories/GuardCompiler.v) 定义了实际执行的 `compile_with_guards`，并证明：

```coq
compile_with_guards select p = OK asm ->
backward_simulation (Csem.semantics p) (Asm.semantics asm).
```

泛型定理要求 `select` 每次返回的条件具有 `guard_contract`；具体的 `compile_no_wrap_correct` 已用插件证明消去这个要求。最终定理没有“不发生溢出”的源程序前提。检查不接受时执行原条件及原分支。

`compile_with_guards_preserves_spec` 进一步证明：若原程序满足排除出错行为的规格，汇编也满足该规格。未定义行为沿用 CompCert 的行为精化关系，不声称任意错误程序的行为完全相等。定理起点是 CompCert C AST，终点是形式化 Asm 程序；C 文本解析、提取、Asmexpand、打印、系统汇编器、链接器及外部函数实现仍沿用上游可信边界。原生运行检查没有扩大定理终点。

## 插件使用接口

[ClightEncodedRule.v](../theories/ClightEncodedRule.v) 的 `encoded_branch_rule a g` 包含：

| 字段 | 插件提交的内容 |
| --- | --- |
| `rule_modulus`、`rule_view` | word 模数、临时环境到 presumption 状态的解释 |
| `rule_obligation`、`rule_encoding` | 独立语义义务 Q，以及 DSL 含义与 Q 的双向对应 |
| `rule_lowering` | 真实 Clight 条件 g 求值、转为 bool 后，等于既有 condition 合成器的结果 |
| `rule_local_correct` | 原条件有定义且 Q 成立时，其 bool 结果必为 false |

`encoded_branch_rule_sound` 将证书转换为底层 `guard_contract`。插件的识别器还要证明识别到的 AST 就是证书覆盖的原条件和机器条件。之后统一复用 `transform_program_correct1/2` 和 `compile_with_guards_correct`，不重新证明调用栈、控制上下文或后端组合。

这个首个 IR 适配器处理的候选形状固定为原 if 的 else 分支：

```text
if a then L else R
    ↓
if g then R else (if a then L else R)
```

因此候选 R、回退的原条件 a 和原分支 L/R 由实际 AST 直接绑定。它目前没有接受任意 R′ 的关系式区域接口；两次写操作交换和一般循环算法仍不能直接接入这个适配器。独立宏步模型的证书也没有被直接转换为 Clight 证书。

## 已实现实例

[ClightNoWrap.v](../theories/ClightNoWrap.v) 提供：

```text
原条件：unsigned32(x + 1) < x
Q：unsigned(x) + 1 < 2^32
presumption：NoOverflow(Scalar(0) + Literal(1))
生成条件：x <= UINT_MAX - 1
候选：原 else 分支
```

`no_wrap_rule` 通过上述编码接口构造证书。`no_wrap_synthesis_value`、`no_wrap_lowering_correct` 证明生成的 Clight 表达式与既有合成结果一致。overflow 有效位由安全的 unsigned 比较表达，不依赖未建模的 CPU flags。识别器检查同一临时变量、literal one 和各处确切类型，避免把 signed 加法或 C 整数提升混入该规则。

[ClightIntegrationExamples.v](../theories/ClightIntegrationExamples.v) 另验证了恒假 literal 分支和永不接受的 guard；两种识别器共享端到端编译器定理。其证据包括实际 Clight 步骤，而不是独立 Python 解释器。

## 上下文和进展

[ClightGuardProof.v](../theories/ClightGuardProof.v) 的状态关系保留相同环境、临时值与完整 CompCert 内存，结构性地对应语句、函数和续体。它覆盖函数调用、外部事件、return、break、continue、switch 和 goto。候选与回退分支可包含调用和可能发散的循环；这里没有有限 region 宏步假设。

每个原程序步骤对应目标程序至少一个步骤；guard 拒绝的 if 步骤对应两个静默步骤。证明使用 CompCert 的 `forward_simulation_plus`，因此无限执行也有进展保证。

版本化会复制 else 分支。若 L 或 R 内有 label，复制可能改变 `find_label` 的首次匹配，外部 goto 也可能绕过入口检查。`label_free` 因此排除这些区域，`find_label_match` 证明整程序 label 查找与续体对应。程序其他位置的 label/goto 仍被支持。

## 运行与实际检查

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make clean
opam exec --root=/tmp/guard-opam --switch=guard -- make check-integration
```

新环境先按 [toolchain.md](toolchain.md) 安装隔离工具链，并用该环境的 opam root 执行相同目标。

`make check-compcert` 编译证明、运行已有独立回归；`make check-integration` 还提取并构建 `compile_common_rewrites` 编译器，再运行 [native_guard.c](../examples/native_guard.c) 和 [native_rewrites.c](../examples/native_rewrites.c)。构建脚本在 `build/compcert-guard` 中复制上游源码、修改一处 OCaml 编译函数调用；`vendor/CompCert` 的源码及 sibling PolCert 均不修改。所有提取 roots 在一次 `Separate Extraction` 中生成，避免分次提取覆盖共享模块的不完整接口。缓存用全部工程证明源码和编译器二进制 checksum 检查。

实际输出：

```text
x=0 probe=22 loop=144 label=22
x=1 probe=22 loop=144 label=22
x=254 probe=22 loop=144 label=22
x=255 probe=22 loop=144 label=22
x=4294967294 probe=22 loop=144 label=22
x=4294967295 probe=11 loop=122 label=11
external-goto=11
```

生成的 Clight dump 中有两处 `x <= 4294967294U` 的版本化区域，带 label 的第三处保持原条件。报告、dump、汇编和运行输出在 `build/native-demo/`。这些检查验证了提取和驱动确实使用新 pass，不替代普遍量化的语义保持定理。

`Print Assumptions` 对原版 `Compiler.transf_c_program_correct`、`compile_no_wrap_correct` 与 `compile_common_rewrites_correct` 显示相同的 35 个假设名。没有新增公理或 `Admitted`；这里继承了上游的外部函数、后端 oracle、选项以及逻辑假设，不声称 Clight 接入后的定理均为 `Closed under the global context`。
