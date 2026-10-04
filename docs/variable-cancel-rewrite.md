变量乘除 rewrite 把 signed32 表达式 `(x*y)/y` 在已编码条件下替换为 `x`。这份说明面向要添加 GuardCert 插件的编译器研究者；源与候选仍遵循 CompCert 的实际机器整数语义。

```c
if (y != 0 && INT_MIN <= (long long)x * y
           && (long long)x * y <= INT_MAX)
  result = x;
else
  result = (x*y)/y;
```

这是生成检查的示意；实际 Clight 使用 `generated_decision_tree` 的条件树，再由已有表达式上下文 lowering 安装到源位置。源码位于 `prototype/affine-nest/ClightVariableCancel.v`，复用语言无关的性质接口以及 CompCert Clight 实例。

插件定义两个原子性质 `VariableNonzero` 与 `VariableProductRange`。`variable_cancel_dimension` 提供它们的语义及 `option bool` 决策证明，`variable_cancel_primitives` 证明每个原子的实际 Clight 检查与该决策对应。检查代码读取两个源 temporary；正常源表达式求值保证它们是已定义的整数。乘积检查提升到 signed64，两个 signed32 操作数的乘积总能表示，检查自身不会溢出。

`variable_cancel_rule` 通过 `encoded_decision_rule` 提供源、候选、两个性质的合取、源定义性推出检查定义域，以及条件成立时的局部等价。`generated_decision_tree` 自动合成短路检查；`encoded_decision_rule_sound` 将检查编码正确性与局部等价组合成 `expression_contract`。

`select_variable_cancel` 检查完整表达式 AST 与类型，包含除数确实为第二个乘法操作数的要求。插件可在 `(x*x)/x` 上实例化；暂只识别 signed32 temporary，其他形式交给已有规则或保留源。`select_all_guardcert_rewrites_sound` 接入递归表达式上下文，`guardcert_scalar_rewrites_correct` 接入 Clight 程序，最终由两个完整编译入口的 Csem→Asm 定理承接。

条件是可证明的充分条件，未声称最弱。比如 `x=INT_MAX,y=2` 时，源表达式按 word 乘法得到 `-1`，直接返回 `x` 会改变结果，生成的范围检查会选择原表达式。`examples/native_variable_cancel.c` 还覆盖外围算术、相同操作数、除零的源前置分支以及由源短路控制使除法不可达的路径。

2026-10-04 的完整 audit 编译 101 个模块，两个编译器 stamp 各记录 712 份证明源、8 份 native 源。`variable_cancel_value` 无假设，规则和递归 selector 沿用六条 Clight 源语义假设；两个整程序定理仍为已有 42 条假设，无新增全局公理。

`make native-variable-cancel` 分别验证统一入口和条件搜索入口，各运行 602 次实际汇编调用，并与独立 Word 模型及 GCC `-fwrapv` 参照一致。独立的实际 Clight 分支插桩在每个入口观察到 200 次候选、175 次回退和 227 次源控制流未到达表达式；短路使除法不可达时，新 guard 的执行次数为零。汇编结果与 GCC 诊断分别记录，不混为同一证据。

复现时先用已配置的 Rocq 9.2 工具链执行：

```sh
make affine-nest-prototype-proof
make guardcert-compiler guardcert-conditioned-compiler
make native-variable-cancel
```

同一统一编译器本阶段的回归包括原有循环／内存服务和这条 rewrite，共 19,352 次实际汇编调用；条件搜索编译器为 10,814 次。完整分支诊断分别为 9,787 和 5,783 次，分别对应各自二进制。
