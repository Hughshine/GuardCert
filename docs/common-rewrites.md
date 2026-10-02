# 常见 rewrite 的接口与接入

2026-10-02：表达式 rewrite 已接入实际 Clight pass、`Csem → Asm` 定理和提取后的编译器。当前实例都针对确切的无属性 unsigned32 临时变量。它们验证框架的可用性，不代表这些小例子的运行时版本化一定能带来收益。

## 变换族与现有支持

| 变换 | 足够前提 Q / presumption | 实际机器检查 | 接入程度 |
| --- | --- | --- | --- |
| `x/y → x>>1u` | `unsigned(y)=2` / `Equal(Scalar(0),Literal(2))` | `y==2u` | Clight、Csem 到 Asm、原生运行 |
| `x%y → x&1u` | 同上 | 同上 | Clight、Csem 到 Asm、原生运行 |
| `(x+x)/2u → x` | 数学整数和小于 `2^32` / `NoOverflow(Scalar(0)+Scalar(0))` | `x<=2147483647u` | Clight、Csem 到 Asm、原生运行 |
| `x-x → 0u` | `True` / `Truth` | literal true | 同一接口；Clight、Csem 到 Asm、原生运行 |
| 消除 `(x+1u)<x` 的 then 分支 | 数学整数和小于 `2^32` / `NoOverflow(Scalar(0)+Literal(1))` | `x<=4294967294u` | 既有分支 pass；与表达式 pass 组合 |
| literal 恒假分支、永不接受的 guard | `Truth`、`Falsity` | literal true、false | 既有实例共享泛型端到端定理 |
| 跨 store 提前 load | 实际 byte ranges 不相交 / `Disjoint` | 已证明合成 condition 的接受含义 | CompCert Mem 局部端点证明；未接 Clight 或可执行编译器 |

这里把“候选算法正确”和“条件可执行”分成两个义务。例如 unsigned32 的 `(x+x)/2u` 总是有定义，但当 `x=2147483648` 时结果为 0；无条件变成 x 会错。检查失败后必须保留原加法及除法。除数 specialization 也保留所有非 2 的除数，包括原程序的未定义情况；其正确性仍是 CompCert 的行为精化。

## 表达式插件提交什么

[ClightExprRule.v](../theories/ClightExprRule.v) 中的 `encoded_expression_rule source guard candidate` 暴露这些字段：

| 字段 | 证明责任 |
| --- | --- |
| `expression_modulus`、`expression_view` | 模数和完整 `(env,temp_env,mem)` 快照到 DSL 状态的解释 |
| `expression_obligation`、`expression_encoding` | 独立语义条件 Q，以及 `holds(view(snapshot),presumption) ↔ Q(snapshot)` |
| `expression_type` | 候选的类型等于原表达式类型；赋值／return 的转换因此保持 |
| `expression_lowering` | 原表达式有定义时，机器 guard 也有定义，其 bool 等于 `execute(synthesize(presumption))` |
| `expression_local` | 原表达式求值为 v 且 Q 成立时，候选也求值为同一 v |

完整快照允许后续插件解释内存条件，但不自动允许读取内存或沿用失效事实。lowering 必须给出检查求值安全的证据，local 必须对其声明的所有快照成立。需要 reaching-store、缓存值有效性等入口不变量的优化，还需要提取与不变量保持的适配器；不能只填一个 alias 条件就算接入。

`encoded_expression_rule_sound` 自动组合编码正确性、通用 synthesis 定理、lowering 和局部证明，得到 `expression_contract`。各插件还证明识别器返回的 AST 就是证书的 source、guard 和 candidate。当前提供的是几种已证明的 lowering 形状，尚未提供整个 DSL 到 Clight 的统一 lowering 函数。

实际可复用的例子在 [CommonRewrites.v](../theories/CommonRewrites.v)：

```coq
Definition divisor_rule (rem : bool) (x y : ident) :
  encoded_expression_rule
    (divisor_source rem x y)
    (divisor_guard y)
    (divisor_candidate rem x).
```

`rem=false` 是除法，`rem=true` 是取模。同一个编码与 guard lowering 供两个局部等价证明复用；等价使用 CompCert 的 `Int.divu_pow2` 和 `Int.modu_and`。`cancel_rule` 则使用另一个 `NoOverflow` 编码，并证明在不回绕时整数除法确实消去加法。`self_sub_rule` 用 Truth 展示无条件等价如何通过同一证书接口接入。

## 从表达式接到完整程序

[ClightExprRewrite.v](../theories/ClightExprRewrite.v) 实际生成：

```c
/* unsigned x, y; 原来是 return x / y; */
if (y == 2u)
  return x >> 1u;
else
  return x / y;
```

当前语句上下文是 `Sset`、`Sassign` 的右侧和带值的 `Sreturn`。遍历进入 sequence、if 分支、loop、switch case 和 label body。`select_deep` 另在二元运算、单目运算和 cast 中定位一个子表达式，并复用已证明的严格表达式上下文提升；例如 `return 3u+(x/y)*5u` 会保留外层表达式，只替换内层除法。

每个表达式每轮最多选一个 rewrite，顺序是根、左、右。当前不改 if/switch 条件、调用参数、解引用地址或字段地址；也不做 fixpoint saturation。新规则可在 `select_common_root` 中注册、组合其 selector soundness 后，复用 `select_deep_sound`。signed、volatile 属性、其他宽度及更一般的幂次除数需要新的实例。

[ClightExprRewriteProof.v](../theories/ClightExprRewriteProof.v) 一次证明完整程序 simulation。它保持所有环境和完整内存，映射语句、调用栈、续体和 label 查找；原一步对应目标的一个或两个步骤，包含静默无限执行。新增 wrapper 只复制无 label 的叶语句，因此 labeled body 仍可优化，goto 进入该 label 后仍会执行 guard。既有分支消除 pass 的 label barrier 继续保留。

[GuardCompiler.v](../theories/GuardCompiler.v) 提供两个插件入口：

```coq
compile_with_rewrites branches expressions p
```

它在 SimplLocals 后先运行分支 pass，再运行表达式 pass。泛型正确性定理要求两个 selector soundness；具体 `compile_common_rewrites_correct` 已用 `select_no_wrap_sound` 和 `select_common_sound` 消去它们：

```coq
compile_common_rewrites p = OK asm ->
backward_simulation (Csem.semantics p) (Asm.semantics asm).
```

`compile_common_rewrites_preserves_spec` 同时提供排除出错的规格保持。最终定理不要求源程序始终无溢出或除数始终为 2。外部函数、解析、提取和系统汇编／链接仍沿用 [接入说明](compcert-integration.md) 中的上游可信边界。

## 内存类雏形

[CompCertMemoryRule.v](../theories/CompCertMemoryRule.v) 将真实 CompCert block 经单射 `Pos.to_nat` 解释成 DSL 身份，将 `Mem.load/store` 的实际 Z offset 和 chunk byte size 解释成区间，证明 Disjoint 的含义恰好对应 `Mem.load_store_other` 的不重叠前提。合成检查接受后，store 前后的 load 结果相等；`checked_load_hoisting_endpoint` 因而给出成功提前 load 的值和 store 后内存端点。

实例拒绝同一 block 中 offset 0 和 1 的两个 4-byte 访问，接受相邻的 offset 0 和 4，并在检查 endpoint 越界时返回 None。检查使用 `Ptrofs.modulus`，避免把 64 位指针区间误放进 32 位整数模数。

这不是可执行 C alias guard：CompCert 的语义 block 身份不能直接当作 C 的可读字段。`Mem.store=Some m'` 的访问／权限义务也没有由 Disjoint 推出。实际 Clight 提前 load 还需 guard lowering、访问安全、入口事实和中间状态／续体关系。当前只声称这条真实内存语义的局部证明链。

## 已运行验证

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make clean
opam exec --root=/tmp/guard-opam --switch=guard -- make check-integration
```

新环境的安装入口见 [toolchain.md](toolchain.md)。目标编译全部工程证明、运行既有独立回归、提取 `compile_common_rewrites` 并构建 ccomp，再运行两个 C 示例。

[native_rewrites.c](../examples/native_rewrites.c) 覆盖 6 个 x 值和 4 个非零除数的 24 对组合，另验证零除数的源程序保护分支和 goto。实际 Clight dump 含 9 个除数检查、2 个无溢出检查、7 个 shift 候选及 2 个 mask 候选，另有 Truth identity；保留了原始 fallback。运行同时覆盖临时赋值、真实全局写、return、嵌套表达式、循环、switch 和 label body。所有输出与 GCC 编译原 C 的结果相同；取消加法的溢出边界还与独立预期结果核对。

报告和 dump 在 `build/native-rewrites/`；旧 no-wrap 例子仍在 `build/native-demo/`。证明假设与上游编译器的 35 个假设名相同，没有新增假设。没有性能测量。
