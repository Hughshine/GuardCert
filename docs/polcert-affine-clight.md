# 从数学仿射表达式到实际 Clight

`PolCertAffineClight.v` 与 `PolCertAffineGuard.v` 对接真实 PolCert `Loop` 和当前 CompCert 的 Clight。它们证明表达式及布尔测试的 lowering，并生成检查输入范围的实际 Clight 条件树。这是完整循环 lowering 的一个组成部分。

## 输入与接口

调用者提供参数位置到 Clight temporary 的 `layout`，以及每个参数的候选区间 `bounds`。`typed_view` 关联 Loop 的数学整数环境与这些实际 temporaries：对应 temporary 必须包含 `Vint`，其 signed 值等于数学参数。这个关系不包含无溢出或参数处于提议区间的假设。

区间是未经信任的输入。`analyze` 检查区间合法性、常量、乘法系数，以及每个中间表达式的 signed32 范围。`compile_expr` 同时要求区间检查和代码生成成功。目前支持 `Constant`、`Var`、`Sum` 与常量乘法 `Mult`。`Div`、`Mod`、`Max`、`Min` 返回 `None`；其中整数除法还涉及 Loop 的 floor division 与 C 的截断除法差异。

输入区间检查是独立的性质维度，可与其他维度组合。`range_dimension` 给每个下界或上界比较提供正、负证据；`range_primitives` 提供实际 Clight validity/value 表达式。参数映射缺失或区间无效时返回 unknown。通用条件编译器保持 unknown，包含对条件取反的情况。

`range_guard layout bounds` 不把数学环境编入生成代码。环境只用于证明实际入口 temporaries 对应哪些数学值。`range_guard_environment` 证明更换这个证明环境不改变条件树。

## 定理提供什么

| 定理 | 结论与前提 |
| --- | --- |
| `analyze_sound` | 输入满足提议区间时，成功分析的表达式及其中间结果、系数均在 signed32 范围内，结果落在输出区间。 |
| `compile_expr_sound` | 再给出 `typed_view`，实际 Clight 表达式可以求值，结果等于 `Vint (Int.repr (Loop.eval_expr env e))`，类型为 signed32。 |
| `lower_test_exact` | 接受的比较、and、or、not 与布尔常量形成纯条件树；每次成功执行的结果恰好等于实际 `Loop.eval_test`。该定理仍要求输入区间。 |
| `range_guard_sound` | 在 `typed_view` 下，生成的条件树接受可推出所有输入区间；不需要预先假设区间成立。 |
| `range_guard_total` | 在 `typed_view` 下，范围条件树总有执行结果。合法边界比较只读取整数 temporary，不执行可能溢出的目标算术。 |
| `guarded_affine_correct` / `guarded_test_correct` | 组合运行时接受与静态区间证书，推出实际 Clight 表达式或测试与数学 Loop 语义一致。 |

`ClightPureExpr.v` 提供这一子集的求值唯一性，以及条件树 continuation 的替换。它只处理常量、temporaries 和纯运算，不把内存 load 的语义隐藏成确定性假设。

## 已执行的边界例子

Rocq 的 `vm_compute` 检查实际算法：

- 在 `0 <= x <= 1073741823` 下，`2*x+1` 的证书为 `[1,2147483647]`。
- 对完整 signed32 输入域，同一表达式被拒绝。
- `-2*x` 在 `[-3,4]` 下得到 `[-8,6]`。
- 对完整 signed32 域，`-x` 被拒绝，因为最小负数不能取负。
- 除法被拒绝；无参数映射或倒置区间的原子在否定下仍是 unknown。

这些是编译时执行与证明检查，不是多面体优化的原生性能测试。

## 复现与假设

```sh
make polcert-affine-proof POLCERT_SOURCE=/path/to/verified-compilation-v10-driver
```

该目标复用锁定 CompCert 工具链，恢复并重编译真实 Loop 的 57 个证明依赖及既有适配器，然后编译两个桥接文件。`build/polcert-affine-report.json` 将新增定理的 `Print Assumptions` 与实际 `Clight.eval_expr` 基线比较；二者相同，新增全局公理为空。数学区间分析本身闭合。表达式语义证明继承 CompCert 的四个既有逻辑假设。

当前没有生成完整 `Loop.stmt` 的循环代码，未将此桥接接入提取后的优化器，也未证明多语句区域进入完整 Clight 程序。实际 `Opt_prepared_correct` 已接入的是 [guarded Loop 程序](../adapters/polcert-optimizer/README.md)。后续必须补充指令实现、有限迭代及 private temporary 的状态关系、候选进展和区域上下文模拟。
