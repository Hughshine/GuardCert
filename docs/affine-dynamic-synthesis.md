# 从仿射不溢出前提直接合成 guard

`PolCertAffineDynamic.v` 为实际 Loop 的 signed32 仿射子集合成 Clight guard，不要求调用者先提议输入区间。输入是表达式和参数 temporary 的 layout，输出是实际 Clight 表达式与检查树。

这一步合成的是指定 presumption 的检查代码。它没有从任意 source/candidate 推断最弱的正确性前提，也不支持任意逻辑谓词。

## 依赖顺序与安全的检查算术

前提 `affine_safe` 要求常量、乘法系数以及每个中间结果都在 signed32 范围内。参数由 `typed_view` 对应 signed32 temporaries，因此读取参数本身有定义。

常量与系数在编译时核对，参数映射必须存在。对于加法和乘法，生成的树先检查子表达式。子检查接受后，子表达式的 signed32 求值已被证明等于数学值；此时才将操作数扩展为 signed64，计算父运算并比较 signed32 的上下界。

`ClightWideGuard.v` 证明任意两个 signed32 值的和、积都在 signed64 范围内，并证明实际 Clight cast、运算和边界比较的求值。检查不会先执行一个未经证明安全的 signed32 父运算来判断它是否溢出。

例如 `2*x+1` 的树先检查 `2*x` 的加宽结果，再在该结果满足 signed32 范围时检查后续加法。`x=1073741823` 接受；`x=1073741824` 拒绝。`(x+1)+(-1)` 在 `x=INT_MAX` 时拒绝，即使最终数学值合法，因为指定前提包含中间结果。

## 精确性与公式组合

`compile_dynamic_exact` 证明成功编译的检查树总有执行结果，而且结果恰好等于 `safety_bool`。`safety_bool_spec` 将这一布尔值对应到 `affine_safe`。因此接受没有遗漏前提，拒绝也能证明该前提不成立。精确性针对这个选定前提，不意味着它是 rewrite 的最弱条件。

`compile_dynamic_accepted` 进一步证明接受后实际 Clight 值等于 Loop 数学值的 `Int.repr`。

`decision_test_language` 允许一个原子测试本身由安全的条件树实现。它通过已证明的 `decision_bind` 组合检查，继续使用原来的通用三出口 `compile_condition`。核心没有加入算术或 overflow 特例。

`dynamic_dimension` 与 `dynamic_primitives` 将合成器接成性质插件。支持的原子能提供正、负证据；不支持的表达式或无法映射的参数返回 unknown。`dynamic_formula_guard_property` 证明合成复合公式的接受能推出其逻辑前提，包括否定；不支持的除法原子取反仍是 unknown。

数学环境只出现在证明中。`dynamic_compile_environment` 证明生成代码不依赖选用哪个环境来描述入口参数。

## 范围与复现

支持 `Constant`、`Var`、`Sum`、常量乘法 `Mult`。除法、取模、min/max 当前拒绝。输入 layout 的类型与存在性仍须由语言宿主证明；没有把任意 temporary 读取当作安全操作。

```sh
make polcert-dynamic-proof POLCERT_SOURCE=/path/to/verified-compilation-v10-driver
```

该目标恢复实际 Loop 的锁定证明闭包，编译仿射桥接与新合成器。报告 `build/polcert-dynamic-report.json` 比较 CompCert 表达式语义基线，新增全局公理为空。当前动态合成器尚未接到提取后的原生驱动；既有输入区间方案仍用于单层循环原型。
