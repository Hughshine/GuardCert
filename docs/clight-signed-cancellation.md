# 树形原子检查与 signed rewrite 的完整程序接入

`ClightDecisionRule.v` 提供 `encoded_decision_rule`：插件的原子检查可以是一棵已验证的条件树。它沿用 `property_dimension`、正／负／unknown 的证据，以及通用三出口公式编译，不要求一个原子必须对应一条 C 表达式。

插件提供入口域、性质维度、validity/value 检查树、前提公式、类型保持和条件局部值保持。`encoded_decision_rule_sound` 输出既有 `ClightTreeRewrite.expression_contract`，因此复用同一个完整程序宿主与 C→Asm 驱动。调用者无需为多步骤原子检查重写完整程序 simulation。

实际 Loop 的 `PolCertAffineDynamic.v` 已复用这一共享的公式合成器。其数学环境与参数 view 仍由 PolCert 适配器维护；当前原生驱动并不解析或调用 PolCert 多面体优化器。

## signed32 的接受与回退

`ClightSignedCancel.v` 的实例是 `(x*2)/2 → x`。前提为数学乘积 `Int.signed x * 2` 落在 signed32 范围内。源表达式有定义能够证明 temporary 存在且是 `Vint`，从而建立检查入口域。性质插件能提供前提为真和为假的证据。

原子检查使用已经证明的 signed64 扩展、乘法及比较，生成实际 Clight：

```c
if (-2147483648LL <= (long long)x * 2LL) {
  if ((long long)x * 2LL <= 2147483647LL)
    return x;
  else
    return x * 2 / 2;
} else {
  return x * 2 / 2;
}
```

检查没有先执行可能回绕的 signed32 乘法。两倍乘积对每个 signed32 输入都能由 signed64 精确表示；前提不成立时仍执行源表达式。

CompCert 的 signed 乘法使用模 `Int.mul`，因此源在这些溢出输入上仍有具体的回绕结果。此实例不假定完整程序全局没有溢出。GCC 参考程序使用 `-fwrapv` 明确提供相应的乘法／加法回绕行为；没有用默认 C 的溢出行为作参考依据。

规则仅匹配无 attribute 的 signed32 temporary、乘法系数 2 和除数 2。普通 unsigned 乘法取消或其他系数不会被此规则命中。后续可扩展系数范围，但仍须核对除法例外及条件局部证明。

## 完整程序与原生检查

`RegionCompiler.compile_property_regions` 已组合此插件、既有 unsigned 算术与同地址读取插件。它继续提供实际 Csem→Asm backward simulation 以及排除出错的规格保持，完整程序端点不额外要求 no-overflow 前提。

`examples/native_signed.c` 与 `scripts/native_signed.py` 检查九个 signed32 输入，包含 `INT_MIN/INT_MAX`、正负接受边界及紧邻的拒绝边界；还检查严格表达式上下文、局部赋值及标签跳转。提取后的实际 Clight dump 含五个加宽检查树、候选与源式回退。检查结果与 GCC `-O0 -fwrapv` 及独立模算术计算一致。

```sh
make check-integration
```

该目标现在还执行 `scripts/audit_compiler.py`，比较上游编译器与实际组合驱动定理的全局假设。报告在 `build/compiler-assumptions-report.json`；原生 signed 示例在 `build/native-signed/`。形式化终点是 Asm，原生汇编／链接／运行是执行验证。这里没有速度提升或完整多面体 C→Asm 的结论。
