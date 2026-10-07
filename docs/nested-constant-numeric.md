# 从原嵌套源生产 capture／numeric／scan 输入

2026-10-07。接续 [三层 canonical 模型](nested-constant-model.md)；本阶段从原源
执行生产安全检查的入口证据，不以缓存源执行或未来观察稳定性许可检查。
它关闭 parameter definedness、numeric math domain 和逐 `(row,column)` 的
`DOMAIN`／`SOURCE_WORDS` producer。完整 physical guard／factory／candidate／host
尚未组装，Figure 2 适配源的优化仍未安装。

## 原源与实际检查

源是原来的两个表达式 header，加一个正的机器 literal 子循环及 checked 内存 leaf：

```text
row < bound
  column = 0; column < child_bound
    component = 0; component < literal
      checked memory leaf
```

`bound`／`child_bound` 可以是 repeated loads 与计算，不要求缓存源完成。本服务
要求 row 在入口为零、两个表达式为 signed int、child 表达式不读 column，以及
literal 的机器解释大于零。本次支持实例为 `<5`。先前 model transport 对任意
`Z` 常量的证明，不扩大这个 numeric producer 的活动 profile。

实际代码是 `nested_constant_captured_numeric_code`：

```text
root_cache = bound
if row < root_cache: child_cache = child_bound
if 0 < root_cache:
  if 0 < child_cache: old_checked_numeric_probe
  else: result = 0
else: result = 0
```

有序 capture 复用既有语言证明。后两个 gate 的左操作数是常量零，故检查不读
尚未初始化的 source column。Inactive root 不读 child；inactive child 不读取
BODY 专用参数、component counter 或 output pointer。此处返回 false，让后继
dispatch 使用原源；它没有生成整个 dispatch。负的 captured machine count 也
沿同一 gate 拒绝。检查保持入口 memory，仅写私有 temps，并保护原 live temps。

## 原源如何提供参数

[ClightNestedConstantFirstLeaf.v](../prototype/interface/ClightNestedConstantFirstLeaf.v)
的 `nested_constant_original_first_leaf` 分解实际原源的第一次活动路径。两层
活动且 literal 正时，取得 column／component 重置之后的实际 leaf 执行；其入口
仍是原 memory。这一步不需要 helper 初始化、数学域、alias 分离或 bound 稳定性。

[ClightNestedConstantNumericInputs.v](../prototype/interface/ClightNestedConstantNumericInputs.v)
的 `nested_constant_original_parameter_domains` 消费旧 checked package：每个被
接受的参数是 root cache、child cache，或实际 leaf 使用的 word。前两者由
capture 提供；其余由真实 leaf 执行和旧 used-register checker 提供。旧参数
freshness 排除 source coordinates 的赋值，故实际 reset 不会覆盖它们。
这个 producer 允许 BODY 专用参数；调用者不用提供 `Forall register_domain`。

两层实际 gate 均活动时，才把以上事实交给旧 numeric/profile 编码器。接受证明
canonical nest 的完整数学域。`nested_constant_package_scan_inputs` 再从 checked
layout 的 `NoDup` 和该数学域，生产每个活动 `(i,j)` 的 component 域及原 inner
prefix 的 exact word view。`nested_constant_scan_inputs` 是这个证明的结论，
不是要求优化方填入的语义回调。

## 对使用者暴露的端点

[ClightNestedConstantCapturedNumeric.v](../prototype/interface/ClightNestedConstantCapturedNumeric.v)
提供 `nested_constant_captured_numeric_execution`。输入仍包括：

- 对 canonical source 的旧 data-only checked package，以及 proposal nest 等式；
- 原 header 的类型／column freshness、row=0、静态 frameable 和两个 cache 的 freshness；
- positive machine literal，以及原 source 的 silent normal completion。

输出是整段 capture＋gated numeric 的实际 Clight 执行、原 live frame、实际 Boolean
结果，以及 captured-entry 上保留的原 source 执行／公开出口对应。还返回实际
root header receipt 和仅在 root 活动时要求的 child receipt。
numeric=true 另提供参数定义性、完整 math domain 和 scan 输入。
缓存源完成、源／模型 semantic callback 和未来 header 稳定性均不是输入。

这些 facts 锚定 **captured entry**。实际 numeric probe 保持其 protected ports，
但完整 factory 仍须把 scope／namespace、private helpers 和 cursor 的映射绑定到
后续 physical scan 入口。numeric 接受本身不许可未来地址，不提供原 header
表达式的一般数学 non-overflow 结论，也不保证所有后续 loads 的值不变。
这些义务分别由实际 reached source prefix、观察检查与候选前提承担。

| 归属 | 本阶段生产的事实 | 后续仍需生产 |
| --- | --- | --- |
| 最小 kernel | 不变 | 消费最终局部证书；不负责发现参数或整程序安装 |
| 语言库 | 原 first leaf；既有 ordered capture、temp frame、实际 gate 求值 | source scope、private typed pool、progress／placement 与 host 安装 |
| Domain／优化实现 | checked 参数使用到定义性；实际 numeric 编码；逐点域／word view | 原 AST site checker、helper／namespace 接线、完整 physical guard、cross-entry candidate |

## 具体 package 与拒绝路径

[ClightNestedConstantNumericExample.v](../prototype/interface/ClightNestedConstantNumericExample.v)
检查一个 flat 16×16×5 风格的真实 store leaf：
`output[(row*16+column)*5+component] = row+column+component+extra`。
proposal 的参数是两个 caches 和 BODY 专用的 `extra`。旧 checker 接受这个
完整三轴 canonical package，并拒绝把公开 `extra` 用作 result scratch。
root=2、child=3、extra=4 的 numeric flag 接受；root=16 超出 profile 而拒绝。

另有两个实际 Clight 拒绝端点，分别只定义 root=0，或 root=2／child=0。
所有 source counters、BODY 参数和 output pointer 均未定义，检查仍正常完成且
不改 memory。这不是整段源 fixture，也不是新 extracted/native compiler。

## 可重放审计与下一项

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make nested-constant-numeric-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make nested-constant-numeric-validate
```

独立 stage 审计通过 24 个端点：6 language、11 domain、7 fixture，565 required
dependencies／1,076 源摘要，各新端点最多使用六项既有 CompCert assumptions。
`build/nested-constant-numeric/proof/report.json` SHA-256：
`0574bda833e58435b2d8000f9c70284d0bec95bfb2320acd0c8cf9dbf29bead8`。
审计以先前 model report 为父绑定，核对父源码／对象在编译前后保持，kernel
闭合，新端点仅使用既有 CompCert global assumptions；旧 compiler 基线保持。
这不是 empty-build bootstrap 验收，也没有新 native、extraction 或 timing。

下一项把这组实际 producer、observer receipts 和静态 namespace／scope 检查
接到现有 outer physical scan；组装完整 guard certificate、原 source factory 和
候选／host。随后提取并验收 Figure 2 适配原 C，最后在同源同候选上比较 compact
conditions 的代码大小、实际成本、有用接受域和作者工作。完整目标 active。
