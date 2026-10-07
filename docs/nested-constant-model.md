# 完整三层缓存源到已验证 affine 内存模型

2026-10-07。接续 [outer scan／双缓存源](constant-joint-outer-scan.md)，本阶段
将已经合法的缓存执行接到既有 affine package 的真实内存解码。输入是稳定性
检查接受之后取得的缓存源执行；它不能反过来许可稳定性检查。最小 kernel、
候选验证器和语言 whole-program host 保持不变。

## 实际源与模型

[ClightNestedConstantModel.v](../prototype/interface/ClightNestedConstantModel.v)
处理固定的三层形状；leaf 可以是既有 checker 支持的内存计算。

```text
缓存源：
  row < root_cache
    column = 0; column < child_cache
      component = 0; component < literal
        checked memory leaf

canonical 模型：
  row < root_cache
    child_helper = child_cache
    column = 0; column < child_helper
      component_helper = affine_constant(literal)
      component = 0; component < component_helper
        同一个 checked memory leaf
```

`nested_constant_model_nest` 的源 AST 正好是 `nested_constant_model_source`，
父／子形状满足旧 affine 编码器的实际结构要求。常量使用既有
`memory_source_affine_code`，负常量采用其取负表达式语法。
`constant_affine_body_preinitialized_model` 对任意 `Z` 常量证明机器执行运输；
这不意味着这些常量都通过后续 mathematical no-wrap/profile 检查。

在两个 helper 已有目标 word 的入口上，其赋值是实际 Clight 执行中的 no-op。
`nested_constant_preinitialized_model` 用真实 source body 的 quiet/write 事实
填入 `strict_active_loop_transport` 的 TEST、BODY、WEAKEN 和 INCREMENT，
不把它们作为本实例的新语义回调。结论保留同一 trace、outcome、exit temps 和
final memory；quiet/normal BODY 限制了本阶段的源形状。

`nested_constant_closed_preinitialized_model` 将静态输入收敛到 leaf 的 quiet／
`writes_only []`、六个名称的 `NoDup` 和三个 cache/helper word。源的 writes、
quiet/normal 及 protected-frame 条件在证明内部生产。实际 helper 准备仍是
独立义务。已有 `model_bounds_prepare_execution` 和 `model_bounds_prepare_source`
提供初始化及原 source-scope 运输；factory 尚须绑定它们与原 AST 的 freshness。

## 消费 package，取得真实 Loop 执行

[ClightNestedConstantDecode.v](../prototype/interface/ClightNestedConstantDecode.v)
提供 `nested_constant_package_source_decode`：

```text
checked canonical package
+ 实际缓存源执行
+ 已初始化 helper words／名称分离
+ 原 numeric guard flag = true
-----------------------------------
真实 Loop source 执行，使用实际入口 memory 和实际 final memory
```

旧 `check_affine_guard_package` 从数据提案生产实际结构、leaf operations、参数
使用、profile 和 guard namespace 的证书。新 decoder 从该 certificate 取得
leaf 的 quiet/write 事实，调用闭合的 source transport，再消费
`affine_package_source_decode`。没有 source-to-Loop 对应或 body-effect 语义回调。

本端点消费旧 numeric flag、pointer freshness、lowered source-loop 数据和
具体 proposal nest 等式；这些仍须 factory 从实际检查／元数据生产。它没有
执行新的 numeric guard，也没有给出候选执行、依赖保持或完整 guarded rule。

## 验证责任及下一项

| 层 | 本阶段交付 | 仍待连接 |
| --- | --- | --- |
| 最小 kernel | 不变，继续组合局部证书 | 新完整 guard/candidate certificate 尚未组装 |
| 语言库 | 复用 helper 准备、temp transport、strict-loop 执行与 frame | 实际 scope、typed pool、进展／位置与程序安装 |
| Domain 实现 | 三层 canonical AST、具体循环运输、从 checked package 取得真实 Loop 执行 | 原 capture／numeric／namespace 的实际输入 producers；原 AST factory；cross-entry 候选与 host |

Empty outer 仍消费独立 empty 服务，不读取 child，也不为满足此 decoder 假设
child cache 已定义。未到达的 child、negative computed counts 及 unknown 必须
由实际有序 gate／fallback 处理。空扫描 true 不能单独许可先读 child 的候选。

按 narrative `226ba94`／`271f6fc`，下一项闭合约定范围的输入生产与原源安装，
并行更新实际稿件；此后在同一 source/candidate 上验收 compact conditions。
代码大小、运行检查成本、有用接受域和实例作者工作分别记录。当前没有新
source matcher、compiler、extraction、native fixture 或计时。原 Figure 2 coverage
仍为 `not-supported`，完整目标 active。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make nested-constant-model-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make nested-constant-model-validate
```

审计 12 个 domain 端点／557 required dependencies／1,071 源摘要通过；各新
端点最多使用六项既有 CompCert 假设，kernel 闭合，完整 compiler 保持 42 项
assumptions。先前 outer 源码／对象摘要在编译前后保持。
`build/nested-constant-model/proof/report.json` SHA-256：
`da5a29a86acf1934d8242c9f0ba9765e7d831ed80cb4192ba4f2510f95bc52b0`。
旧 native 绑定核对不计作本阶段新运行；这不是 empty-build bootstrap 验收。
