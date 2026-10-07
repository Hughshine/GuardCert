# 表达式 header：真实源到 capture、前缀与缓存源

本阶段处理 `i < *limit + 1` 在 Clight 中的原始循环。根 bound 是实际表达式，而不是预先
改写的参数；子循环的主实例仍使用已有 canonical affine package。语言服务现在可以表达
多个、不同 chunk 的内存观察和任意有限深度的 structured body，但完整优化实例仍需填入
观察覆盖与保持证明。当前提取编译器尚未消费这些新服务，Figure 2 的优化覆盖仍未完成。

## 使用者怎样提供一个实例

优化实现者给出原 source AST、根 bound expression、递归 affine body 的 metadata，以及
之后要验证的候选。`check_expression_affine_numeric_site` 检查真实 source 等于所声明的
signed-expression loop、表达式具有 signed int32 类型、cache 不出现在原 source／public
scope、原 source 可以做 temp transport，以及已有 cached-model package 的静态证书。
这一步产生的是数值检查站点；并不直接产生 rewrite 证书。

它的实际检查代码是 `cache = bound_expression; numeric_check;`。例如：

```c
/* 原 source，每一轮都会重新求值。 */
for (i = 0; i < *limit + 1; ++i) {
  /* checked canonical affine children and array body */
}

/* 第一检查阶段，cache 是 private signed-int temp。 */
cache = *limit + 1;
numeric_check(cache, /* reached first-path parameters */);
```

`signed_expression_capture_receipt` 从实际原 source 的有限正常执行证明第一次 bound 求值
存在，即使比较为 false。它同时给出 capture 执行、原 compound-header source 在 private
cache 写入后的执行、公开出口 frame，以及第一次实际 body 的 receipt。没有稳定性前提，
没有先假设缓存 source 完成。`expression_numeric_site_execution` 消费这个 receipt，复用
现有递归 affine numeric checker，证明检查可执行、memory 不变、public temps 不变，并在
接受后取得 cached-word 视图的数学域。

source-completion 是此 host 的局部安全域，不是使用者必须提前写出循环最终内存的要求。
未来 factory／entry producer 要从 host 的真实 source receipt 生产它。任意 divergence 的
端到端扩展不由本阶段新增定理得到。

## raw observation 与计算结果是两个对象

若入口的 `*limit` 为 2，snapshot 中的 raw observation 是某个 Mint32 location 的值 2，
cache 则为 `Int.add 2 1 = 3`。`loaded_offset_cached_header` 将两者关联；
`loaded_offset_observations` 是入口内存的数学快照，不额外生成一次 runtime 读取。
`loaded_offset_bound_from_observations` 证明：pointer temp 保持，并且该 raw load 保持时，
当前完整表达式仍求得相同的 cache word。这里没有把 load 的结果错误地设成 cache。

加法使用实际 CompCert `Int.add`。当 raw word 为 `INT_MAX` 时，cache 为 `INT_MIN`；
本阶段的实际检查因此拒绝，子参数不被读取。capture 定理不承诺数学加法不溢出。
若某个优化的 presumption 要求原表达式本身不溢出，需要另行编码并证明该条件；
cached-word 数值域不能冒充这一事实，也没有在此引入 overflow flag。

## 使用者仍需给出哪些局部证明

优化实例提供观察列表及其与 header 求值的对应，并实现每一轮的只读 body check。
`expression_body_prefix` 的不变式保留真实原源的剩余执行、观察值和物理权限的逆向运输。
`expression_body_prefix_receipt` 从该执行取得当前实际 body；它允许 domain 解码递归写
trace、取得真实 reached-write permissions，随后证明当前 check 的可用性。

当前检查接受所证明的属性是 `expression_body_preserved`：在受保护 temps 与这些观察
成立的任何当前 body 执行中，body 之后观察仍成立。domain 可通过 byte separation 与
写 trace coverage 证明它；只读 alias 不必因这个稳定性义务而拒绝。语言层另外要求
body 的 quiet／normal 属性、`writes_only`、root 与 stable temps 未写，以及权限运输。
这些是可复用 language laws／checked body evidence，不是 kernel 自行分析出的事实。

`expression_body_prefix_advance` 只在当前 body check 接受后推进。上层
`expression_body_scan_condition` 使用已有 readonly prefix algebra；
`expression_body_scan_sound` 将全部接受推出所覆盖每轮的观察保持。fuel/cap 覆盖全部实际
迭代仍由 domain 提供，不能从“已有 scan combinator”省掉这项证明。

全部所需轮次的保持证据成立后，`expression_body_initial_cached` 和具体
`loaded_offset_body_initial_cached` 从真实原 source 推出相同 temps／memory 出口的 cached
source 执行。前提没有 cached-source completion。domain 此时才能用它许可已有 alias scan、
candidate validator 与候选执行证书；之后由 kernel 组合局部 guarded correctness。

## 为什么失败分支必须保留 compound header

实际 alias 例的 `*limit` 初始为 2，body 将它写成 1。原 `i < *limit + 1` 源执行两轮后
停止，虽然捕获到的初始上界为 3。`offset_alias_original_stops_after_two` 使用实际
CompCert allocation/store/load 证明这个执行；`offset_alias_header_observation_changes`
证明第一 body 后 raw observation 已改变。单凭安全 capture 不能选择缓存源。

未来完整 guard 拒绝时，应执行原 repeated-expression source。当前新 numeric site 可以
拒绝空域或不符合 profile 的值，但它尚未包含此 alias 稳定性 scan；不能把 numeric 接受
解释为候选 rewrite 已证明正确。

## 当前验证及后续接入

源码在 [capture](../prototype/interface/ClightExpressionHeaderCapture.v)、
[prefix](../prototype/interface/ClightExpressionBodyPrefix.v)、
[cache transport](../prototype/interface/ClightExpressionBodyTransport.v)、
[load＋offset](../prototype/interface/ClightLoadedOffsetHeader.v) 和
[numeric site](../prototype/interface/ClightExpressionAffineNumericSite.v)。
实际空域／回绕检查和 alias 源执行分别在
[numeric fixtures](../prototype/interface/ClightLoadedOffsetExamples.v) 与
[alias fixture](../prototype/interface/ClightLoadedOffsetAliasExample.v)。

`make expression-header-proof` 编译依赖闭包并审计新端点的全局假设；
`make expression-header-validate` 复核 source／object／helper／toolchain 摘要。
报告保存到独立 `build/expression-headers/proof/`，原 reduced compiler 的证明报告保持。
这些命令使用当前已验证的 reduced proof 报告和依赖对象；尚未验收从空 build 目录启动的
独立 bootstrap。本轮也复核了原 reduced native／Figure 2／工作量报告的绑定，未重跑旧矩阵。
新完整 factory、program theorem、extraction 和 native 优化结果都尚未提供；原 compiler
端点单列为回归。这些接口参数与 fixtures 不能据此宣称减少了实例作者的证明负担。

下一步由 recursive domain 实际填入此 prefix 的 body-check／coverage，接 guard 的原入口和
checked-entry 关系，再由 typed host 安装。随后把第二 loaded child 的 reached capture 和
观察合到同一三层 package，同时推进 compact write-vs-observation 条件及实际工作量验收。
