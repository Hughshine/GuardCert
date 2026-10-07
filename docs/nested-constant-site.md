# 原 AST checked site、固定 observer 代码与实际检查后入口

2026-10-07。接续 [原源 numeric producer](nested-constant-numeric.md)。本阶段把
实际源形状、静态资源检查和入口 producer 放到一个 data-only site 后面，并
消除 numeric 检查前／后的状态锚点差距。完整 physical guard、候选及语言 host
仍待组装；Figure 2 适配原 C 的优化尚未安装。

## 使用者提交什么

[ClightNestedConstantSite.v](../prototype/interface/ClightNestedConstantSite.v) 的
`nested_constant_shape` 是 proposer 数据：三个 source coordinates、两个 cache、
两个 model helper、literal upper、leaf AST，以及一个 header pointer、child
index 和两个整数 delta。`check_nested_constant_site` 另接收实际 source AST、
parameters、context live 与旧 affine proposal。

它处理的原源是：

```text
row < *pointer + delta
  column = 0; column < pointer[index] + child_delta
    component = 0; component < literal
      checked memory leaf
```

这覆盖 Figure 2 适配的两个 `+1` headers 和 `<5` body 形状，但不意味着已经
在真实 frontend／整程序中安装。Source 必须与此原 AST 精确相等；先手动缓存
再交给 checker 会拒绝。Header 的算术采用原 machine semantics，raw loaded word
与 computed cache word 分别保留，不把缓存范围检查称为任意 header 数学 no-wrap。

Checker 从数据生产以下证据：

- 原 AST 等式、frameable、coordinate/cache/helper 名称分离和 private freshness；
- cache 参数声明、pointer 作用域与 coordinate 分离；
- 对 canonical model 的旧 checked affine package 及 nest 数据等式；
- 旧 scan namespace：私有 controls 唯一、flag 分离、参数值映射；
- component 子模型的实际 `affine_lower_nest` 结果。

该 profile 要求 positive machine literal，允许既有 leaf checker 的普通内存
读写计算和 BODY 专用参数。失败返回 `None`。这里还没有候选字段、typed pool
安装证书或完整 guarded rule，不能把这个 entry site 称为完整 optimizer factory。
片段发现与候选选择继续由使用者／proposer 决定。

## 实际 runtime 入口

[ClightNestedConstantEntryGate.v](../prototype/interface/ClightNestedConstantEntryGate.v)
提供 `ncs_entry_numeric_code` 和 `ncs_entry_numeric_execution`：

```text
if row == 0:
  ordered capture root; active source root 才 capture child
  if root_cache > 0 and child_cache > 0: checked numeric probe
  else: result = 0
else: result = 0
```

最外层 row gate 是真实 Clight 比较。原 source completion 从实际首次 signed
comparison 提供 row word；不要求使用者额外证明 context 中 row 恒为零。Nonzero
row 不读取任何 header 或 BODY 输入；这个候选 profile 在该入口安全拒绝。
Root inactive 不读 child；child inactive 不读 BODY 专用参数和 output pointer。
Guard 只读 memory、写私有 temps；guarded-choice fallback 尚由后续完整规则组装。

入口 theorem 的唯一动态安全域输入是实际原 source 的 silent normal completion。
`ncs_entry_numeric_receipt` 记录实际检查执行、原 source/context scope 的 frame、
检查后原 source 的真实执行与相同 final memory／公开出口，以及 defined Boolean。
接受交付下述 numeric receipt；不存在 source/model、`HEADER` 或参数定义性回调。

## 接受后的实际状态

[ClightNestedConstantSiteNumeric.v](../prototype/interface/ClightNestedConstantSiteNumeric.v)
的 `ncs_numeric_receipt` 将全部事实锚定到实际 numeric **exit temps**：

1. 参数 word 定义性、完整 math domain 和逐点 DOMAIN／SOURCE_WORDS；
2. 原 source 在该入口的执行、同一 final memory 和原公开出口对应；
3. 由真实 root／child evaluations 生产的 raw observers 与初始 observations；
4. `ncs_numeric_initial_prefix` 给出的原 outer source prefix。

旧 protected-port frame 将 flag 运到当前入口；math domain 复用旧 profile 接受
定理，参数 word view 来自真正原 first leaf。接受前不预设完整 cached execution、
future header stability 或 future access permissions。Initial prefix 是原源 witness，
后续仍须每个 BODY 检查接受才推进。

## Guard AST 不依赖运行时 ghost 数据

[ClightNestedConstantHeaders.v](../prototype/interface/ClightNestedConstantHeaders.v)
从实际读取生产 `ncs_observation_receipt`，再由它恢复两个 source header：受保护
pointer word 和全部 raw observations 相同时，computed bounds 也相同。
`ncs_root_header_from_receipt`／`ncs_child_header_from_receipt` 是具体定律的
producer，使用者不提供一个任意的 `HEADER` 假设。

编译时无法知道实际 block、offset 或 raw word。因此 `ncs_observer_templates`
只固定两个地址表达式；其余 dummy fields 没有实际 receipt，不被当成有效观察。
[ClightJointObserverSyntax.v](../prototype/interface/ClightJointObserverSyntax.v) 证明：
observer address lists 相同，完整 outer scan 的 Clight AST 就相同。
`ncs_outer_syntax_uses_templates` 将运行时真实 receipt 的 scan 代码接到编译时
template 代码。没有把 runtime memory witness 塞进编译器配置。

## 责任与验收

| 归属 | 本阶段已生产 | 剩余责任 |
| --- | --- | --- |
| Kernel | 不变 | 消费最终 guarded/candidate certificate |
| 语言／语法库 | observer ghost 数据不改变 AST；原 header row word；真实 row gate 与 frame | helper 准备、typed allocation、progress／placement 和 host 安装 |
| Domain／优化实例 | data-only 原 site；具体 header laws；实际检查后域、observers 和 prefix | 填入 physical scan 的其余静态／helper 输入，组装完整规则，再接候选 |

Fixtures 检查 `load+1`／indexed `load+1` 原 site 接受，cached replacement、公开
header pointer 作 capture scratch、flag 与 component cursor 冲突，以及 empty
literal profile 拒绝。一个只有单个可读 header word、BODY 参数／pointer 未定义
的实际空源，取得完整 entry receipt。另证 nonzero row 在所有 headers／BODY
输入未定义时，实际只写 result=0 并正常完成。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make nested-constant-site-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make nested-constant-site-validate
```

独立审计通过 37 endpoints：4 language／23 domain／10 fixture；584 required
dependencies／1,083 源摘要。各新端点最多使用六项既有 CompCert globals，kernel
闭合，旧 compiler 保持 42 项 assumptions。父 numeric 源／对象在编译前后保持。
`build/nested-constant-site/proof/report.json` SHA-256：
`567669aec6d81a8f7a732a66e76c68b5aa9c36c869ced80681ec5b21c91e36d5`。
这不是 empty-build bootstrap 验收；旧 native 的绑定核对不计作本阶段新运行。

下一项执行接受后的 private helper 准备，并用此 checked site 的 namespace、
scope 与 current-entry receipts 实例化现有 outer scan。继而连接 complete guard
certificate、cross-entry candidate、原 source key／fallback 和语言 host；提取并
运行 Figure 2 适配原 C。Compact 条件、实际检查成本／接受域和作者工作仍是
完整目标的最终验收项，本阶段没有新 compiler、native 或 timing。
