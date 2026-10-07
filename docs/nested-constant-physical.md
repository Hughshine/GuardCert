# 从实际原源到完整 header-stability guard

2026-10-07，接续 `18e1b50` 的 [checked entry](nested-constant-site.md)。现在实际
执行 helper 准备，完整填入 outer scan，并从接受结果取得 canonical Clight 与
真实 Loop 执行。还没有 nested candidate rule／新 compiler／extraction／native。

## 使用接口

使用者仍提交 source AST、shape、params、context live、affine proposal 数据，
由 `check_nested_constant_site` 产生 site。片段发现与候选算法继续由 proposer
决定。该 profile 支持 loaded-offset root、同 pointer 的 indexed-offset child、
literal constant subloop，以及旧 leaf checker 支持的普通多次内存读写 BODY。

[ClightNestedConstantPhysicalGuard.v](../prototype/interface/ClightNestedConstantPhysicalGuard.v)
提供 `ncs_physical_guard site`，实际 Clight 代码依次执行：

```text
row-zero gate
  ordered original root/child capture
  positive root/child gates + numeric probe
if numeric result:
  child_helper = child_cache
  component_helper = literal
  full outer short-circuit scan
    full child short-circuit scan
      constant component scan
        compare every actual write against BOTH header addresses
```

代码使用编译时 observer templates；没有 runtime raw proof witness 配置输入。
不把 guard 写入私有 temps 说成无状态变化：memory 只读，原 source/context scope
的 temps 保持，模型 helpers 和扫描 cursors 是 private。Runtime result 是定义的
Boolean；nonzero row、inactive root／child 和 physical scan refusal 均走真实路径。

`ncs_original_physical_guard_execution` 的动态域输入只有实际原 source 的
**silent normal completion**。它交付完整 guard 执行、same memory、public frame、
检查后的原 source 执行和相同 final memory／公开出口。该定理不覆盖任意源的
divergence，也不自行提供整程序 progress／placement 合同。

## 接受交付什么

`ncs_physical_accept` 由实际 result=1 得到：

- 一个明确的 model entry，而非把 private guard cursors 当成 source coordinates；
- model entry 到 **实际 guard exit** 的 `ncs_ports` frame；
- model entry 的 numeric acceptance；
- 真实 canonical three-axis Clight 执行、原 final memory 和 public exit frame。

Canonical execution 是完整 stability scan 接受后的结果。许可扫描时只用原源
prefix 的实际读写权限，未假设未来 bound 稳定或未来 cached source 完成。
所有 point-domain、source word view、header law、静态 effect／namespace 输入
由 site 和检查／准备 receipts 生产，调用者没有新增这些语义回调。

`ncs_physical_accepted_source_loop` 再消费实际
`affine_package_source_loop parameters proposal = Some source_loop` 的数据 lowering
结果，用旧 verified decoder 生产 model entry 上的真实 Loop semantics。它保留
到 actual guard exit 的 frame；不宣称两入口任意 temps 或整个 location map 相等。
下一项 candidate adapter 需要沿此 frame 证明实际使用的 context／pointer cells
对应，接候选 dependency/alias 检查与 lowering／公开出口恢复。

## producer 与责任

| 责任 | 本阶段实现 |
| --- | --- |
| Kernel | 未修改，后续消费 guarded/candidate certificate |
| 已有语言服务 | helper assignments/source transport、真实 comparisons、prefix loops、observation preservation、checked decoder |
| Domain 实例 | `SitePrepare` 生产 helper 后入口；`ScanNames`／`ScanStatic` 从 checker 消除 scope/effect/namespace 义务；`OuterConsumer` 完整实例化原源服务；`PhysicalGuard` 合成实际代码与 receipt |
| 尚待完成 | candidate dependency/alias guard、cross-entry candidate adapter、guarded rule factory；typed pool／host progress-divergence／placement；新 Csem→Asm 与运行 |

最难的 source-definedness/stability 闭环已经在 normal-completion 域内接通，但
这不能取代最后一行的候选和语言宿主验收。完整目标保持 active。

## 验证

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make nested-constant-physical-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make nested-constant-physical-validate
```

39 endpoints（36 domain／3 fixture）、590 required dependencies、1,089 源摘要
审计通过；各新 endpoint 最多六项既有 CompCert globals，没有新增 global axiom。
Kernel 闭合，旧 compiler 的 42 项 assumptions 保持，父 site 源／对象未变。
Report `build/nested-constant-physical/proof/report.json` SHA-256：
`73482e061adbb772a0faad52840152b4d33f2375000c36ab2d55b4090a289dab`。

Fixtures 证明完整 source-loop lowering 存在，实际原 empty-root source 获得完整
guard receipt，以及 headers／BODY 参数全部 undefined 时 nonzero-row guard
仅写 result=0、跳过 helpers 与所有扫描。接受到 source/model 的定理是 quantified
Clight/Loop 结果；本阶段没有新增 active accepting array fixture 或 native matrix。
没有 empty-build bootstrap、timing 或 Figure 2 optimizer 安装结果。
