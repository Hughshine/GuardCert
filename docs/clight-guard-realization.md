# 共用的实际 guard 分派接口

这是 P1 的实际接口，与 [三方责任](framework-responsibilities.md) 对齐：语言实例证明分派和私有 state 运输，优化作者仍提交原条件和局部规则，语言无关 kernel 保持不变。源码在 [ClightGuardRealization.v](../prototype/interface/ClightGuardRealization.v)。

## 对使用者有什么变化

规则作者仍提供真实 source／candidate、D／P、readonly condition、条件性局部证明和 source placement／scope 证据。没有要求作者重新证明共享分派，也没有给 direct 规则增加 quiet-candidate 限制。既有 choose、规则优先级、private pool 检查和实际 Clight 生成方式保持；这次将两套安装证明归入同一边界。

语言库提供两种 realization：

| 实现 | 实际代码 | guard 后 temp 环境 | 资源与义务 |
| --- | --- | --- | --- |
| direct | `tree_statement tree yes no` | 原 le | 不占私有 slot；复用已有 `decision_dispatch` |
| shared | `shared_guard_statement tree result yes no` | `PTree.set result (Vint word) le` | 一个私有 Boolean；result 不属于任一分支的 temp 使用位置或 live；pool 分配／声明仍由现有宿主核对 |

`clight_guard_realization` 给出实际代码、私有名字、guard 后环境及两个资源定律：私有名字新鲜；其余 temp 不变。`realization_entry_agree` 从这些定律推出两分支所需 temps 和 live 的 agreement，不把实际 raw temp map 的写入称作 logical check 的 effect。

最关键的执行定律是：

```text
decision_run original_entry tree accepted
    ⇒ 实际代码经过有限、E0、memory 不变的 Clight 小步前缀
    ⇒ State (if accepted then yes else no)
             同一 fn / continuation / locals / memory
             realization_entry accepted le
```

这个定律不要求 yes／no 执行完，甚至不要求其下一步有定义。真实 guard 的定义性和可用性由原 condition 证书提供；realization 消费其 `decision_run` 证据。该法则是 forward dispatch 证明，不另造一个 abstract select，也不单独声称所有执行的双向等价。

## 怎样连接局部规则和宿主

完成执行的宏片段需要额外的 branch transport。`clight_normal_realization` 在上述分派证书上增加：若逻辑选中分支从原 le 正常结束，实际分支能从 realization_entry 正常结束并保持 live 与相同 memory。

direct 的这一步直接复用原执行，对 candidate 没有新增 write-frame 限制。shared 消费两个分支的 `writes_only` 和 result freshness，复用 `structured_execution_temp_transport`；当前 selector 仍以原 quiet-candidate 检查提供其 write bound。这个限制属于现有 shared 宏适配器，不加入 kernel 或所有 direct 用户。

`realized_guard_normal_steps` 将有限 dispatch 与运输后的真实分支执行相接。[projected_realized_rule_region_contract](../prototype/interface/ClightReadonlyProjectedCompiler.v) 在同一处消费 source 的公开 temp 运输、原 condition／local certificate、realization 和公开出口，得到 private-region 契约。原 direct 和 shared 的公开 contract theorem 都调用它，完整编译入口继续使用既有上下文与 CompCert 后端证明。

10 月 6 日进一步抽出 `realized_projected_selection_contract`：双向规则及新 source-to-candidate 保持规则分别提供所选实际分支的执行见证，语言安装证明共用。[真实 named affine／tiling 使用者](clight-polyhedral-preservation.md) 已消费这条路径，同一原条件和局部保持证书支持 direct/shared。旧 local rule 的方向及实际 globalenv 量化保持，不为迁移增加一个未证明的反方向。

这仍是要求 source 独立 progress 的宏宿主。把分派前缀改成不要求分支完成，不会自动取消该宿主的 progress 假设。

## 哪些实际使用者已接入

1. direct projected 安装路径，包括稳定参数、loaded-bound 和现有矩形规则：消费 `direct_normal_realization` 和公共安装定理。
2. shared projected 安装路径，包括 shared／simplified rectangle 与双动态矩形：消费 `shared_normal_realization` 和同一公共安装定理。没有重做 alias scan、调度或 condition 证明。
3. 新 open host 的 unsigned memory-bound 完整循环：[circular_guard_dispatch](../prototype/interface/ClightCircularPrefix.v) 消费 direct 的有限前缀证书。空路径、alias 回退、non-alias 候选都沿用这一证明，再与原局部小步协议连接；无限 fallback 不需要正常结束的 realization 层。
4. [真实 named affine／tiling 使用者](clight-polyhedral-preservation.md)：接受真实 mapped-domain／依赖或 tiling／依赖证书，复用旧实际数组执行对应后，通过同一保持接口和两个 normal realization 安装。它保留 finite source-progress 宿主，没有借此次迁移获得多面体无限源回退。

第三项没有安装 shared whole-loop 编译路径。共享前缀定律已经不要求分支完成，但为这个具体 open 协议运输 private Boolean、连接新的 matcher 和提取入口仍须单独实现／验收。任意内部 call／return／label 也没有因此进入当前 open host 的支持范围。

## 复用和剩余难点

当前规则证书、条件算法、候选调度和模板支持域保持。两个 finite compiler adapter 共用逻辑选中分支见证和实际安装证明，完整循环复用 dispatch prefix；新接口确实被这些实际编译证明消费。新增通用模块本身增加了证明代码：对 `26956a4`，公共模块新增 154 行，direct 文件 172→176、shared 155→123、完整循环前缀 101→126 行。这是整个文件的行数，不是证明负担或复用比例；不能因此声称总证明行数下降；后续量化应统计新的规则作者要写什么、是否还重复语言安装证明，以及维护成本。

最难的主线仍是 `B⇒A` 的全实例覆盖、源／候选真实语义与依赖对应，以及让实际 affine／tiling 候选消费这一主接口。realization 统一不替代这些 optimizer/domain 证明。当前验证结果和产物绑定以 [最新阶段记录](research-checkpoint-2026-10-05.md) 为准；性能没有测量。

P1 固定验收为 411 端点／863 摘要，无新增全局公理；25 种提取配置全部重建／回归，40 份 native 报告核对该阶段源码和产物。相对 `26956a4` 保存的 40 份 C／Clight 摘要全部保持，包括 whole-loop 与混合旧 preload。报告为 `build/interface-compiler/realization-validation.json`；不能从一致性回归推出新的优化收益。保持证书接入后的当前结果单独见 [10 月 6 日记录](research-checkpoint-2026-10-06.md)。
