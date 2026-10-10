# 整段 source tree：识别、独立进度与 pre-guard header effects

本阶段把原 `fusion1`、`multi-stmt-stencil-seq` 和 `tricky3` 的 marked 区域
作为整棵树识别，保留 sequence、不同 loop 深度、真实 IEEE assignments、
signed literal 起点、global I64 `N`／`N-c` headers 和 frontend skip nodes。
识别结果直接生产 source progress、共享 layout 和 header-frame 证据。
七个 Rocq 模块已编译并审计；固定摘要见[double-source-tree.json](double-source-tree.json)。

**这些原例的优化尚未安装。** 这里验收的是原 Clight source 的静态识别与
实际执行效果，不是整棵树的 source/Loop 对应、动态 condition、调度候选或
新 Csem→Asm 端点。原 native 覆盖仍为 22 原例／39 sites；本阶段不重标它。

## 原代码识别与共享 registry

[GuardMemoryDoubleSourceTreeData.v](../adapters/compcert-memory/GuardMemoryDoubleSourceTreeData.v)
提供 `Skip`、checked assignment、sequence 和 strict range 四种节点。
Raw/canonical 标志保留实际控制语法。Range 保存 signed I32 initializer 与
global I64 header，以及可选 signed I32 subtraction offset。模型参数名按
header 去重；`N-2` 和 `N-3` 仍指向同一个 `N`。所有 leaf accesses 进入一个
共享 layout registry，重复 symbol 必须有一致 dimensions。

[GuardMemoryDoubleSourceTreeDecode.v](../adapters/compcert-memory/GuardMemoryDoubleSourceTreeDecode.v)
的 `checked_double_source_tree` 从原 statement 计算这些数据。Range proposal
可以忽略字段，最终完整 statement equality gate 核对 initializer、comparison、
increment、types 和 raw skip 形状。Static checks 核对 ancestor iterator freshness、
header declarations、assignment descriptors、layout consistency 和全部 header
write exclusions。Fuel 不足或不支持的语法返回 `None`，不会成为语义假设。

三个原始 marked C 经既有 frontend 导出 Clight，再由 Rocq `vm_compute`
证明整段区域的 decoder 接受；没有额外 source normalization。

| 原例 | 区域 | assignments | range nodes | 去重后的 header parameters |
| --- | --- | --- | --- | --- |
| fusion1 | 完整 marked 区域 | 2 | 2 | 1 |
| multi-stmt-stencil-seq | 完整 marked 区域 | 5 | 5 | 1 |
| tricky3 | 完整 marked 区域 | 4 | 3 | 3 |

`tricky3` 包含 scalar assignments 和不同深度的循环。此处没有把 region 拆成
独立优化 sites，也没有运行 scheduler。Source checks 固定在
`build/double-source-tree/source-attempts/source-v2/report.json`；首次 probe 缺少
`Pos.eq_dec` 的 import，三个失败日志、脚本快照及后继成功输入分别保留。
导出器属于既有 trusted frontend 边界；本检查不新增 parser 正确性证明。

## 不借用接受事实的实际 header 保持

[GuardMemoryDoubleRawEffects.v](../adapters/compcert-memory/GuardMemoryDoubleRawEffects.v)
从成功的原 Clight lvalue 求值反推 global array block。坐标只需要 decoder
提供的静态 long 类型；不需要坐标值、mathematical cell resolution、范围或
no-wrap。指针加法可能改变／回绕 offset，但保持 array block。

`checked_double_source_raw_store` 从真实 assignment 执行取得实际 `Mem.store`
receipt。它还消费 checked program metadata、`preserving_globals` 和 write
symbol 的 local-scope exclusion。Global-symbol injectivity 与实际 store 定律
证明不同 header block 的任意 chunk load 保持。这不是任意 pointer-base
alias 检查，不能用两个不同 pointer variable 的名字替代物理分离。

新的 language service
[ClightStructuredMemoryFrame.v](../theories/ClightStructuredMemoryFrame.v) 将实际
assignment effects 沿 skip/set、sequence、if 和 loop 的完成执行组合；它允许
local break/continue，拒绝 calls、returns、labels 和 switch。Relation 可依赖
local environment，需有 reflexivity、transitivity 和 assignment evidence。
它位于 Clight language library，最小 semantic kernel 与 host laws 没有修改。

[GuardMemoryDoubleSourceTreeEffects.v](../adapters/compcert-memory/GuardMemoryDoubleSourceTreeEffects.v)
由 checked tree 自动构造该 evidence，证明整树每次有限完成执行保持 checked
headers 的 loads，并保持所有 blocks 的 `Mem.perm`。结果不依赖 guard 接受或
source/model point resolution。它填补了 pre-guard effect 服务；后继仍须把
具体 reached-header receipts 按真实路径运输到 capture 入口。它本身不许可
读取未到达的 child，也不构造多 header guard。

## 静态证据直接接到原 source

[GuardMemoryDoubleSourceTreeProgress.v](../adapters/compcert-memory/GuardMemoryDoubleSourceTreeProgress.v)
递归使用 assignment、sequence 和 strict long-loop protocols；body 保护 ancestor
iterators，新的 iterator 不在其 protected set 中。协议独立于 bound stability、
guard acceptance 与模型范围，可以表示 stuck execution，不能称为任意入口
的正常终止保证。Nullable skip 可用作 child；region certificate 要求 root
为 sequence 或 range，确保符合现有 host 的 active-entry 契约。

[GuardMemoryDoubleSourceTreeCertificates.v](../adapters/compcert-memory/GuardMemoryDoubleSourceTreeCertificates.v)
把 decoder soundness 直接连接到原 statement 的 region progress、header-frame
定理和每个 leaf 的 shared-layout certificate。实例化者仍提供真实 language
state／scope；C 用户不提供逐 assignment 的 semantic callback。

审计查询 25 端点，其中 6 closed、最多继承 6 个既有 globals，无新增全局
假设。七模块 656 行；249 reachable sources 和 9,858 bindings 固定；29 次
proof attempts 中 7 次成功，失败输入／日志保留。这里只计新端点的实际范围，
不据库存在、import 或 kernel 未改推断作者负担收益。

## 下一项实际连接

继续保留整段 source tree，构造相同 shared registry／header vector 上的 Loop
模型及实际 IEEE／Mem 双向有限执行对应；在 instance 中闭合机器参数编码、
控制与 point ranges，恢复准确公开 exits。利用新 raw effects 运输实际首次
观察，按路径许可 child captures；empty outer 跳过未到达的 child 读取。
拒绝和独立 source progress 不借用接受后事实。

随后同一 factory 必须实际消费这些证据，运行 phases/codegen，验证最终候选，
经机器 lowering、当前程序 installation 和 CompCert backend 完成新 Csem→Asm
路径。新 source 检查通过不减少这些义务，也不替代 OLO compact conditions、
sequential configurations、其余原 benchmark tiers 和完整调用成本验收。
