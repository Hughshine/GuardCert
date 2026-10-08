# 双 loaded store-list：数据入口、资源和缓存模型

2026-10-08。本阶段把 [完整 nested guard](word-store-nested-guard.md) 的静态
参数变成可运行检查器输出。两个 loaded axes、任意 checked store list 的
源识别、七个私有 int32 slots、scope、rename 和原源 progress 不再需要在
每个证明实例中手填。缓存模型消费现有递归多数组 checker。

这仍是新的 loaded family 库入口，尚未接本族的 polyhedral candidate 分派、
projected region guarantee、selected compiler 或 native C→Asm。既有已安装
temp-bound 多数组编译器的证据保持独立。

## 接入方提供什么

Domain/优化库的接入方提供实际 Clight `source`、site 所需的 `public`、语言
host 的 typed private pool，以及普通数据 `word_nested_store_description`：

```text
row, root_pointer, root_delta
column, child_pointer, child_delta
body
```

描述没有 cache/scan names、稳定性证明、执行证明或模拟 callback。
`check_word_nested_store_data_source` 独立检查实际 source 与描述重建的 AST
相同，然后分配缓存和扫描资源、识别 body，检查有限 scope 和原 loaded
source 的 progress。无法识别或资源不足返回 `None`。

实际支持的 source 是 `i < *H + delta` 的 strict frontend loop，body 内先
reset `j=0`，再运行 `j < *K + child_delta` 的同类 loop，叶子是 full-word
store list。当前检查器要求精确的此类 AST；C normalization 的 wrapper/reset
适配还需要接前端。它不因此支持任意 dependent bound 表达式或一般 affine
source domain。

再调用 `check_word_nested_store_data_polyhedral_source` 时，接入方提供普通
`describe_cached : statement -> option multi_tensor_region_description`。
它看到实际缓存 AST，包含 factory 已分配的 cache names。返回的是维度、
assignment/access/value metadata、cap 和 profile；既有
`check_multi_tensor_region_source` 重检实际 source、模型、shape 和 box。
它不是用户提供的条件正确性函数。

这组输入属于 domain producer API。最终源程序使用者仍应只给 marked C 和
phase/tile options；本族的自动 C metadata proposer 尚待连接，不能把这个
库接口称为已经完成的源码使用体验。

## 检查器生产什么证明

内部 `word_nested_store_package` 携带实际 source 等式、allocation、checked
body 和 static facts。它是 checker 输出，不是源程序用户需要构造的 record。

| 证据 | 生产/证明责任 |
| --- | --- |
| source 与描述重建的 AST 相同 | domain 数据提案，实际 syntax equality 检查 |
| 两 cache、四 cursor/limit、flag 的 int32 声明、唯一性和 freshness | typed allocator 和语言资源定律 |
| header pointers/cache 稳定 scope、store pointer/index scope、cached scope | finite membership/subset 检查和反射定理 |
| rename 稳定 temps、不改变源 coordinates 的含义 | 语言重命名定律，factory 生成具体 rename |
| 原 loaded source progress | 既有 signed-expression classifier 和 soundness；不使用 cached progress 替代 |
| 从原 source 执行到完整 guard/cached-or-original rewrite | 原源许可与 header 保持服务，`nwsp_rewrite_execution` 自动实例化 |
| cached source/model 和静态 box | 既有递归 multi-tensor factory 对实际 AST/普通 metadata 的检查 |

`nwa_candidate_pool` 排除全部七个 header-private slots。后续候选的 typed
allocator 不得复用它们。Pool 本身仍由语言 host 负责合法声明和整程序
freshness；局部 allocator 不证明任意 pool 可安装进函数。

`nwsp_original_progress` 证明原 loaded source 满足语言 region progress。
`nwsp_rewrite_execution` 对任意该 package，从原 source 的实际正常执行
导出完整 rewrite 的执行，保持原 final memory 和请求的 public temps。
READY、nonnegative gates、cached-source 执行均不是动态输入前提。这里的
source execution 是正确性定理量化的行为，编译时输入不包含它的证明。

`ClightWordNestedStoreDataEntry.v` 使 body 的普通 site list 能直接计算：
正确性事实通过 projection 放进 record，避免对 opaque 合取证明的 case
analysis 阻塞 `vm_compute`。前一成功模块和旧 body checker 保持冻结；两种
入口构造相同的 checked package 类型。所有失败尝试日志保留。

## 接候选还欠哪一条证明

静态构造 cached model 不读取 runtime temps；它不意味着接受入口已定义
所有 cache/scalar。特别是 outer 空域接受可以缺少 child cache。候选 adapter
下一步应实现：

```text
complete source-licensed header guard
if flag then
    if root_cache > 0 then full checked cached-model candidate version
                      else cached source
else original loaded source
```

活跃接受用实际 guard exit 的 cached execution 许可既有完整 multi-tensor
candidate 服务；空域绕开无条件 child 参数准备。内层候选 guard 拒绝时运行
cached source，外层 header guard 拒绝时运行原 loaded AST。两层 fallback 与
public exit transport 都需要实际执行证明。

随后 domain producer 导出 region guarantee，语言 host 和 site 分别检查
context requirement、scope、placement、原源 progress、private declarations
并提供安装 simulation。Generic kernel 继续止于局部证书组合。
Guarantee/requirement 的自由 clause algebra 仍是开放问题，本阶段没有更改
kernel 或 host contract。

## 验证边界和复现

三模块审计 34 个端点：29 闭合、最多 6 项既有 globals、1,280 项实际可达
绑定、零新增公理。冻结 parent report 的 1,142 项绑定逐项核对；未重跑
历史递归审计，未读取其他工作的 column/component 文件。报告为
`build/multi-word-nested-factory/proof-v1/report.json`，SHA-256：
`5f8e904381ae1c2b655bebedf8c53fe066f89adb101cad638680f046d9ea06e8`。

Rocq 求值检查了成功分配、pool 耗尽、重复 slots、public collision、实际
AST 不符的拒绝，以及独立两-store AST 的 cached model 接受和 metadata 不符
的拒绝。真实内存 fixture 由自动 package 导出接受、child alias fallback、
空域完整 rewrite 的 `exec_stmt` 推导。它们不是新增 native/interpreter 测量。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/compile_word_nested_store_factory_sources.py --attempt completed
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_word_nested_store_factory.py --validate
```

本次 fetch 并核对所有远端 heads，narrative 可见仍是 `12419c1`；
`paper-narrative.md` 和 `context-lifting.md` 与 main 内容相同，未发现更新
的已推送澄清。三方责任、原源许可、空域 dependent reads 和真实 polyhedral
集成继续约束后续。Compact condition 的安全/充分性/入口运输、接受域、
code size、runtime work、完整成本和 OLO 功能/可用性比较仍须独立验收。
