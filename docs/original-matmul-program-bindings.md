# 原 matmul：实际程序前提与 scoped host

2026-10-09 后继从实际 exported Clight program 的声明生产原 matmul 使用的
global bindings，并把[实际 guarded execution](original-matmul-double-lowering.md)
接到 program-scoped region contract。它解决旧 universal contract 与实际
program facts 的量化差距；完整 matmul 安装仍待 source progress、site/factory
和 Csem→Asm 接入，没有新已安装 benchmark 或 native／成本结果。

## 为什么声明检查需要环境 invariant

旧 `PrivateRegion.projected_region_contract` 对任意 program 和 local environment
量化。原 matmul 的 globals/layout 事实来自特定 program；它们不能仅凭一次
声明检查在任意 environment 中成立。局部变量还可能遮蔽同名 global。

`ClightGlobalScope` 检查整个实际 program 的每个 internal function：指定
global IDs 不出现在 params/vars 中。实际 allocation 和两种 Clight function
entry 都保持这项不遮蔽性质。Continuation invariant 记录调用时保存的
caller locals；所有实际 source steps，包括调用、返回和 goto，保持 invariant。
初始状态从 program 检查建立它。因此到达 rewrite site 时，host 可以交付
`locals_avoid globals locals`，而不是要求 C 用户证明这一事实。

这是一个保守的静态 eligibility 条件：当前检查所有 internal functions。
局部化到受影响函数可以提高接受范围，但不是此检查点的证明结论。

## 语言 host 的后继契约

`ScopedPrivateRegion.projected_region_contract live reference globals S T` 仍
量化 temps、执行状态、function 和 continuation，但只消费两项 host facts：

- 实际执行环境保持 reference 的 global symbols 和 composite environment；
- locals 不遮蔽指定 globals。

它要求有限正常 source execution 能从公开 temps 对应的 target entry，产生
target small-step execution，并保持公开 temps 和 memory equivalence。
旧 universal contract 可直接解释为这个 scoped contract。

`ScopedPrivateRegionProof.transform_program_correct2` 在实际 program 的
global-scope invariant 下证明整个 Clight program 的 forward simulation。
它仍要求 selector 的 scoped contract、source `region_progress`、public scope
和 fresh private resources。结构证明是既有 private-region host 的后继；AST
变换直接复用 `PrivateRegion.transform_program`，没有第二个 IR，也没有改
通用 kernel。不能把新的语言 host 定理混称为 kernel 自动获得 contextual closure。

`transform_scoped_private_program` 计算 `program_temps`，检查 no-shadow 和
private pool；静态拒绝返回原 program，检查成功使用该 AST 变换。Selector
可依赖实际 program，并须生产它的 scoped contract。

## 原 matmul 的实际证据生产

`GuardMemoryDoubleProgramBindings` 核对真实 `Gvar` 声明和类型，通过
CompCert global-environment 定律取得 symbols，再消费 host 的不遮蔽事实。
它不从声明推导 memory permissions 或可读值。

`OriginalMatmulProgramBindings` 对实际 program 检查八项声明：A/B/C 为
100×100 nested double arrays，alpha/beta 为 double，M/N/K 为 signed I64。
No-shadow 检查成功。`original_matmul_checked_static` 自动生产五个 data
bindings、三个 header bindings、padding range 和 physical layout span。
`original_matmul_checked_guarded_execution` 因此不再接收手写 blocks/static
premises，而由实际 program metadata 和语言 host facts 生产它们。

`original_matmul_scoped_contract` 再使用原 source 的 structured temp transport，
把公开 temps 对应的两个入口连接到实际 capture/candidate/fallback execution，
交付上述 host contract。实际 source execution 仍是语义证明起点，不在 runtime
先执行 source；pipeline/lowering receipts 仍须来自真实候选检查。

## 责任与下一步

本次 fetch 后 narrative 远端仍为
`topdown/research-positioning@8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9`，
main 的 narrative/context-lifting 正文一致。沿它的责任划分：

| 提供者 | 此次交付 | 仍须交付 |
| --- | --- | --- |
| Generic kernel | 沿用局部 guarded composition | 不承担具体 globals、Clight scope 或 source progress |
| Language/IR host | Checked no-shadow invariant、actual global binding、scoped whole-Clight simulation | 连接具体 source progress、site/resources 和 CompCert backend |
| Domain/optimizer factory | 原 matmul typed metadata、实际 guarded region contract | 实际 I64 source progress 及 selector/factory、Csem→Asm 接入 |

最直接的剩余证明是原 I64 nest 的 progress protocol。有限执行对应和 candidate
model progress 不替代 source protocol，也不自动证明 divergence preservation。
再把实际 selector、private resources、placement 和 typing 接上，执行原 C→Asm
accept/fallback/context 验收。62-case corpus、BT 和全部要求的顺序路线及优化
效果／完整调用成本仍在总目标中；当前检查点不缩减这些验收。

## 可复现证据

[机器摘要](original-matmul-program-bindings.json)绑定新 proof report。
六模块970行、15端点／4 closed、275 reachable sources／7,650 bindings，
至多14个 inherited globals，均属于原42-global baseline，无新增公理。
六次成功、十五次拒绝证明尝试保留；attempt JSON 记录实际编译 return code。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_original_matmul_program_bindings.py --validate
python3 scripts/summarize_original_matmul_program_bindings.py --validate
```

该阶段没有新的提取/native 实验或收益／成本结果，原 corpus 的新安装优化
案例仍为零。Scoped language-host theorem 已完成；实际 matmul whole-program
compiler 尚未完成。
