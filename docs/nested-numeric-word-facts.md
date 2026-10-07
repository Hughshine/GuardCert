# 已知 word 的 numeric/domain 充分事实

2026-10-07。该库是条件推导服务；当前生产 compiler 和 runtime guard **未改变**。
源文件为 [ClightNestedNumericWordFacts.v](../prototype/interface/ClightNestedNumericWordFacts.v)，
示例为 [ClightNestedNumericWordExample.v](../prototype/interface/ClightNestedNumericWordExample.v)。

## 使用方式与保证

已有 nested site checker 绑定真实源、模型、参数范围和 private names。新数据
检查器 `ncs_numeric_word_check parameters proposal shape word` 不接收语义回调。
它只接受所有模型 parameters 都属于两个 header caches 的情况，并在包含
`row=0`、`root_cache=Int.add word delta`、`child_cache=Int.add word child_delta`
的临时环境中计算既有 numeric 条件。

调用方从实际 capture/condition 取得这三个 bindings，提交静态 checker 的正结果，
即可调用 `ncs_numeric_word_sufficient` 得到真实入口的 numeric flag；进一步调用
`ncs_numeric_word_math_domain` 得到既有 affine math domain。库复用 site 的
parameter dependency 和 frame 定理，将计算环境的事实运到实际环境。
`ncs_numeric_temps_flag_exact` 证明纯 temps 求值与原有包含 ge/env/memory 的
入口条件完全相同。Machine additions 使用 `Int.add`，不能先按数学整数假定无 wrap。

该证书不要求原 BODY 已通过 constant-word checker；它只谈已知缓存值的 numeric
充分性。要用同值 BODY 推导稳定性，仍需原 typed BODY effect checker 和模型运输。
额外 parameters、未通过范围检查、负值/零 counts 或 wrap 后失效均保守拒绝。

| 责任 | 本库的实际工作 | 仍由其他层提供 |
| --- | --- | --- |
| 最小 kernel | 保持不变 | 消费 guard 和 candidate certificates |
| 语言服务 | 既有 machine word、temp frame 和原 guard 编码 | actual capture 的读许可、definedness、执行和公共 frame |
| domain 服务 | 静态充分事实计算及 soundness、既有全域 math domain | BODY effect、source/cached/model 对应、alias 和候选正确性 |
| host/site | 既有 checked site 提供范围、依赖及 namespace | actual check-exit transport、fresh resources、region/progress/placement |

不能将正 Boolean 当作新的 actual-execution receipt。本轮未把 numeric 检查从生产
guard 删除；后续 residualization 仍须证明实际新代码运行，以及 helpers/model entry
到它的 frame。固定成本的简化也不能替代常见非同值输入的 footprint/alias 条件。

## 验证与发现

独立 audit 查询 34 个端点、600 个依赖、899 个绑定源；新增四个定理的假设均
为空，kernel 闭合，既有 Csem→Asm compiler 的 42-global baseline 保持。没有
依赖历史 proof reports，runtime compiler entry 保持原值。

七个 fixtures 覆盖 word=1、word=15、typed site construction，以及超 profile、
computed-count wrap、空 count 和未知参数的拒绝。Literal-15 新 fixture 使用
实际 frontend 的 cached-count 区间 `[1,17)`；前阶段 construction-only fixture
使用 `[0,16)`，它能构造 site，但 count=16 的 runtime numeric 条件会拒绝。
这正说明静态 package 构造成功不能代替条件在目标输入上可接受的证据。

报告 `build/nested-stability-shared/numeric-facts/proof/report.json`：
`8f0dc06f7c6d578fc4c1fda2392f2218066c4e16b297d47773b2a57f43a94281`。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_nested_numeric_word.py
```

本轮也更正成本归因：原 numeric guard 是 first-path probe 加参数区间 tree，
并非逐 iteration-point 检查。真正的迭代成本来自 stability 和跨数组 alias scans；
新完整成本报告将这种区别与候选 traversal/public-exit 成本分开。
