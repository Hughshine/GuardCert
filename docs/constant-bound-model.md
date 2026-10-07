# 常量子循环到 affine 模型：检查安全的许可桥

2026-10-06。这是 [层次 loaded header 服务](nested-header-services.md)的后继，
用于 Figure 2 的第三层原 `<5`。完整 joint scan／optimizer 安装仍未完成。

关键输入是一段**原 source 实际到达的子循环执行**。不能用尚未建立稳定性的
完整缓存 outer/child execution 来替代它。本文的 `memory` 始终是实际 source
到达的 memory；`guard_memory` 是检查起点，两者通过权限关系连接。

## 准备 private model bounds

原 child cache 是候选域的参数，canonical child bound 是模型控制资源，二者
不能在 metadata 中随意混用。语言提供实际 Clight 准备代码：

```text
child_model_bound = child_cache;
component_model_bound = 5;
```

`model_bounds_prepare_execution` 从已捕获的 child word 得到这两条 assignment 的
真实执行，memory 保持；helper 可在此前未定义。`model_bounds_prepare_source`
要求 helper 不在原 source 的 temp scope 和 public live 集中，证明同一原 AST
可从 prepared temps 执行，保留 final memory 和 public 出口，并保留 helper words。
child capture 的读取许可仍来自上一阶段的 ordered capture；本服务不提前加载它。
完整 guard 应在 outer 实际进入、child capture 完成之后调用准备阶段。

有了初始化，canonical body 中反复执行的 helper assignment 是赋同一个值。
`initialized_bound_assignment` 证明这些 assignment 保持 exact internal temps。
`constant_loop_preinitialized_model` 将原 literal test 换成 helper test，
`constant_body_preinitialized_model` 再包含 reset 和 canonical bound assignment。
`cached_child_preinitialized_model` 提供 child cache →独立 model bound 的同类桥。
最终整段 cached source →canonical nest 的递归组装仍由 domain client 完成。

这修正了前阶段“额外 assignment 都需 projected transport”的实现选择：整体
private preparation 到原 source 仍使用 public projection；prepared 状态内部的
已初始化 bound assignment 可以证明 exact，不需要新增通用 loop kernel 定律。

## 从原子循环执行得到全部点权限

`constant_affine_prefix_body_decode` 的核心输入是：

```text
实际 reset component; for(component < 5) body 的完整正常执行
prepared helper = Int.repr 5
prefix/parameters 的 word view，data pointers 的 frame
checked affine source/leaf shape 与 numeric math domain
```

输出是这段子循环对应的真实 `Loop` 模型执行。`prefix` 不限于一个轴，可以
包含 `[row; column]`。它不要求原 outer 或 child loaded bound 已稳定，也不要求
缓存的 enclosing loops 有完整执行。任意更深 canonical descendants 仍须满足
原有 shapes／freshness／dependency／leaf certificate，不能只宣称一个模型接口。

`constant_affine_prefix_body_capabilities` 继续消费这个 source/model 对应和既有
affine footprint 定理，证明该子域每个 scan point 的所有 leaf read/write cells
在 `guard_memory` 具有所需权限。它要求语言 prefix 提供
`memory_accesses_back guard_memory memory`；只运输 permissions，不运输 source
已经改写的数据值。这些权限供后续实际写地址比较使用，比较的 Boolean 编码、
raw observations 和接受后的观察保持仍需接入。

因此，即使 component body 已改变 loaded child word，只要这个固定第三层
body 是原 source 实际完成的执行，权限桥本身仍可使用。它不推出 child/header
稳定，也不许可 source 未到达的下一个 column。

## 实际 fixture 和验证边界

fixture 从实际 reached `component=4` 的第五次 store 开始，literal upper=5。
同 block offset 4 的原 word 是 1，store 后变成 2；这个位置可作为 loaded child
header。source 执行后 component=5；helper=5 的 canonical loop 得到相同 temps
和 final memory。此 fixture 是一次实际 store／第三层 tail execution，不是完整
五次 store 或三层 optimized Figure 2 的 native 结果。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make constant-model-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make constant-model-validate
```

`build/constant-bound-model/proof/report.json` 审计 14 endpoints，required closure
565 源，连同 inherited material 绑定 1,060 源摘要。新端点最多使用 6 项已有
CompCert global assumptions，无新增公理。继承 nested-header report 的 sources／
objects 在编译前后保持；旧完整 compiler regression 保持 42 项 assumptions。
工具链仍是 CompCert 3.18／Rocq 和 Stdlib 9.2。

报告 SHA-256：
`3d0d95a6de499127db58406ffe8854b63090c58002948024751d891688d3d1b8`。
这是当前 inherited build 上的增量 audit；没有另验空 build bootstrap。
没有新 compiler、extraction、native 矩阵或 timing。

下一连接是使用 reached inner BODY receipt 实例化这些 point capabilities，
在 guard entry 逐写地址保护**全部** captured observations；检查接受才推进
inner prefix，一 row 接受才推进 outer，再导出整个 cached model 和原 AST 安装。
