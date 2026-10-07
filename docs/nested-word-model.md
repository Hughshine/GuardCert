# 相同 word 条件：实际循环、缓存模型与检查出口

2026-10-07，接续 [constant-word observation](constant-word-observation.md)。
本阶段把固定 cell 的语言性质接到实际三层原循环、canonical 模型和两次比较的
Clight 检查。当前 compiler 仍运行原 guard；新的 producer 尚未接入 factory／提取。

## 条件及使用方式

优化实例先提交既有 `nested_constant_site` 数据，以及 word `w`。静态
`check_constant_word_statement w (ncs_leaf shape)` 必须接受；它检查实际 typed BODY，
不是使用者手填“所有 writes 都是 w”的语义假设。真实仿射索引写 `1` 的 fixture
同时通过旧 source/model package 与这个 checker。

在既有 row gate、有序 capture、positive／numeric gates 和 helper 初始化之后，
新检查只比较已初始化的私有缓存：

```text
root_cache  == Int.add(w, root_delta)
&& child_cache == Int.add(w, child_delta)
```

这些是 computed bounds，不是 raw header values。`ncs_same_word_flag_raw` 消费实际
header receipt，并利用 machine `Int.add` 的消去律，证明接受时两个 raw headers
都等于 `w`。此逻辑在 modular arithmetic 中成立；control／address 的 numeric
要求仍由旧 gates 单独提供。它不增加 header load 或 pointer comparison。

使用入口是
[ncs_prepared_same_word_check](../prototype/interface/ClightNestedConstantWordCheck.v)：
消费由原 source 正常完成生产的 `ncs_prepared_receipt`，交付真实检查执行、same
memory、`ncs_ports` frame、定义的 Boolean 结果，以及接受后的模型执行与原公开出口。
调用者没有新增 model／prefix／BODY 语义回调。片段识别、候选和具体 site 数据
仍由优化实现者提供；候选正确性继续是独立的证明环节。

## 已闭合的链

语言服务 [ClightWordObservationControl.v](../prototype/interface/ClightWordObservationControl.v)
扩展分类至 sequence、if、loop、break／continue，并从实际有限 `exec_stmt`
归纳取得 `constant_word_stores`。Unsupported calls／returns 等结构保守拒绝。
这是完成执行的 memory 保证，不是终止性或任意 temps 的保持。

Domain producer
[ClightNestedConstantWordModel.v](../prototype/interface/ClightNestedConstantWordModel.v)
把这个保证用于整个 literal subloop，证明每次原 BODY wrapper 执行保持两个 header
observations。它消费 checked site 提供的 pointer／control frame 和旧 capture／helper
receipts，再直接实例化 `nested_expression_initial_cached`，取得真实 cached source；
旧 `nested_constant_closed_preinitialized_model` 将其接到 canonical Clight 模型。
Same-cell header/data alias 由 value preservation 支持，没有推出 address separation。

实际 [Clight 检查](../prototype/interface/ClightNestedConstantWordCheck.v)使用嵌套 if
和私有结果 temp。其执行、短路行为、ports frame 和结果均已证明。模型入口保持在
检查前，actual check exit 可以有不同 scratch state；接受交付的 frame 明确运输
这两个入口。没有把缓存模型执行用于许可原 source 的 capture。

三方责任保持：kernel 未修改；语言证明实际 store／control／comparison 性质；
domain 将这些性质与已检查 source shape、安全 capture 和 numeric 前提组合。
语言 host 的安装、progress／divergence 和 placement 仍独立于这份局部 producer。

## 验证和剩余工作

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_nested_word.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_nested_word.py --validate
```

22 个直接查询端点（3 language／10 domain／9 fixtures）、508 required dependencies
通过。独立查询的 memory／Clight 基线并集为 6 项既有 assumptions；全部端点为其
子集，kernel 闭合，零新增 global axiom。报告绑定实际 sources、objects、helpers
和查询 artifacts，不依赖旧 proof report。

`build/nested-word/proof/report.json` SHA-256：
`ce5c202de41b517fc4b9e51b81b239754a5278758dadef995255c731695677ae`。

Fixtures 核对实际三层语法、旧 package／新 BODY checker 同时接受、两个缓存值的
接受／拒绝，以及实际 accepting check 和 first-refusal 跳过未定义 child cache。
没有新 compiler、native matrix、性能／接受域测量。

下一项把这个 producer 接到实际 physical guard、multi candidate adapter 与 typed
factory。优先保留旧扫描作为新条件不成立时的路径；新条件接受可跳过 header-stability
扫描，其他 BODY 继续使用旧服务。不得用 descriptor 中的语义回调代替已生产的
模型入口证据。随后测试 header/data overlap 的 candidate 路径、不同 raw word
的旧扫描／原源回退、完整上下文，并分别测 residual check work 与完整 guard 成本。
两次比较的 bounded work 不意味着整份 guard 已具有常数成本或优化有收益。
