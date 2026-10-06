# 依赖 header：checked affine package 到完整局部候选链

后继 [dependent compiler 与完整 C 验收](research-checkpoint-2026-10-06-dependent-compiler.md)已关闭本文下一验收中的 source factory、captures／typed pool／入口 producer、plan／host／Csem→Asm、提取及两类 C 运行缺口。本文保留本阶段的 29 个局部端点和原历史范围；不将后继结果混入本文冻结 report。

本阶段接续 `89fc68b` 的[双观察服务](research-checkpoint-2026-10-06-dependent-header.md)。原来的泛型 prefix／缓存运输要求实例提供 HEADER、DECODE、WIDTH、PERMISSIONS 与 scan coverage；这里已经用真正 checked affine package 填入这些义务，并连接 preparation、完整稳定性检查和既有 candidate certificate。最小 kernel、原 checker、旧 compiler 和提取入口没有修改。

新的局部定理针对实际 Clight 的 `i<**pp` 源和实际生成的候选 statement：接受时沿证明链执行候选，拒绝时执行原复合 header 源，最终 memory 相同、公开 temps 按 live 集合保持。**尚未完成新 source matcher／factory、typed private pool、capture 后入口 producer、全程序安装、提取和原生执行。** 泛型 callback 的实例连接已关闭，不把这项进展扩大为完整 dependent compiler。

## 入口与检查顺序

入口域 `affine_dependent_loaded_completed` 包含：

- row 的实际 integer typing；
- pointer／bound caches 与首次真实 `Mptr`、`Mint32` 读值一致；
- 当前 body pointers 的源观察 receipts；
- 原 compound-header loop 的有限、silent、正常完成执行。

它不包含未来 pointer 或 bound 的稳定性，不预置全部源访问可供 guard 任意读取。body pointers 的 receipts 仍须来自 retained source prefix；private captures 的实际接入 producer 尚待完成。当前正常执行域与旧 affine host 的能力一致，不新增一般 divergence 或任意控制出口。

完整条件顺序为：

```text
源 header／首次 body 支持的 preparation
  → 每个已到达 row 的双观察稳定性检查
  → 既有 candidate 范围／alias 条件
  → candidate 或原 **pp fallback
```

第一阶段失败后不读取 body-only 未定义参数；row probe 失败后不检查未来 row。guard 不执行源 stores；ghost 中的真正源执行仅用于证明已到达的许可。

## 实例证据已填入的位置

| 义务 | 实际生产证据 |
| --- | --- |
| 首次活动 header、inner body 的 parameter typing | [ClightAffineDependentLoadedPreparation](../prototype/interface/ClightAffineDependentLoadedPreparation.v) 从真实 compound header 和 first row 提取；[通用 first-body words](../adapters/compcert-memory/GuardMemoryAffineDependentSourceWords.v) 消费真正 leaf body，复用地址和 scalar 使用位置证书 |
| preparation 检查安全／可完成／接受事实 | 复用 `affine_preparation_evidence` 和既有 arithmetic／width 检查；新 evidence 的两个字段均从实际源生产 |
| HEADER 与 row decode | [ClightAffineDependentLoadedPrefix](../prototype/interface/ClightAffineDependentLoadedPrefix.v) 消费具体双观察 header theorem 与旧 checked-package actual row decoder；额外 root temp 由真正 body 出口保护 |
| 每点 guard 入口 write permissions | 到达 row 的真正 physical iterations 提供全部 write receipts，再沿实际 stores 的权限保持运输回 guard entry |
| 内层 cap 与完整 point 覆盖 | [GuardMemoryAffineDependentRow](../adapters/compcert-memory/GuardMemoryAffineDependentRow.v) 复用 affine bound 的实际求值、signed 范围与 expression scan；每个 point 检查 pointer cell 和 bound cell |
| 外层 cap 与完整 row 覆盖 | [ClightAffineDependentLoadedStability](../prototype/interface/ClightAffineDependentLoadedStability.v) 消费 checked source 的 count／width／control caps，具体化 `ReadonlyPrefixScan`，完整接受提供所有活动 point 的 byte separation |
| 原 compound source→cached source | [ClightAffineDependentLoadedCache](../prototype/interface/ClightAffineDependentLoadedCache.v) 用接受事实实例化 actual-execution transport，保持最终 memory／temps／trace／outcome，不再要求用户另给 body decoder 或全局 load 稳定性 |
| candidate 执行与局部分派 | [ClightAffineDependentLoadedRewrite](../prototype/interface/ClightAffineDependentLoadedRewrite.v) 组合三个实际条件，运输到已有 cached-source candidate certificate；接受执行实际 candidate statement，拒绝保留原 header |

root、pointer-cache temps 必须不同于 row／column／inner-bound。这是本实例的静态保护义务；body 不改写它们的 binding，不蕴含它们指向的 memory 稳定。该稳定性由两个实际 observation 的 byte separation 和 physical write sequence 保持证明给出。

当前 body 仍是已有 `memory_nary_compute` 的 Mint32 operations。不同大小的观察已支持，不代表已支持 typed pointer-store body。上阶段的 offset-4 pointer-cell 反例仍是 memory／guard 证据，不能作为 defined C optimizer benchmark。新局部定理参数化于已有 `affine_inner_pointer_candidate_package`，原 mapped／schedule／tiling checker 可生产该证书类型；本阶段没有新的 factory 调用和提取，不能称三类候选都已在依赖源上原生验收。

## 审计范围

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make affine-dependent-joint-proof
```

七个新增模块均编译通过。独立 audit 校验双观察服务和 private-loaded 两层父报告的 script、source／object bindings，再审计新端点和原 private-loaded 完整 compiler。对父 source 摘要逐项检查，包括位于此次 selected closure 中的文件；没有把新增源文件混进旧编译器的历史产物证据。

最终为 **29 个新增端点，其中 24 个语言端点，518 项 selected dependencies，952 份 source 摘要**。所有新增端点（包括参数化于 candidate certificate 的局部执行端点）最多六项假设，均在原 CompCert 基线内；prefix 上层库端点无公理。原 private-loaded 完整 compiler 回归保持原 mapped／tiling 的 42 项基线，这与尚未调用新 factory 的局部端点范围不同，不主张 compiler 假设减少。

最终 report SHA-256 为 `dbb0301045768400020b7636a40372b4bee6119fb3e723e81b7686f901cedd48`；父双观察 report 为 `772724ae3d42eef83edf284b83cd5a0e133b65a2a23e85e4c9f6baefa817ccb9`，继承 private-loaded report 为 `3fe08e4c4c8e233ad97f32b6ef2c90c31515d67a016a939c298790ff336464b6`。闭包核对为增量编译；本阶段未 clean rebuild 全闭包，也未新增 native 矩阵。此前两套 private-loaded validators 在本次工作中通过产物绑定复核，旧运行次数保持历史范围。

## 下一验收

1. 从真正 original `**pp` AST 识别复合 header，构造内部 cached package；保留实际 original source key 和 fallback。
2. 在原 prefix 之后安全插入两项 private captures。将 prefix body-pointer receipts、捕获值和真正 prepared source execution 接到上述入口域；证明 public／private 运输，不要求私有初值已定义。
3. 分配并检查类型不同的私有资源：pointer cache、integer bound cache、Boolean 和候选 counters。当前全 numeric private pool 不能直接使用。
4. 用已有 plan/code 桥保留 scan continuation 的顺序结构，连接新 signed-expression progress selector、scope／placement、完整 Clight host 和 Csem→Asm。
5. 提取并运行合法的完整 C 接受／拒绝／上下文案例；先覆盖稳定依赖读取与 bound-cell 改写，typed pointer stores 留作明确后继 body 能力。随后继续 guard 循环化、一般深层 affine 源、不同 body base 的 alias 接受、P4 和同例证明责任比较。

narrative `7d94d81` 的责任边界仍有效：条件处理与 prefix 是上层库，实际 memory／控制／context 定律属于语言，域覆盖和候选对应由实例证明；kernel 只组合局部证书。完整 goal active。
