# 在一个程序中交替单缓存与双缓存 rewrite

综合入口已消费双动态内存上界的矩形交换，并保留原有单缓存和精确出口规则的优先级。规则仍提交 source、candidate、condition、D／P、局部观察等价和源入口证据；规则作者无需重做条件或局部调度证明。这个案例验证不同安装方式与私有资源如何在一个完整程序中组合。

## 使用者 pass 的接口

[ClightCommonRewriteCompiler.v](../prototype/interface/ClightCommonRewriteCompiler.v) 的 `common_region_selection live pool source` 返回实际替换语句及单次 region correctness。它先使用原 `projected_readonly_selection choose_common_rewrite`：精确出口规则经已有嵌入，私有快照规则直接使用 projected rule，没有改变它们的原直接树 lowering。没有旧规则匹配时，才尝试 `shared_projected_selection choose_simplified_dual_rectangle`。

第二项消费同一双动态矩形 rule，先用 `simplified_projected_rule` 保留 D／P 与局部证书地简化重复实际测试，再用共享出口安装 guard、唯一候选和唯一原片段回退。共享安装另核对 candidate quiet 和 private Boolean freshness。

`transform_common_regions` 提出三个与全部原程序 temps 分离的 signed32 private slot。旧单缓存规则使用第一个；双缓存规则将第一个用于 Boolean、后两个用于 rows／columns cache。资源数量、规则顺序及采用哪种有证书的 lowering 都是这个使用者 pass 的选择，没有加进语言无关核。

这些 slot 可以跨互不重叠的 region 复用。这里不需要全程序始终保留旧 cache 的值：每次候选在使用前执行自己的 preload，分派在使用 Boolean 前保存当前 guard 结果；局部观察只隐藏新鲜私有 temps，所有原 temps、memory、trace 与 control outcome 继续受到保护。只读抽象 guard 仍完全不改变入口，实际 Boolean 写入由已有 frame／scope 证明处理。

## 框架消费哪些证明

| 接口／定理 | 本使用者提供或复用的义务 |
| --- | --- |
| `common_region_selection_sound` | 分别消费原直接安装和共享安装的 region contract |
| `common_progress_supported_sound` | 选中宏片段的独立源进展，不能假定 loaded bounds 稳定 |
| `transform_common_regions_correct` | 私有池 freshness、源 scope、单次 contract 到真实 Clight forward simulation |
| `compile_common_rewrites_correct` | 再组合逐步求值 rewrite 与 CompCert，得到完整 Csem→Asm backward simulation |

同一个函数中后续规则使用各自到达时的实际入口。第一段 guard 接受的事实不自动成为第二段的前提；中间 memory 写入会使第二段重新读取和检查。多次替换的正确性消费单次 contract 和 continuation 运输，完整程序端点没有将此程序当作一条需要手工整体等价证明的新规则。

## 实际交替程序

[common_multicache.c](../prototype/interface/tests/common_multicache.c) 中的一个函数依次包含：

```c
// 第一段：普通参数 load 提升，候选用一个 cache。
for (i = 0; i < n; ++i)
  *out = *parameter + (unsigned)i + 1U;

// 第二段：两个 memory-bound 维度，候选用两个 cache 并交换。
for (i = 0; i < *rows; ++i)
  for (j = 0; j < *columns; ++j)
    cells[i*4+j] = i*10+j+1;

*parameter = 23U;
*rows = next_rows;
*columns = next_columns;

// 随后再次执行两类 rewrite；矩形 payload 改为 i*7+j+2。
```

fixture 在后续覆盖之前观察 payload、完整十二单元数组、两个公开 counter 和当前两个 bound。它同时包含不同对象、安全的同数组非活动单元、共享 bound、活动 alias 改变行／列数、空维度、布局外但合法的空内层，以及两次改写间的接受／回退切换。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-common-native
```

这个目标运行原有综合 fixtures、新双动态矩形 fixture 及新交替程序。实际提取编译器在交替程序上通过 120 次函数调用／720 行输出，同 GCC、无诊断 GCC UBSan 和独立逐头部 source 模型一致。每个 source 头重新读取当前 bound，模型不使用候选缓存解释 fallback。

输入模型分别分类 64 次第一矩形接受、64 次第二矩形接受、32 次前后接受类别变化；60 次 payload alias，40 次输入在至少一段矩形中改变了 bound。这是输入分类，不是测得的 runtime branch count。生成 Clight 另确认四处实际 macro region、两个不同 affine candidate、每处两项独立 bound preload、两份真实源 fallback，以及 private 单缓存槽复用为两次共享 Boolean 分派。每次快照的位置确实在该段实际参数改变之后。

同一综合入口的原双动态矩形 fixture 另通过 113,330 次调用／八处 region；原混合单缓存／精确 fixture 保持 576 次调用／2880 行输出。各自独立输出检查避免后续正确覆盖掩盖前段错误。

## 审计与保留的范围

当前完整审计 368 个端点、850 份证明源码摘要，不超过 FRAGMENT=6、MEMORY=1、REGION=6、PROJECTED_REGION=8、STEPWISE=8、COMPILER=35 的既有分层基线。两个新宿主端点按 MEMORY 与 PROJECTED_REGION 的并集比较，显式继承既有 memory 记录相等的 `Axioms.proof_irr`；最初误按单独 region 基线分类导致审计拒绝，修正分类后重新完整审计。24 种提取配置全部重建回归，39 份原生报告绑定当前证明及编译器。相对 `ae80fe6`，37 份旧 C 摘要相同；24 份旧 Clight 摘要相同，12 份综合入口 Clight 的逐行差异只增加两个 private 声明；另一份仅额外在原六单元 `refused_extent` helper 接入合法通用矩形规则（只编译／检查），所有已匹配的旧规则语句相同。

双动态矩形选择器仍要求 extent≤12、静态 stride 和一个经语法／布局证书核对的 affine store。旧规则也保持各自 cap 和 body 范围；本例没有完成一般大布局／指针缓冲区、双 loaded 与参数 stride、多个依赖 preload、复杂 body 或旧 affine／tiling 的主接口迁移。没有性能测量，完整 OLO 主线仍按 [验收账本](optimistic-loop-acceptance.md) 记录未完成项。
