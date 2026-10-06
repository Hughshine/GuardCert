# 只读条件的共享候选／回退出口

下文验证计数保留最初接入阶段。当前 direct/shared 已接到 [公共实际分派与安装接口](clight-guard-realization.md)，复用相同逻辑规则证书；最新产物与回归另见 [阶段记录](research-checkpoint-2026-10-05.md)。该分派前缀本身不要求选中分支完成，但本文的 finite 宏片段宿主仍有其 source progress 要求。

嵌套前缀检查已经能够证明动态内存上界的矩形交换，但直接用 `tree_statement guard candidate source` 会在每个叶复制一个完整循环。12／4 的实例每处 region 展开 156 份候选。共享出口适配层复用原条件与局部规则，将完整循环放到检查之后各一次。

## 使用者的接口保持什么

使用者仍交付 `readonly_projected_clight_rule`：真实 source／candidate、入口域 D、接受性质 P、只读条件、条件性局部观察等价和源入口证明。选择器和源 progress 仍由使用者提供。抽象条件仍是原来的 `decision_tree`，接受性质和源前缀安全证明保持原样。

共享适配层另外核对 candidate 是 quiet statement，并从 private pool 取一个 Boolean slot。这个 slot 必须不出现在 source／candidate 的所有 temp 使用位置，也不能属于原程序的公开 temps。其余 private slots 继续交给原使用者选择器，矩形实例用其中一个缓存 bound。

quiet 是已有语法证书，普通 load/store 和循环可以满足。本例候选的 stores 仍由原局部调度证明负责。

核对失败时保留源。这个适配层复用已有宏片段宿主，要求被选中源的独立 progress；它不扩展到潜在发散的整段选中循环。

## 实际生成代码

```text
if test1 then ...          // 原检查树，仅在叶写新的 private_result
  private_result = 1
else
  private_result = 0

if private_result then
  candidate               // 一份
else
  source                  // 一份
```

检查表达式及其求值顺序不变。所有检查完成后，编译器才在叶保存 Boolean；后续只有一次分派。抽象 condition 的执行不改变声明的入口 state。实际 Clight 实现增加一个编译器私有 temp，因此其原始 temp map 会不同；适配层显式证明原变量、内存、事件和出口观察保持一致。

这两种陈述必须分开：不能声称实际 lowered Clight 原始 temps 完全没写，也不能让 private_result 任意影响用户 candidate 或 continuation。freshness／scope、实际执行运输和公开观察证明负责这条边界。

## 证明提供什么

`ClightSharedGuard.v` 将实际 `decision_run` 连接到 Boolean materialization 的 `exec_stmt`，并把选中分支接到后续唯一的 `Sifthenelse`。

公共 `projected_rule_selected` 消费原 `readonly_available`／`readonly_sound` 和 `projected_rule_local`，取得逻辑选中分支的实际完成执行。`ClightSharedProjectedCompiler.v` 选择 `shared_normal_realization`，复用 freshness／执行运输和公共 `projected_realized_rule_region_contract`；direct 安装也调用该定理。`compile_shared_projected_correct` 继续连接完整 Csem→Asm backward simulation。

`ClightSharedLoadedRectangleCompiler.v` 只是将原 `choose_loaded_rectangle`／`loaded_nested_supported` 实例化到这个编译适配层，并提供两个私有 slots。没有重新证明矩形调度、别名稳定性或条件合成。

## 验证与复现

完整接口现审计 251 个端点，无新增全局公理；语言无关 49 个闭合端点、Clight 59 个端点的基线保持。十七种配置全部重建／回归通过，二十六份原生报告绑定当前审计。相对 `19a0cd1` 的二十五份已有源码／生成 Clight 摘要均相同。

共享入口通过同一份 fixture 的 6,248 次 C 调用／6,253 行输出，与 GCC 和独立模型一致。七处实际 region 的候选／回退均各一份；sequential 函数有两处 region，故共两份。Boolean slot 与 cache 分别声明、分派实际读取该 Boolean，未初始化内层尺寸的空路径和改变 bound 的回退行为保持。

单 region 函数 `loaded_rectangle` 的打印 Clight body 从 332,491 字节减至 61,039 字节；候选份数从 156 降至 1。这是生成文本和语法计数，不是运行性能测量。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-shared-loaded-rectangle-native
```

提取入口是 `ClightSharedLoadedRectangleCompiler.compile_shared_loaded_rectangles`。原 `interface-loaded-rectangle-native` 和统一 pass 保留直接树出口，便于核对相同条件／相同输入与生成表示的区别。

共享出口避免完整循环体的叶复制，但检查树本身仍会展开重复的后续检查。它不是完整 DAG／CFG 检查生成器，也未取消选择器的规模预算。两个 memory-bound 维度、参数 stride 的同次组合、复杂 body 和 affine／tiling 主接口迁移仍待完成；尚无性能结论。
