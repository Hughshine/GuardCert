# 内存上界与运行时 stride 的同次循环交换

这个实例处理真实源 `cells[i*stride+j]`：外层头部每次读取 `*rows`，列数和 stride 是运行时 temps。接受后候选缓存 rows，交换 i／j 两层，并继续使用参数 stride 计算地址。使用者规则通过主只读接口、共享出口宿主和 CompCert 完整 Csem→Asm 定理。

```c
for (; i < *rows; ++i)
  for (j = 0; j < columns; ++j)
    cells[i*stride+j] = i*1+j+(-1);
```

## 条件表达力与规模限制

当前使用者选择器只接收固定数组 extent≤12 的模板，枚举 stride=1…extent 的布局并核对每个布局证书。框架不限制布局数；这是此原生 pass 的编译规模预算。语言实例证明枚举包含每个合法正布局，不是只支持某个预选 stride 常量。

入口 guard 先测试 i=0、`*rows>0`、columns>0，然后读取 stride 并分派到匹配布局 k。该布局检查 `*rows≤extent/k`、columns≤k，以及所有活动 word 地址与 rows 不同。条件的数值含义为：

```text
i=0 ∧ N>0 ∧ 0<M≤stride ∧ stride>0 ∧ N*stride≤extent
```

乘积是接受性质中的数学表达式。实际检查使用已经选中布局的常量除法界，运行时没有 signed32 的 N*stride 检查；`loaded_stride_product_bound` 证明两种界在正 stride 下等价。源／候选实际地址的机器语义对应继续消费原矩形证明。

参数 stride≤0、重叠行、超布局或 alias 输入回退。源码固定 extent 超过 12、步长 2、volatile bound、循环内修改 stride 等模板保留为源。源在非活动路径允许未初始化 columns／stride，条件不能提早读取它们。

简化后的 guard 节点另限制为 4096。现阶段生成器会先展开布局检查树再简化，编译时仍可能有大量中间节点；这不是廉价的一般动态布局分析或性能成果。

## 使用者提交的证明

`ClightLoadedStrideTransport.v` 从实际源的活动外层／内层路径得到 columns 和 stride 的定义性。第一次真实 store 提供 stride 的整数值；没有要求进入 guard 前完整 footprint 稳定或可写。

stride temp 不被循环修改。语言实例证明在它等于 k 时，源完整执行可以保持 trace、memory 和所有 temps 地运输到 k 的常量模型。这个运输只替换地址里的 temp 与常量；源 `*rows` 仍每轮重新 load，尚未假定 bound 稳定。

`ClightLoadedStrideGuard.v` 因此能复用每个模型原有的只读前缀证书。当前行的实际源 stores 先提供地址比较依据；non-alias 通过后才保持 rows 并推进下一行。接受性质显式包含被选中的合法模型和它的 alias／范围证据。

`ClightLoadedStrideForward.v` 复用模型的局部交换／快照证明，再将候选的常量地址运输回使用参数 stride 的真实代码。公开出口、全部原 temps、完整内存和事件保持；cache 的 freshness／scope 仍由规则与宿主交付。

`ClightLoadedStrideCompiler.v` 核对实际 AST、模型布局、变量区别和 private cache，应用已验证的探针简化，再实例化共享宿主。最终只有一份参数 stride 候选与一份真实源回退，布局分派不复制完整循环。统一选择器也消费同一个局部规则，但仍使用其原直接树出口。

这些模块是 Clight 使用者实例。语言无关核仍只认识条件、局部执行／观察及上下文契约，不解释 stride、alias 或 CompCert 内存。

## 验证记录

独立编译入口和统一 pass 各通过 68,368 次有定义的 C 调用／68,373 行输出，与 GCC 和独立的逐头部 rows 模型一致。逐单元、行列出口和 bound 最终值均核对；七个函数有八处实际 guarded region，四个不支持模板保留为源。

网格里 4,248 次调用符合接受条件的独立 oracle，包含 3,792 次同对象非活动单元；所有 stride 1…12 都有接受输入。另有 3,204 次后续行活动 alias、96 次 bound 增长、1,374 次重叠布局回退和 3,480 次超布局但源有定义的回退。统计是输入／语义模型分类，尚无实际分支计数或运行性能测量。

空外层时 columns／stride 未初始化、空内层时 stride 未初始化、两次 rewrite 间 stride=3→6，以及 INT_MAX bound 被首行 alias 写入后提前退出均在运行 fixture 中。明确无限的外围 context 只编译和检查，源未定义输入不执行。

完整接口 279 个端点通过全量 Rocq 编译／假设审计，保持既有分层基线，没有新增全局公理；纯接口 54 个闭合端点、Clight 59 个端点保持。十九种配置完成重建／回归，二十九份原生报告核对当前编译器／证明摘要；相对 `7798e4b`，二十七份已有源码／生成 Clight 摘要全部相同。原生结构检查曾因打印指针语法及深层换行导致脚本拒绝，修正为精确语法的空白无关比较后定向重跑两入口通过；运行结果比较始终相同。

独立共享入口的单 region 函数打印 body 为 71,693 字节、候选一份；统一直接树入口为 395,143 字节、候选 127 份。两者使用相同简化条件和局部证明，这是静态文本／语法比较，不是运行时间测量。

复现入口为 `make interface-loaded-stride-native`；统一 pass 使用 `python3 scripts/native_interface_loaded_stride.py --common`。它补上有界固定数组的参数 stride／内存上界组合，仍缺大布局／一般指针缓冲区、两个 memory-bound 维度、多个依赖 preload、复杂 body 和旧 affine／tiling 迁移，见 [验收账本](optimistic-loop-acceptance.md)。
