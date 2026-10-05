# 两个动态内存上界下的矩形循环交换

这个实例接受不同的运行时 rows／columns，两个值都来自普通 memory load。它消费现有的只读条件、嵌套前缀扫描、局部观察和完整程序宿主。语言无关核没有加入整数或内存语义。

## 使用者提交的变换

例如一个十二单元数组、静态 stride=4：

```c
for (; i < *rows; ++i)
  for (j = 0; j < *columns; ++j)
    cells[i*4+j] = i*10+j+1;
```

候选缓存两个独立的参数值，再交换循环：

```c
cached_rows = *rows;
cached_columns = *columns;
for (j = 0; j < cached_columns; ++j)
  for (i = 0; i < cached_rows; ++i)
    cells[i*4+j] = i*10+j+1;
```

使用者提供 source、candidate、位置与规则证书。这里附带的选择器先提出数组 extent、stride、payload 系数和循环描述，再核对原始 source AST、完整 typed store、两个实际 loaded 头、单位自增、内层归零及标识隔离。识别和遍历属于示例 pass；框架没有规定所有使用者必须使用这个识别器。

接受性质 P 包括 `i=0`、`0<*rows≤extent/stride`、`0<*columns≤stride`，以及每个活动单元的地址与两个 bound 指针都分离。检查先核对入口 counter、外层范围，之后才读取内层上界。接着两层短路扫描只检查活动的行／列：每点依次比较该地址与 rows、columns。两个 bound 可以共享同一只读单元，也可以位于同一数组的非活动单元中。

例如 `rows=2,columns=3` 时，源地址序列是 `[0,1,2,4,5,6]`，候选为 `[0,4,1,5,2,6]`，出口都是 `i=2,j=3`。这已不要求两个 bound 相等或固定为 2。

## 局部证明义务

入口域 D 来自实际源的正常完成执行。源进展由 `ClightMixedLoadedProgress` 单独提供，signed 单位增量的 rank 不依赖两个 memory bounds 稳定。完成见证和源执行游标只用于证明，提取后的 guard 不执行或模拟源循环。

[ClightDualRectanglePrefix.v](../prototype/interface/ClightDualRectanglePrefix.v) 解码实际行入口、当前一个 store、内层退出和外层 continuation。它不先假定整行迭代数固定：第一笔写入可能改变 columns；任何一行也可能改变 rows。

[ClightDualRectangleCursor.v](../prototype/interface/ClightDualRectangleCursor.v) 保存当前实际状态、两个读取、入口到当前的权限运输和两层剩余执行。当前 store 先提供写权限，两个实际 load 提供读权限，随后才能证明入口中的指针比较有定义。两项 non-alias 都通过后，才运输两个读取到下一点。

[内层扫描](../prototype/interface/ClightDualRectangleInnerScan.v) 把“最后一个活动点通过后可以建立下一行游标”纳入该点的接受性质。它消费真实内层退出、外层增量和 tail。[外层扫描](../prototype/interface/ClightDualRectangleOuterScan.v) 消费整行证书，复用同一个语言无关 `synthesize_prefix_scan`。活动性分类器分别提供 true／false 证据；inactive 的后续区域不需要地址权限。

[条件合成](../prototype/interface/ClightDualRectangleGuard.v) 连接入口范围与两个扫描。证书证明实际 guard 安全、可完成、状态不变，以及接受蕴含 P；拒绝不等于否定 P。[语法运输](../prototype/interface/ClightDualRectangleSynthesis.v) 保证运行时树不依赖证明采用的函数入口语义或观察关系。

[ClightDualRectangleLoop.v](../prototype/interface/ClightDualRectangleLoop.v) 在 P 下同时运输两个 loaded 头到缓存头。每次实际 store 分别保持两个 load，活动 body invariant 与包含终止 counter 的头部 invariant 分开。[局部 forward 证明](../prototype/interface/ClightDualRectangleForward.v) 随后消费既有实际 CompCert store 调度交换，保留完整内存、事件、控制出口和所有原程序 temps。

两个缓存必须分别与源／continuation 的标识隔离，并彼此不同。freshness、源 temp 写界和实际执行运输把新增 temp 隐藏于公开观察；源完成性与候选确定性补足局部观察等价的另一方向。这些义务不能由“循环只改变数组”一句话代替。

## 完整程序接口

[ClightDualRectangleCompiler.v](../prototype/interface/ClightDualRectangleCompiler.v) 的 `dual_rectangle_rule` 返回已有的 `readonly_projected_clight_rule`。语言提供检查分派、实际局部执行和框架所需的上下文定律；共享宿主安装 guard／candidate／原片段回退，并证明 continuation 运输。

`compile_dual_rectangles` 调用 `compile_shared_projected`，预留三个私有整数：两个缓存和共享分派的 Boolean。每处实际 candidate／fallback 各出现一次。抽象 condition 仍只读；Boolean 的实际写入由宿主的 private frame 证明处理。

`compile_dual_rectangles_correct` 的结果为完整 `Csem.semantics p` 到 `Asm.semantics target` 的 backward simulation。同一函数中的多处 rewrite 每次使用自己的实际入口与检查证据。当前综合入口预留一个候选 cache，因此本例先通过独立入口接入；综合入口尚未消费这条双缓存规则。

## 复现与当前边界

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-dual-rectangle-native
```

选择器将静态 extent 限为 12；局部定理和条件生成证明没有这个额外 cap，要求布局本身满足 signed32／Ptrofs 的表示界。检查规模随静态布局展开，不是廉价无界区间检查。当前 body 为一个经过完整语法核对的 affine signed32 store；没有覆盖任意多语句、复杂读写依赖、参数 stride 的同次双 loaded 组合或多个依赖 preload。

实际提取编译器通过 113,330 次 C 调用／113,330 行输出，七个函数中八处实际 guarded region；结果与 GCC、GCC UBSan（无诊断）和独立逐头读取模型一致。十二单元／stride=4 的全部 12 个正矩形尺寸都进入输入分类的接受集合，六单元／stride=3 另覆盖六个正矩形与空域。fixture 同时核对完整数组和两个 counter，包含 goto、外围循环、空外层的 null／未初始化内层指针、两次改写间改变两个参数，以及 signed 极值的合法回退。明确无限的外围函数只编译／检查。

113,280 次有效网格调用中，模型分类 6,516 次入口接受，1,692 次共享 bound 接受；111,996 次 alias 调用包含 1,836 次外层值变化和 1,572 次内层值变化。43,968 个候选网格调用因源越界或超出有限测试预算而未执行；额外 50 次调用覆盖上述边界及另一个布局。这些是输入／模型分类，没有实际分支计数或性能测量。

原共享入口阶段全量审计通过 364 个编译接口端点、849 份当前证明源码摘要；FRAGMENT=6、MEMORY=1、REGION=6、PROJECTED_REGION=8、STEPWISE=8、COMPILER=35 的既有基线外没有新增全局公理。23 种提取配置全部重建／回归通过，36 份原生报告绑定当前产物；相对 `83295d2`，35 份已有 source／Clight 摘要相同。结构检查最初误设了后续行探针只出现一次，修正为实际树的复制次数后通过；所有运行结果在修正前已一致。

共享出口没有共享检查树的 continuation。布局 12／4 的主函数打印体为 129,224 字节，包含 413 个语法 `if` 和 248 个 alias 比较位置；每条运行路径只检查当前活动点，但后续行的语法被前行的多个成功叶复制。生成 Clight 的结构断言明确核对这些次数，以及两个独立 cache 和各一份候选／回退。下面的已验证简化减少重复测试；一般共享检查图仍未接入，不能将语义正确性当作优化收益的证据。

## 保留原证书的条件简化

[ClightSimplifiedDualRectangleCompiler.v](../prototype/interface/ClightSimplifiedDualRectangleCompiler.v) 的选择器把同一 `dual_rectangle_rule` 交给 `simplified_projected_rule`。语言无关 [部分探针接口](readonly-probe-simplification.md) 用同一入口中已执行的实际 Boolean 结果简化后续相同表达式；新的只读证书保留 D、P、candidate 和局部证明。该入口仍预留三个私有整数，并有自己的完整 Csem→Asm 定理。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-simplified-dual-rectangle-native
```

同一 source／fixture 的 113,330 次调用与 GCC、无诊断 UBSan、逐头部模型一致，八处 region 保留各一份候选和回退、两个独立 cache。布局 12／4 的主函数打印结果为：

| 检查生成方式 | body 字节 | 语法 if | alias 比较位置 |
| --- | ---: | ---: | ---: |
| 共享出口 | 129,224 | 413 | 248 |
| 共享出口及探针简化 | 14,234 | 69 | 40 |

这是静态生成结果。简化没有推导不同表达式的算术关系，也没有生成一般共享 DAG；部分后续检查的 continuation 仍复制。原共享入口保留可复现，接受范围、extent≤12 和一般布局等限制保持。当前完整审计为 366 个端点、850 份证明源码摘要，24 种配置回归和 37 份原生报告绑定当前产物；相对 `7f8f725` 的 36 份既有 source／Clight 摘要相同，没有新增全局公理。
