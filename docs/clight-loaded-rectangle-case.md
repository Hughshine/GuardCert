# 动态内存上界与矩形循环交换

本例扩展固定 2×2 的组合：行数从普通内存 load 得到，列数是运行时临时变量，数组布局和 stride 是静态的。源每次外层头部读取 bound；接受后候选用新鲜私有 temp 缓存 bound，真正交换两层循环。主线验收参照 [Optimistic Loop Optimization 账本](optimistic-loop-acceptance.md)。

## 源、候选和检查

实际 C fixture 的源是：

```c
int cells[12];
for (; i < *rows; ++i)
  for (j = 0; j < columns; ++j)
    cells[i*4+j] = i*1+j+(-1);
```

使用者规则的接受性质是：`i=0`、`0<*rows≤3`、`0<columns≤4`，以及每个活动 `cells+i*4+j` 的地址都不同于 rows。条件是实际只读 Clight decision tree；生成器先检查入口范围，再嵌套调用语言无关 `synthesize_prefix_scan`，外层扫描行，内层扫描活动列。

检查成功时执行：

```c
cache = *rows;
for (j = 0; j < columns; ++j)
  for (i = 0; i < cache; ++i)
    cells[i*4+j] = i*1+j+(-1);
```

任何检查失败都执行原循环。`columns` 只在 `i=0` 且外层活动时读取；外层为空时，源未初始化的 columns 不会被新条件提前读取。源自己的头部仍要求 rows 可读；本例没有将 null bound 的源未定义路径变成安全路径。

本例支持的 shape 可以更换 extent、stride、coefficient、bias；实际 AST 必须核对到该 shape。RHS 按 CompCert 机器数据语义处理。控制和地址的范围另由布局条件及 `rectangle_point_bound`、实际 `Int`／`Ptrofs` 对应证明建立，不能把数据回绕与控制范围混为一谈。

## 检查为什么可以先执行

不能预设所有入口访问地址都有效。如果 rows 指向第一行，源写入它之后可能提前退出，因此后面行的访问权限不能从入口尺寸直接假定。

外层 ghost invariant 保存原入口和一段真实源的剩余执行，还保存当前 bound load 与入口值相同、当前权限能够运输到入口。当前行有完整的实际内层执行，因为内层 columns 是不被 body 改变的 temp。`loaded_rectangle_row_decode` 因而在不预设 non-alias 的情况下解码这一行的真实 stores，建立这一行比较地址的有定义依据。

内层扫描只比较当前行的活动 word。整行比较接受后，non-alias 的 store/load 保持性证明 bound 未变；真实源 tail 因此提供下一行 invariant。外层扫描再进入下一行。检查过程中实际内存和 temps 一直是原入口；ghost 前缀只出现在证明中，不在运行时执行源 stores。

例如入口 bound=8、columns=3、rows 指向 cells[0]：源第一行把 bound 写成 -1，正常退出，第二行没有访问依据。入口范围检查先拒绝，保留该行为。即使入口 bound 在范围内，某个当前行的活动 alias 比较失败，也会在建立下一行依据之前回退。

## 使用者需要交付什么

| 内容 | 本实例提供的证据 |
| --- | --- |
| source／candidate／位置 | 使用者 selector 和已核对 AST；框架不寻找矩形 |
| 入口域 D | 实际源头部求值得到 iterator、可读 bound，加 quiet source completion |
| 条件编码 | 范围探针和实际指针比较的求值可靠性；两层活动分类器及逐点证书 |
| 局部 effect | 源仅写 row／column temps，实际 stores 提供权限与 bound 保持性 |
| 接受后的局部对应 | 私有快照、活动头部运输、既有 `rectangle_local` 调度与实际 memory 对应 |
| 公开出口 | 所有原程序 temps、内存、事件与正常出口保持，cache 被 freshness／scope 证明隐藏 |
| 上下文 | `readonly_projected_forward_loop_rule` 复用源完成性和候选确定性，再接 projected context adapter |
| 独立源进展 | `loaded_nested_supported_sound` 只保护 outer iterator，不假定 bound 稳定 |

入口／扫描证书最终是同一个 `readonly_condition`；局部证明最终是同一个 projected rule。框架的状态、整数和内存语义均由 Clight 实例交付。多次替换仍由单次正确性和 pass 组合证明连接。

## 源码和复现

新增模块位于 `prototype/interface/ClightLoadedRectangle{Row,Memory,Atoms,InnerScan,Prefix,Guard,Loop,Forward,Compiler}.v`。`loaded_rectangle_generated_condition` 证明实际固定代码生成宿主的语法可以用于每个真实函数宿主；提取入口实际调用两层通用扫描生成器。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-loaded-rectangle-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-common-native
```

独立完整端点是 `ClightLoadedRectangleCompiler.compile_loaded_rectangles_correct`，结论为 `Csem.semantics` 到 `Asm.semantics` 的 backward simulation。统一 pass 在固定 2×2 规则之后尝试这个规则，保留已有模板的选择优先级。

## 边界和验证状态

完整编译接口现审计 242 个端点，没有超过既有分层假设基线；语言无关接口 49 个端点闭合，Clight 适配层 59 个端点不超过既有六项基线。十六种编译配置已全部重建／回归通过；相对 `e37e458` 的 23 份已有源码／生成 Clight 摘要均相同。

独立／统一入口各通过 6,248 次实际 C 调用和 6,253 行输出，逐个公开 iterator、bound 和十二个 cells 与 GCC／独立模型一致。6,222 次网格调用中，576 次入口满足逻辑接受条件，其中 504 次是同对象非活动单元；另有 402 次活动别名位于后续行、492 次改变 bound、18 次增大 bound。这些是独立模型的输入分类，不是运行时分支计数。18 个源未定义的网格候选被排除。

附加调用覆盖 bound=8／INT_MAX 但首行写入后合法退出、signed 极值空循环、负列数和超过 stride 但实际源访问仍合法的回退、空外层的未初始化 columns、两次 rewrite 间修改尺寸。七处实际 guard 和列优先候选均从生成 Clight 核对；四类不支持／超预算模板保持源。无限外围只编译和检查，未运行。

示例 pass 将静态 extent 和成功叶预算分别限制到 256。两层短路树会复制后续代码；设 `k=stride+1`、`n=extent/stride`，成功叶包括提前停止的路径，数量为 `1+k+…+k^n`，使用 `2*k^n-1` 作保守预算。超出预算保留源。这个条件是使用者的代码规模策略，局部定理和通用扫描本身没有这个限制。它不是廉价、无界的区间 guard，也没有性能结论。

实际 12／4 shape 的每处 region 展开 156 份候选（两处 sequential region 共 312 份）。因此运行正确性已经验证，但代码大小尚不适合一般大循环；后续需要有证明的共享出口或更廉价的足迹检查。

当前组合只覆盖普通 bound load、运行时行数／列数、静态 stride 和 affine 纯写 body。参数 stride、两个从内存读取的维度、多个依赖 preload、读写更新／复杂依赖和旧 affine／tiling 的主接口迁移仍待接入。有限选中片段可以位于无限外围上下文中；本例不改写潜在发散的整段选中循环。
