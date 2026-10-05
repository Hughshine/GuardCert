# 运行时 stride 的 guarded 循环交换

本例使用新只读接口处理实际二维 Clight store 循环。`n`、`m`、`stride` 都来自运行时；数组长度和数据表达式的系数由静态语法证书核对。它对应 [Optimistic Loop Optimization](https://compilers.cs.uni-saarland.de/papers/doerfert_cgo17.pdf) 的维度界、线性化及检查自身算术安全需求，但只实例化一种二维纯写模板。

## 用户提交什么

源片段与候选片段分别为：

```c
/* source */
for (; i < n; ++i)
  for (j = 0; j < m; ++j)
    a[i * stride + j] = i * 7 + j + 1;

/* candidate */
j = 0;
for (; j < m; ++j) {
  i = 0;
  for (; i < n; ++i)
    a[i * stride + j] = i * 7 + j + 1;
}
```

选择器属于使用者 pass；框架不负责发现循环或决定交换有利。此实例的提议器解析前端循环、实际下标和 RHS；独立的 `check_stride_description` 核对完整源 AST、body、内层初始化、增量、类型、数组长度和变量不相交约束。仅匹配一个乘法或一个 store 不足以取得证书。

运行时检查来自 `stride_dimensions_primitives` 的已认证原子，并通过现有 Boolean 条件树合成器生成：

```c
i == 0 && 0 < n && 0 < m && 0 < stride && m <= stride
       && (long long)n * (long long)stride <= extent
```

guard 成立则执行候选，否则执行原片段。真正输出的源／候选地址都保留 `i * stride + j`；编译器没有枚举 stride，也没有将它替换为源码常数。条件是充分条件：例如 `n=1, stride=INT_MAX, m=3` 的源地址仍合法，但此 guard 保守拒绝。

## 条件为何可读、可算、可靠

使用者证明分为入口读取域与优化前提。`runtime_stride_domain_from_source` 从实际源执行取得外层计数器和 bound；只有 `i=0` 且 `n>0` 才要求内层 bound 是整数，只有两维都活动才要求 stride 是整数。后一个事实来自第一次实际地址求值，而不是假设该参数总已初始化。因此，`n=0` 时即使 `m` 和 stride 未初始化也不读取它们；`m=0` 时也不读取 stride。

生成条件按这个顺序短路。`stride_dimensions_run` 给出实际 Clight 检查执行；`stride_dimensions_sound` 证明检查接受蕴含数学前提；`stride_dimensions_condition` 将执行、安全、只读及可靠性封装为通用 `readonly_condition`。它直接作用于实际入口，不执行片段或扫描全部动态迭代。

检查中的乘法也需要证明。`stride_wide_product_exact` 证明两个正 signed32 值转换到 signed64 后，其实际 `Int64.mul` 的 signed 值精确等于整数乘积。最大乘积为 `2147483647²`，小于 signed64 最大值。数组长度由静态证书限制为正且不超过 signed32 最大值。故检查不会因自身回绕错误接受；循环的机器地址与数学地址则由后续执行对应另外证明。

接受时，`m <= stride` 给出每行有效宽度；`n*stride <= extent` 给出整个矩形的范围。两者结合正数要求，导出原内存调度实例所需的 `n <= extent/stride`、地址单射、signed 下标范围和 `Ptrofs` 字节范围。维度界与访问权限分开：候选 store 的定义性由实际源 store 执行和认证的重排证明获得，不由数组大小代替权限证明。

## 局部证明如何复用

`runtime_stride_index_constant`／`runtime_stride_store_constant` 是证明里的执行对应：在 stride temp 保持入口值时，真实变量地址与以这个值实例化的数学布局有相同求值和 store。这个布局是 ghost，未生成到候选中。

`strict_loop_body_transport` 提供一般循环 body 运输；使用者提交 body 执行对应和 body／增量保持的不变式。此实例用写界证明 stride 不被 body、内层重置或两个计数器增量修改，再将上述 store 对应逐次提升到实际嵌套循环。`runtime_stride_rectangle_forward` 随后消费已有实际内存重排证明，并把结果接回保留变量 stride 的候选执行。观察包括完整 memory、所有原 temps、trace 和 outcome。

`stride_forward` 是使用者提交的局部单向执行定理。`readonly_forward_loop_rule` 补上源完成性和候选确定性所需的反方向，得到条件性局部等价，再封装成 `readonly_clight_rule`。源完成性的 ghost 来自实际源执行；该二维模板的有限源进展由现有结构化循环宿主证明。

## 如何嵌回完整程序

`compile_runtime_strides` 将使用者选择器交给通用只读编译适配器。`compile_runtime_strides_correct` 的端点是：

```text
compile_runtime_strides p = OK target
  -> backward_simulation (Csem.semantics p) (Asm.semantics target)
```

它支持多个被选片段和外围 goto／循环。每次检查使用该片段的当前入口，因此前一片段后修改 stride 不会沿用旧检查。无限外围循环可被编译；这不意味着被选片段本身可以是潜在发散的 `!=` 循环。

统一 pass `ClightCommonRewriteCompiler` 也消费这条规则，通过保持生成代码相同的精确规则嵌入接到保护原 temps 的公共观察宿主。它与私有 load 快照、已有矩形和单元交换共用一个完整程序入口。

## 验证及边界

证明模块和 102 个编译接口端点的假设审计已通过，没有新增全局公理。可重现入口是 `make interface-runtime-stride-native`。提取后的独立编译器通过 345 次函数调用／342 行输出，其中参数网格有 330 次调用、108 个输入满足 guard；九处实际 guarded 区域已确认。统一用户 pass 也在同一个 fixture 上通过相同检查，可用 `python3 scripts/native_interface_runtime_stride.py --common` 复现。

fixture 包括运行时参数网格、重叠行回退、零／负 stride、signed 极值的合法源回退、全部数组单元和公开 iterator 出口、空路径未初始化参数、连续两处改写以及外围上下文。重叠行实例的源／无 guard 交换结果确实不同；生成 guard 保留源行为。独立 Python 模型只用作原生结果对照；正确性端点来自实际 Rocq／CompCert 证明。报告保存在 `build/interface-runtime-stride-native/report.json` 和 `build/interface-common-stride-native/report.json`，绑定同一证明报告、源码、编译器、Clight 和汇编摘要。

当前只处理普通 signed32 数组上的二维纯写 RHS 模板。参数 stride 的 RMW／行内依赖、内存载入的二维边界、一般指针访问区间及多维 tiling 的新接口迁移仍待组合。既有实际内存相等证明继承 CompCert 的 proof irrelevance；本例未新增语言语义公理，也没有性能测量。
