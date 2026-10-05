# 用路径事实简化只读条件

同一个运行时条件可能在多个阶段重复读取、比较同一个表达式。前缀扫描的直接展开还会复制后续测试。`ReadonlyProbeTree.v` 提供语言无关的简化器：保留第一次测试，将其实际 Boolean 结果作为该路径的事实，后续相同测试直接进入对应分支。动态内存上界矩形编译器已消费该接口，原条件编码和局部调度证明直接复用。

## 语言需要提供什么

`readonly_probe_semantics S Probe` 把探针当作不透明 key，提供关系 `probe_test key entry answer` 及同一 key、同一入口状态上的结果确定性。关系允许未定义：框架不要求每个探针在任意状态都可执行。

语言再提供 key 的可判定相等，以及 `readonly_probe_compiler H L`：纯检查树的执行与宿主检查精确对应，检查不改变入口；树的可达安全性与宿主检查安全性对应。整数、指针、load、volatile 和内存权限均由语言解释。不能用这个接口自动消除有副作用或可能给出不同结果的读取。

在 Clight 实例中，key 是实际 `expr`，相等是语法相等，解释是已有 `expression_test`。所有测试读取同一个入口状态；语言适配层证明执行／安全对应。真正的 volatile 操作不能直接作为这种探针。普通 load 的定义性仍来自原条件的证书和真实源前缀。

## 规则作者怎样使用

先提交原来的 `readonly_condition H D P tree`，包括安全、可用、完全状态不变和接受蕴含 P。调用 `simplified_probe_condition` 得到同一 D、同一 P 的新证书；候选和条件性局部证明均保持。Clight 的 `simplified_projected_rule rule` 直接完成这项适配，再交给已有共享出口编译器。

```text
Test p
  (Test q
    (Test p yes no)       // 在这里已有 p=true
    reject)
  reject

        ↓

Test p
  (Test q yes reject)
  reject
```

事实只由已经执行的测试建立。如果 p 为 false，不会触及只在 p 为 true 时有定义的 q。拒绝整个 guard 仍不等于逻辑上证明 ¬P；这里保存的是具体探针结果，不是 arbitrary Prop 的否定。相同 key 的比较也不推导不同表达式之间的算术关系。

路径事实是在编译时遍历树的参数，不是插入运行时缓存或执行 ghost 源循环。简化后的逻辑检查仍只读。共享出口适配另外在最终叶保存新鲜的 private Boolean，其实际写入仍由原 freshness／scope 证明处理。

## 框架证明什么

- `simplified_probe_tree_run`：事实有实际测试证据时，原树和新树给出相同 Boolean 结果，两个方向都成立。
- `simplified_probe_tree_safe`：原树在入口安全时，新树也安全；只需要可达分支的定义性。
- `simplified_probe_condition`：将上述结果连接原条件证书，保持域、接受性质、只读性和可用性。
- `ClightProbeTree.v`：提供实际表达式／决策树的执行与安全桥，并保留原 projected rule 的 candidate、premise、局部证明和入口证明。
- `compile_simplified_rectangles_correct` 和 `compile_simplified_dual_rectangles_correct`：分别实例化单 loaded 和双动态 loaded 矩形的共享编译宿主，连接完整 Csem→Asm backward simulation。

## 实际验证

`make interface-simplified-rectangle-native` 构建实际提取入口 `ClightSimplifiedRectangleCompiler.compile_simplified_rectangles`。它使用原动态内存上界矩形的源、候选、条件和 fixture，随后执行通用简化和共享出口适配。

6,248 次 C 调用／6,253 行输出与 GCC 和独立的逐头部 load 模型一致。七处实际 region 都有唯一候选／源回退；重复的 `0 < *rows` 已删除。上界被 alias store 改写、同对象非活动单元、signed 极值、空外层时未初始化内层参数，以及顺序多次改写均保持原行为。

同一单 region 函数的打印 Clight body 为：

| 生成方式 | body 字节数 | 语法中的 if 数量 | 候选份数 |
| --- | ---: | ---: | ---: |
| 原直接树 | 332,491 | 854 | 156 |
| 共享出口 | 61,039 | 289 | 1 |
| 共享出口加探针简化 | 6,584 | 45 | 1 |

这是此 fixture 的静态文本／语法计数，没有运行时间测量、普遍体积定理或新颖性结论。它仍是树，不是一般共享 DAG。

本阶段语言无关接口 54 个闭合端点，Clight 59 个端点，完整编译接口 259 个端点审计无新增全局公理。十八种配置全部重建回归通过，二十七份原生报告绑定当前审计；相对 `2ca0524` 的二十六份已有源码／Clight 摘要全部相同。报告位于 `build/interface-simplified-rectangle-native/report.json`。

这个实例推进条件生成后的已验证简化，不扩大优化模板或接受域。双动态内存维度的静态矩形与单 loaded 的参数 stride 组合已有后续实例；双 loaded 与参数 stride、多个依赖 preload、廉价一般 alias／仿射检查和旧 affine／tiling 迁移仍待完成，见 [主线验收账本](optimistic-loop-acceptance.md)。

双动态 memory-bound 矩形也已消费同一个后处理接口，无需重做原有的局部调度或条件编码证明。`make interface-simplified-dual-rectangle-native` 通过相同 113,330 次调用；主函数 body 129,224→14,234 字节、语法 if 413→69、alias 位置 248→40。当前 366 个完整编译端点、850 份源码摘要审计无新增全局公理；24 种配置回归和 37 份原生报告通过，36 份旧 source／Clight 摘要相对 `7f8f725` 相同。详细原条件、源前缀义务和保留的树展开限制见 [双动态矩形使用者](clight-dual-dynamic-rectangle-case.md)。
