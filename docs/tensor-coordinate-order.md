# 相同证明服务处理两种地址坐标次序

此阶段扩展不受信任的源描述／候选策略，复用已经验收的
[tensor region compiler](tensor-region-compiler.md)。没有新增或修改 Rocq 定义、
定理、kernel、语言 host 或 candidate checker。旧 proof、native 与 cost reports
保持；新 compiler 和 artifacts 使用独立的 `build/tensor-affine-region`。

## 使用者交付的数据

实际源的循环次序不变，改用如下地址表达式：

```c
for (; i < n; i++)
  for (j = 0; j < columns; j++)
    for (k = 0; k < components; k++)
      a[((j * ld) + i) * 5 + k] = a[((j * ld) + i) * 5 + k] + alpha;
```

在这一源中，`j` 是物理地址的较高坐标，`i` 是较低坐标。策略提出 dimensions
`[columns,ld,5]`、write/read coordinates `[j,i,k]` 和 scalars `[ld,alpha]`；模型
parameter layout 仍是 source iterators `[i,j,k]` 后接 scalars。九字段描述器与
candidate/witness 是数据，没有增加 SOURCE、BOX、binding、exit 或 context 语义
callback。Profile 和寻找候选仍由策略决定。

Factory 重新核对实际 Horner AST／RMW RHS、source shape、标识符空间、参数用值
和 dimension 的读取许可；它不会因为策略称这是一种坐标次序就接受。首 extent
选择已经属于原 bound 的 `columns`，不是任意额外输入。Full guard producer
按原 source-definedness 建立安全读取和模型输入，再将 affine box 条件编译为
实际检查。这一布局的充分坐标条件为 `n <= ld`；另一种 `[i,j,k]` 布局使用
`columns <= ld`。仍有 positive counts、cap、layout volume、profile 等其他条件。
这些是 checker 使用的充分事实，不是变换正确性的必要条件。

同一候选策略提出交换前两层的 Loop AST 和 swap witness。Operation 自身保留
原坐标表达式，checker 检查域、依赖和对应。原循环和 candidate 的真实执行、
word32 RMW、公开 iterator 恢复、kernel local certificate 与 program installation
均复用原证据。`compile_tensor_regions_correct` 对 describe/propose 参数通用，
不需要信任或另证这一 OCaml 策略。扩展新的 source grammar／效果则仍可能需要
新的对应证明；此例没有越过已证明的 parametric-coordinate 接口。

策略同时保留旧的 `((i*ld)+j)*5+k` 地址匹配。两种源分别执行单个 region、连续
两个 region、带 goto／外围数组写的完整函数。Source AST fallback 保持，两个
单 region 函数的空 outer 输入实际传 null pointer。Context 中仍使用有效数组，
因为外围语句本身会读写它。

## 原生验收

七种配置各执行72个完整调用，共504次 CompCert assembly calls。每次核对全部
6,144个 word、公开 `i/j/k`、第一个 region 的出口及 pre/post／memory markers。
输入包括正常接受、坐标覆盖失败、越过第三维、非零 root、empty outer／inner、
profile 拒绝、word32 溢出、跨两个 region 和 goto 绕过 region。

Identity、interchange 和2×3 tile 各安装8个 source sites。独立216-call Clight
插桩矩阵每种配置观察28次 fast 和66次 refusal；这是打印 Clight 的分派观察，
不是生产汇编上的路径探针。错误 reindex、零 tile 和故意调换的坐标 metadata
全部静态拒绝，六个函数没有安装 site，完整源输出仍相同。错误坐标模式在
factory 前提不成立时被拒绝，即使该模式还准备了一条 identity 候选。

| Column-traversal 函数 | Source bytes | Identity | Interchange | Tile2×3 |
| --- | ---: | ---: | ---: | ---: |
| 单 region | 218 | 630 | 629 | 878 |
| 连续两 region | 347 | 1,155 | 1,155 | 1,636 |
| goto／memory context | 317 | 704 | 706 | 940 |

旧 row-traversal 函数的相应 bytes 与前一阶段相同。大小和执行次数不证明收益。
本阶段未增加作者工时或其他 verified framework 的比较实验。

Native report `build/tensor-affine-region/native/report.json` SHA256：
`6b4fc69ebfefcc4b4437c300225c8bd21c5adb8c60f927391561ef5cde032c05`。
复用 proof report SHA256：
`640d768bbbe74f456e04c7bfbbf848f994fbcaa6c4018c31ecc82a32feb4e4e3`。
新 builder 绑定原 proof sources／objects、原 entrypoint、新 native policy、driver、
extraction 和 compiler。Native validator 再核对这些绑定、实际 AST、sites、完整
结果和 dispatch 记录。运行矩阵支持此处接口使用的结论；普遍正确性来自原定理。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_affine_region.mk compiler
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_affine_region.mk native
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_tensor_affine_region.py --validate
```

同一 column-traversal 单函数的[独立成本实验](tensor-coordinate-cost.md)已完成
30轮／960批次，采用明确的stride<2048 profile；大stride输入获得交换净收益，
小输入仍更慢。所有时间、检查工作和原生正确性证据分别记录。

## 继续的功能边界

这仍是三层 temporary-bound rectangular nest、一个 tensor、单个 RMW leaf。
实际坐标次序的扩展没有交付 literal-bound transport、loaded-header 与动态 layout
的组合、跨 tensor alias、多 statement body 或 nonrectangular affine domains。
[OLO 对照](olo-tensor-comparison.md)中的这些缺口保持。后继优先交付 literal bound
的实际源运输，再组合 loaded bounds／动态布局；最终目标继续 active。

下一接入可复用 `ClightConstantBoundModel.constant_loop_preinitialized_model`：
原 `<5` 在 fresh helper 已等于 `Vint(Int.repr 5)` 的状态下，能够运输为 temp-bound
loop，保持实际 memory／公开出口。Tensor adapter 还须完成以下具体组合，当前
没有把它们计作已实现：

- 从语言分配的 pool 保留一个 typed int32 helper，检查它不属于原 source scope／
  live／其他 private resources；实际初始化不能是假定入口已定义。
- 用实际 raw source execution 和 public temp frame 生产 prepared state 上的
  canonical source-definedness，再消费原 tensor factory／guard／candidate 证据。
- 目标保留原 AST fallback；helper 初始化和 canonical proof entry 的状态变化需
  有 projected contract，不能将两个不同的 entry 当作相等。
- 改用已有 `ClightExpressionRegionHost` 的 source-progress／安装接口：当前
  `apply_memory_tiled_table` 的 temp-bound structured progress classifier 会拒绝
  literal 子循环。既有语言 host 不需要重证，但新 compiler glue 必须实际调用它。

因此，此扩展的主要证明工作是 source 与 prepared-model 入口、guard exit、原 AST
回退之间的运输。常量赋值和 Boolean dispatch 本身不能关闭这些义务。
