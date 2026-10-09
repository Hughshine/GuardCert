# 原 matmul：double 局部执行与 PolCert 模型的接入

2026-10-08，继续 narrative `8ce9c8b` 的原计算验收方向。本阶段完成原 matmul
赋值的局部双向桥，并实例化 typed PolCert 验证与代码生成。**尚未安装完整
matmul 优化**；原 corpus 的 requested optimized case 数保持零。

## 实际输入与已完成链

使用[首轮原案例](original-benchmark-first-attempt.md)固定的 `matmul/marked.c`，
没有改成整数数据、缩小维度或更换计算。重新构建的 CompCert `clightgen`
从同一 C 输入产生完整 Clight 程序，经过 `SimplExpr`／`SimplLocals`，不加
exporter 的额外 `-normalize` pass。短 identifier 编号是导出配置；parser
仍在既有 trusted frontend 边界。Rocq adapter 仅改 import namespaces，
所有导出的程序定义保持原样。

原区域使用 I64 计数器、32 位常量、100×100 全局 double arrays、padding 2
和 double scalars，保留运算树：

```c
C[i+2][j+2] = beta*C[i+2][j+2]
             + (alpha*A[i+2][k+2])*B[k+2][j+2];
```

本阶段的证明链是：

```text
同一原 C → 实际完整 Clight AST
              └ selected region／三层循环／assignment 精确模板匹配
                  └ actual assignment execution ↔ memory action
                      ↔ DoubleAssignmentInstr.instr_semantics
                      ↔ DoubleAssignmentLoop.loop_semantics（单个 body）
```

Rocq 直接执行 RHS decoder 并证明其输出是预期的 double expression，
不仅证明模板的 parser roundtrip。原三个公开 iterator 的 I64 类型也精确核对。
`OriginalMatmulBody` 的两条执行定理作用于从真实 `f_main` 选出的 assignment，
消费下面列出的局部入口事实。整段 selected region 的 AST 相等不等于已经
证明三层循环的执行对应。

## 模块、接口与证明方向

| 新实现 | 输入／提供的事实 | 已证明的结果 |
| --- | --- | --- |
| `GuardMemoryObservationDeterminism` | 固定 ge／locals／temps／memory 下两次 expression 或 lvalue 执行 | 值、block／offset／bitfield 相同；只读观察确定性 |
| `GuardMemoryDoubleSource` | typed operand receipts、实际 source expression、decoder／emitter 一致 | 实际 expression→model；与既有 model→Clight 合成双向 expression 对应 |
| `GuardMemoryDoubleLocations` | global binding、I64 坐标执行、维度及地址 span | 原两层数组 lvalue 对应 `Mfloat64` 的八字节行优先地址；global registry 非 alias |
| `GuardMemoryDoubleAssignment` | 只含地址的 read／write receipts、实际 assignment 执行或模型动作 | source→真实 loads／IEEE compute／store，及反向 lowered execution；trace／temps／normal exit 精确 |
| `GuardMemoryLongControl` | I64 operand／temp、I32 literal 的 signed 范围；比较另需 I64 signed 范围 | mixed-width addition、零初始化、增量与 `<` 的点级机器执行对应 |
| `GuardMemoryDoubleMatmul` | site identifiers／extent／padding、globals／temps／坐标边界 | 自动构造五个 read receipts 和一个 write receipt；原 matmul body 的双向 memory-action 对应 |
| `GuardMemoryDoubleMatmulInstr` | 同一入口事实及 layout lookup 证书 | 仿射 accesses→真实 locations；原 body↔PolCert `INSTR`／单 body `Loop` |
| `GuardMemoryDoublePolyhedral` | 具体 double `INSTR` 与不受信任 model／candidate 数据 | 实例化 affine／tiling validators、ExtractorCorrect、PrepareCodegen；固定参数的双向模型验证及 checked affine codegen backward endpoint |

`DoubleAssignmentInstr` 是 `MEMORY_VALUE_CODE` 的闭合实例。计算只能访问
显式 loaded operands；内存交换证明复用既有 arbitrary-chunk footprint
定理。它不允许浮点结合律、FMA 替换或改变每次赋值的运算树。调度仍须
保留同一 C cell 沿 k 方向的依赖，独立 i／j 动作才可能交换。

严格 assignment 实例修正了一个重要语义边界：`Mem.load Mfloat64` 可以返回
`Vundef`，但 `sem_cast double→double` 不能把它变成成功的赋值结果。因此
`compute_double_assignment` 仅接受实际 `Vfloat` 输出。旧 raw expression
实例保持冻结；新模型与 source assignment 的成功路径一致。

## 前提来源与责任

`double_matmul_entry` 不是待生成的 guard，也不是已经完成的 factory API。
它现在是局部证明的显式逻辑入口，刻意不包含成功 load 或语句执行作为字段。

| 局部前提 | 本阶段如何使用／产生 | 完整安装所需 producer |
| --- | --- | --- |
| globals 不被 locals shadow，symbol 指向相应 blocks | 构造实际 `eval_Evar_global`；不同 global identifiers 的 blocks 由 Genv 单射分离 | source／scope／global metadata checker 与语言实例；尚未接 factory |
| layout lookup 与原数组类型、extent 对应 | checked 数学 registry 按维度解析 cells；实际 lvalue 使用原 nested-array 类型 | AST／global-declaration producer；当前用显式 layout certificate |
| i／j／k temps 是相应 I64 words | mixed I64/I32 expression 定理生成实际 `i+2` 等地址输入 | 三层 source loop invariant、capture／transport、候选入口；完整 nest 尚缺 |
| shifted coordinates 在维度内，八字节 span 不回绕 | 给出 raw Mem.load/store 与 loadv/storev 的一致性；row-major index 有界 | 静态维度事实＋运行时充分范围条件；没有新 emitted Mfloat64 guard |
| padding 的 I32 signed 范围 | 保留原 I32 literal→I64 的转换；本例 literal 2 | syntax／constant checker；点级证明已完成 |
| 实际 RHS reads 成功 | 从原 assignment execution 恢复精确 read list 及 loaded values；地址 receipts 不提前假设 loads | source execution 是语义证明起点；未来 guard 不得在运行时先执行原 assignment |
| IEEE 结果及 store 成功 | source cast／assign_loc 反演得到；反方向由严格 model action 生产 | 候选／source 对应定理，不能由 address permission 单独推出 |
| 参数长度／nonalias／模型验证 | concrete `INSTR` 复用；global registry 非 alias 定理可提供模型前提 | typed source model producer 与实际 pipeline／candidate checker |

这里的 global registry 只证明 cell separation。它不自动证明 memory permission、
lifetime 或 loaded-value definedness。当前点级 addition 保持 modular I64
运算；将 signed machine `<` 解释成数学 `<` 需要 signed 范围，完整循环
无回绕和公开终值仍须另证。不能把“点表达式已对应”写成“已支持 I64 循环”。

Kernel 与既有 whole-program host 均没有改变。语言实例新增 concrete IEEE、
观察、地址和 I64 执行事实；optimizer/domain 新增原赋值与仿射访问模型。
最难位置仍是 source loop 许可的部分状态到 safe guard/capture，再到实际
候选入口与公开出口。最终源码用户只应提供标注与策略选项；本阶段的显式
entry/layout 前提必须由后续 site producer 自动生产，不能交给 C 用户补证。

Typed checker／codegen 的证明范围也单独标注。双向 validator 定理只作用于
固定参数的模型。`checked_double_schedule_codegen_correct` 是 generated
Loop→source model 的 backward 端点；它不证明 generated-loop progress 或
实际 Clight candidate lowering。新实例的 external scheduler、OpenScop
export 和 native double compiler 路径还未安装，不能算一次真实调度调用。

## 独立审计与未完成项

八个新模块共 1,181 行；独立查询 40 个端点，其中 10 个 closed，单端点
最多使用 12 个 inherited globals，没有新增公理。审计跟随 159 个 reachable
sources，连同原 source AST、frontend、父 compiler／proof checkpoints、helper
与 rejected attempts 共绑定 6,990 个文件。父 baseline 仍为原 42 globals。
AST namespace 拒绝及所有 proof 拒绝保留，不覆盖成功源／`.vo`。

检查点：`build/original-matmul/proof-v1/report.json`，SHA-256
`ae8628ac41fdd4c76843df2969f1be9691fbf7fcc27fbed39915cf86cc0f854a`。
机器可读摘要见[original-matmul-typed-bridge.json](original-matmul-typed-bridge.json)。
`build/` 中的完整源／object／log／binary 不随 Git 提交。

原 exporter 和 parent compiler 的 pretty-printed Clight 全程序文件不逐字相等：
打印接口及 identifier 配置不同，parent 输出还经过既有 compiler 路径。
本阶段绑定同一 C、实际 exporter 调用和完整 exported AST 的精确 source
模板证明；没有宣称 exported program 就是 parent binary 内部 AST 的字节快照。
两者都使用 `SimplExpr`／`SimplLocals`，与 selected compiler 的输入层一致。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python scripts/export_original_matmul_ast.py
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python scripts/compile_matmul_typed_sources.py MODULE --attempt NAME
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python scripts/prove_original_matmul_ast.py
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python scripts/audit_original_matmul_typed.py --validate
```

Export、compile、AST proof 和 audit 的成功目录保持冻结；完整首次重建时依次
编译上述八模块，再生成 AST proof，最后不带 `--validate` 运行 audit。不要
在已有成功目录重复这些创建命令。

下一实现继续同一原 matmul：完整 I64 nest→Loop 的 source correspondence；
条件读取 M／N／K 和 globals metadata 的 producer；真实 typed scheduling／
tiling／codegen、candidate lowering；安全 guard、公开 i／j／k exit 恢复、
selected factory 与 Csem→Asm；最后实际 native 接受／回退与完整成本。
这些缺口仍需关闭，不能把本阶段的局部编译和类型实例化当成原 benchmark
优化验收通过。全部 62 cases／原 BT／其他顺序路线与源取得目标继续保留。
