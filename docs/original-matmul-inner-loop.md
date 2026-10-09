# 原 matmul：I64 内层循环与实际 PolCert Loop

本阶段把同一原 matmul 的完整 k 循环接到 typed PolCert Loop，包括实际
Clight 的零初始化、重复读取 K、`loop + break`、混合 I64/I32 increment，
以及公开 k 出口。**这是内层循环对应，不是已安装的 matmul 优化。**
原 corpus 的 requested optimized case 数仍为零。

重新 fetch 核对 narrative `8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9`；
main 的 [paper narrative](topdown/paper-narrative.md) 与远端一致。按其责任
边界推进原计算的证明，kernel／既有 whole-program host 均不变。

## 实际源与证明链

复用[原 typed bridge](original-matmul-typed-bridge.md)冻结的完整 exported
Clight，而非重写一个相似的整数 fixture。新 `OriginalMatmulInnerLoop`
从真实 `f_main` 的 selected region 取出 k 循环，并以 Rocq reflexivity
证明它就是下面的 Clight 模板：

```c
for (k = 0; k < K; k++)
  C[i+2][j+2] = beta*C[i+2][j+2]
               + (alpha*A[i+2][k+2])*B[k+2][j+2];
```

运算树、global double arrays、I64 iterator 和 I32 literals 都保留。
新链为：

```text
实际 selected initialized k loop
       ↕ 有限执行、入口前提下
counted_iterations（原 matmul 的真实 memory actions）
       ↕ 仿射 cells 的真实 registry 解释
DoubleAssignmentLoop.loop_semantics（完整 k Loop）
```

两方向保留最终 CompCert memory。公开 temps 精确为
`PTree.set k (Vlong (Int64.repr upper)) entry_temps`；i、j 和其他 temps
保持。`upper=0` 时也涵盖原初始化／break，出口 k 是零。该 Loop model 的
环境为 `[j;i;M;N;K]`，k 插入后用 `[k;j;i;M;N;K]` 解释原 body 的三个
仿射坐标。M／N 在此只是 model 环境的参数位置，没有在新 k 证明中执行
额外读取。

本阶段限制 K 为非负、有界的 signed I64 值，并要求 padding 后的坐标落在
原 100×100 arrays 内。负 K 的零次迭代、外层 i／j 与条件读取仍待接入。
双向有限执行定理消费一侧已有执行；它没有增加总 progress、所有入口的
termination 或 divergence 结论。

## 三层责任与接口

| 层／模块 | 作者提供什么 | 已提供的证明 |
| --- | --- | --- |
| Generic kernel | 既有 guard／conditional correctness certificates | 无改动；局部 guarded composition 的边界不变 |
| Language：`GuardMemoryLongLoopControl` | 实际 header test，body 的 normal exit 与当前 iterator frame | 原 `Sloop` 的 stop／step encode 与 decode；精确 I64 increment |
| Language：`GuardMemoryLongLoopIterations` | header、body／increment invariant、normal 与当前 iterator frame | 实际有限 loop ↔ `counted_iterations`；迭代状态保留全部 temps 与 memory，适合内层循环改变其自己的计数器 |
| Language：`GuardMemoryDoubleHeaderFrame` | global bindings、写入与被观察 globals 不同、实际 store | 不同 globals 的 blocks 分离；C store 保持 K 的 Mint64 load；实际 global I64 expression 与 load 的对应 |
| Optimizer/domain：`GuardMemoryDoubleMatmulLoops` | static globals/span/padding、入口 i/j/K 状态及范围 | 每个到达 k 值自动建立旧 assignment entry；原 initialized inner loop ↔ physical iterations，并精确刻画 k 出口 |
| Optimizer/domain：`GuardMemoryDoubleMatmulLoopModel` | 同一 static／layout／坐标事实 | 真实 memory actions ↔ typed PolCert body／完整 inner Loop；registry interpretation 不依赖程序 temps |
| Concrete site：`OriginalMatmulInnerLoop` | 从实际 selected source 取出的节点及适用入口事实 | 节点精确匹配；原节点的双向 typed Loop 对应；固定 identifiers 的差异在证明中 discharge |

这些是语言实例和 transformation 作者的证明接口。最终标注 C 的用户仍只应
给源码标注与策略选项。当前未安装 factory，表中的适用入口前提不是要交给
C 用户补的 callbacks，也不是已自动生成的 guard。

## 前提来源与最难的剩余链

`double_matmul_static` 分出 globals、不被 locals shadow、padding literal 与
地址 span 等静态事实；它不包含 temps、内存读结果或原语句执行。
Inner invariant 保持 i／j 的当前值和 K 的入口 load。每次 body 前，k 的
I64 word 和数学计数范围推出旧 `double_matmul_entry`，所以不再逐次另行
假设 assignment entry。当前 iterator 无回绕来自 `0≤k≤K≤Int64.max_signed`。

K 的稳定性已有 producer：原 body 只写 C，其 global block 与 K 的 global
block 不同，`Mem.load_store_other` 保持 header load。这个结论没有许可一次
新的读取。**入口 K 的 load 成功和充分范围仍是显式逻辑前提**，未来必须由
安全 capture／guard、静态 metadata 和 source/site producer discharge。
Body 的实际 reads 则沿用原 assignment decode，从原执行恢复，不在运行时
先执行 source，也不新增提前 body preload。

这属于 narrative 的 `C_opt` source/model bridge 和一部分 `C_derive`
（循环 invariant 推出局部义务）。它没有交付新的 `C_guard` 或 `C_host`
安装。尤其不能因内层定理显式含 K load，就在外层为空时读取本来不会读取的
N／K；安全的条件观察顺序仍是 M，只有外层活动才观察 N，只有中层活动才
观察 K。最终还要生产候选入口、恢复公开 i／j／k 出口，并连接 continuation。

下一实现继续同一原程序的外层两级／完整 nest与部分状态入口 producer，再接
实际 double scheduling／tiling／codegen、candidate lowering、安全 guard
和 selected Csem→Asm。浮点动作仍保持每个 expression tree；调度不能改变
同一 C cell 的 k 依赖。所有 62 原案例、原 BT 及其他适用顺序路线继续保留。

## 审计与复现

五个新模块共 700 行，独立查询 27 个端点，其中四个 closed；单端点最多
使用六个 inherited globals，无新增公理。跟随 212 reachable sources，
连同父 checkpoints、实际 AST、helper 与全部尝试，共绑定 7,082 个文件。
六次成功和 23 次拒绝保留，成功 `.v`／`.vo` 和旧 helpers 未覆盖。

Proof checkpoint：`build/original-matmul/loop-proof-v1/report.json`，SHA-256
`7e4a29874ee0af89005e613e897af1c96d3d0933f575e67d51ea30240266951c`。
实际 AST inner-loop checkpoint：
`build/original-matmul/source-loop-v1/report.json`，SHA-256
`a96edefb578c7a2df9b116c83a47939bcce48af172a8861da188d7b609a11794`。
机器摘要见[original-matmul-inner-loop.json](original-matmul-inner-loop.json)。
`build/` 的 proof objects／完整源／logs 不随 Git 提交。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/compile_matmul_loop_sources.py MODULE --attempt NAME
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/prove_original_matmul_inner_loop.py --attempt NAME
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_original_matmul_loops.py --validate
python3 scripts/summarize_original_matmul_loops.py --validate
```

首建时先建立旧 typed checkpoint，然后按表中的依赖顺序编译五模块，生成
actual AST proof，最后不带 `--validate` 建立 audit 与 summary。已成功目录
保持冻结。编译／审计只说明上述 proof 范围；本阶段没有新的 extracted
compiler、native 接受／回退、优化速度或成本结果。
