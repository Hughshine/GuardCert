# Loaded bounds 与动态 Horner 地址：原源许可的首点检查

本阶段补齐原 loaded-bound 循环、私有 capture 和首个动态地址检查的执行连接。
它尚未交付完整 nested scan、cached-source execution 或新的 loaded tensor compiler。
完整程序入口仍是上一阶段的 [literal-bound tensor compiler](tensor-literal-bound.md)。

目标源包含下面的控制与地址模式；两种坐标次序都需要后续完整接线。

```c
for (i = 0; i < grid[0] + 1; i++)
  for (j = 0; j < grid[1] + 1; j++)
    for (k = 0; k < 5; k++)
      a[((i * ld) + j) * 5 + k] += alpha;
```

`grid` 可以与 `a` alias，`ld` 是实际运行时参数。先前 affine leaf 服务只允许
常量乘积，不能为 `i*ld` 提供原源权限证明。因此本轮没有将 `ld` 改回固定 stride，
也没有用“地址在数学 tensor 范围内”代替实际 memory permission。

## 首点为什么可以检查

新 `word_arithmetic` 限定 typed signed int32 的 constant、temp、加、减、乘，
包括变量乘变量。`word_arithmetic_check_sound` 证明语法检查的 soundness。
`word_replacement_evaluation` 从原表达式实际成功求值运输机器词结果，允许将
已知坐标替换为 word literal、保留其他 temp，且不依赖目标 memory。
它不声称数学值不溢出。Clight 的 `pure_scalar` 包含 pointer comparison，后者
依赖 memory；因此不能仅凭 pure 就跨 memory 运输求值。

实际原 store 的 receipt 提供地址与 `Mem.storev Mint32`。前缀服务持有原源
到当前 memory 的 `memory_accesses_back`；它将该地址的权限运输到 guard-entry
memory。地址对齐与有效性据此取得。两个 header observer 的读取 receipt 则给出
其实际地址、raw word、对齐和权限。运行时生成的是实际 pointer-cell 不等比较，
没有源码级 block ID primitive，也不要求数组 base 与 header base 不同。

接受结果先证明实际写地址与每个已读取 header cell 分离，再用 store/load 定律
证明 raw observation 保持。拒绝表示未知。它不证明 no-wrap，也不证明候选
重排正确；后继完整条件还须独立取得这些模型义务。

## 从原循环生产输入，而非让使用者假设输入

`tensor_header_capture_execution` 从原 loaded-bound source 的 silent normal
completion 生产实际私有 capture 执行、保持同一 final memory 的 prepared source
执行和公开出口 frame。child header 只在原 outer comparison 活跃时捕获。
`None` 分支不添加 child 读取许可；`Some word` 分支生产实际 observer receipts。
缓存的 `raw+delta` word 与被保持的 raw memory observation 仍是不同对象。

`tensor_header_original_first_point` 在 root、child、literal 均活跃时，从原循环
取得实际首个 leaf 执行。`j`、`k` 的 reset 发生在原路径上；guard 用零 literal
替换三个坐标，因此不读取原入口中未初始化的 child counters。其他参数的定义性
由实际 leaf 求值取得，包括 `ld`。不先假定整个缓存循环已经执行。

`tensor_header_capture_point_ready` 将这两项串到同一次执行：原源 → capture →
prepared 原源 → observer receipts → 首点 domain → 实际 Clight check statement。
此 theorem 的调用者提供语法／资源条件和原源执行，不提供新的 alias-stability、
word-definedness 或 source/model 语义 callback。物理 receipt 字段不进入生成代码；
`direct_word_observer_tree_addresses` 只依赖 observer address AST，允许用固定
template 生成检查。

## 接口与三方责任

| 责任方 | 本阶段的输入或服务 | 当前边界 |
| --- | --- | --- |
| Framework | 既有 `readonly_condition`，safety、availability、acceptance soundness 与 local guarded preservation 接口 | 最小 kernel 未修改；本阶段尚未安装新的整体 rewrite |
| Clight 语言库 | typed word grammar／checker、实际求值运输、store receipt／permission transport、pointer-cell 比较与 observation 保持、tree 到 check statement 的执行 | 只支持列出的 int32 算术；actual statement 写 Boolean temp，公开 frame 仍需 fresh flag |
| Optimizer/domain 库 | loaded／indexed header shape、literal 第三层、私有 capture／公开 frame、原源首点 producer 与同入口组合 theorem | 只生产首点；尚无该 family 的完整 source-to-cached producer 或新 data factory |
| Site 策略 | 原／目标片段、header／坐标／private 名称及候选数据 | 后续 checker 需自动查验 exact AST、grammar、freshness、profile、progress 与 namespace |

Domain 库与 site 策略均归优化实现者；表中分列复用库与具体使用者，不增加第四个
证明责任方。现有 fixed-affine site checker 不能接受 `i*ld`；它没有被修改来假装
已有完整 factory。本阶段 theorem 的静态 proof 参数仍需由后继 data checker 生产。

按 narrative 的逻辑分解，`C_derive` 当前生产安全捕获与首点许可；`C_guard` 生产
该点的实际检查、state identity／私有 Boolean 写入和接受后的保持。`C_opt` 的
完整 cached model／candidate-state 连接、`C_host` 的实际安装仍未为 loaded tensor
组合交付。它们不是四份新增 caller callback。

## 证据与限制

五个新 Rocq 模块通过40端点／445依赖的独立审计，其中15端点闭合；其余端点
最多使用既有 CompCert baseline 中的6项全局假设，无新增公理，kernel 仍闭合。
报告 SHA256 为 `ab7fb8352ec476d156f9a975153e65f4c1014d8c1190ea752b42d2911c5921ec`。
独立审计绑定源码、对象、toolchain、旧 literal-bound 报告及每个查询的公理集合；
复用旧报告仅核对冻结依赖，不将旧208端点或旧 native 调用算作本阶段新增证据。

`ClightTensorHeaderPointExample` 构造真实64-byte allocation，初始化两个 header
和 data word，证明 actual RMW、separation check、两个 raw observation 保持。
其中 `((2*MAX)+3)*5+4` 在机器词语义下为9，原 store 地址为 byte52；这证明
bootstrap check 不需要先消费数学 no-wrap。完整 tensor guard 仍需另证其 no-wrap
要求。另一个实际 alias-refusal Clight statement 跳过依赖缺失 temp99 的后续
测试；这是一次拒绝路径的证明，不声称 unvisited test 的 totality。

提取原型仅执行 syntax checker、coordinate replacement、observer-tree 和 capture
AST construction；它不运行生成的 Clight。实际 statement/memory 的证据来自
Rocq 定理。八项提取运行通过，覆盖动态乘积、load／division／wrong type拒绝、
只替换坐标并保留stride、双observer tree、check lowering与条件式child capture。
提取报告 SHA256 为 `0510fef0c31cf1dd98cba1b2c07cc17cff2a5e64618a4627f7621310ee096e30`。
本阶段没有新的 C／Asm matrix、安装入口、性能或作者工时测量。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_header_point.mk proof
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_header_point.mk extracted
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_header_point.mk validate
```

下一步必须将每次接受后的 observation 保持接到实际第三层／child／outer source
prefix，逐点生产许可，拒绝即停止未来检查。完整接受之后才能导出 cached source，
再连接动态 tensor guard、候选入口和公开退出，最后安装到完整 Csem→Asm 并验证
同一实际 C 的接受／回退／上下文和成本。不能把首点 theorem 推广称全域许可。
