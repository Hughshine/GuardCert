# Double 分块后重排：表示证明、真实编译和 narrative 责任

2026-10-09。重新 fetch 后，可见 narrative 仍为 `8ce9c8b`；两份 topdown
正文已与 main 一致。本后继落实其逐配置整程序交付要求：真实 Pluto 自动调度、
tiling、intra-tile scheduling，经阶段验证、prepared codegen、最终候选检查、
actual Clight lowering 和 Csem→Asm。使用者给标注 C 和策略数据，不手写候选或
逐 site 提交语义 callback。

[固定摘要](double-reindexed-tiling.json)验证 11 reports、13,704 bindings，SHA256
`455ed39d796f3e8055cd1b16c4c669413942c5cde6be26035e9b9e795b1dadac`。
[证明摘要](double-reindexed-tiling-proof.json)绑定五个后继模块、492 行、10 端点、
498 reachable sources；1 closed，最大 42 inherited globals，无新增公理。

## 实际行为与边界

| 原案例 | 安装 | 实际阶段效果 |
| --- | --- | --- |
| mvt | 两处 | 两处都分块；第二处 tile 内点顺序由 i/j 改为 j/i |
| matmul-seq | 两处 | 分块后 tile 内点顺序由 i/j/k 改为 i/k/j |

真实命令去掉 `--identity`，启用 `--intratileopt` 和 `--tile`。这四处的
初始 affine schedule 仍是 identity；改变顺序发生在 tiling 后。摘要逐项核对
实际 scattering，不把调用自动调度器等同于其初始阶段产生非恒等结果。

10 项原输入／unmarked／外部拒绝／错见证／malformed 检查和 14 项 context
全部通过并匹配 GCC。多个 marked 安装四处、调用四次；相同 unmarked 邻居
保留。公开 i/j 在正数时为 `(96,96)`，零和负数时为 `(0,23)`。
三次 unchanged assembly 调试观测：正数／零 `[accept,refuse]=[2,0]`，负数
`[0,2]`。这些是实际路径观测，不是检查成本计数或完整状态等价的独立证明。

这不是新 compiler 的完整 62-case replay，也不扩大原 affine 的 8/62 非恒等
计数。无受控成本／收益结论。新路线的 unit tile、一般 affine completion 和
更复杂 permutation 尚未验收；此前 unit 验收属于旧 producer/build。

## 验证责任与最难的连接

Kernel 的局部证书接口和 language host 定律不改。Domain 的新责任是把
实际候选 Loop 的坐标表示对齐 tiling witness，而不改变其执行顺序或指令。
`checked_double_reindexed_tiling_loops` 对提议的有限 adjacent swaps 重新编号
提取后的表示，检查完整域／指令／访问／变换字段及双向依赖验证。
`validated_double_reindexed_tiling_loops_at` 复用已有
`memory_reindexed_execution` 坐标同构和 constructive tiling progress，得到
**同一组实际参数**下 source Loop → actual candidate Loop 的 forward 执行。
它不能用 raw codegen 的 backward theorem 或某组存在参数的执行代替。

新的 factory 内部生产 actual source/model、充分界限、安全 capture、private
frame、public exits 和 region guarantee；语言 host 核对当前 program 的
scope、placement、resources 与 source progress。最后端点为
`DoubleReindexedTiledChoicesCompiler.compile_selected_tiled_choices_program_correct`，
证明原 Csem→Asm backward simulation。后续 affine/source pass 消费新的
intermediate program，并重新核对其适用证据。

具体复用发生在坐标同构、capture/source 服务、candidate lowering、出口恢复和
scoped installation。此路线的局部 guarded execution 证明直接展开 Clight
分支；不能把 kernel 未改或被 import 计作直接调用 `guardify_preservation`。
论文的复用论证需要指出实际消费的定理及消除的义务，端点数本身不证明贡献。

## 保留的失败和修复

Native v1 在改变点顺序的候选上最终拒绝。增加已证明的 reindexing checker
后，v2 仍拒绝：实际 driver 的旧策略在 `tile` 模式只提议空见证。v3 的
data-only inspection 记录这个事实；其重建 source 仅用于诊断，不作为
source execution 证书。v4 使用有限不受信任搜索，默认六轴、可配置上限 32；
每项仍由 checker 验收。没有因为诊断结果放宽检查或引入语义公理。
这些失败、第一次 Rocq import／binder 错误及相应输入快照均保留并绑定。

构建与复核：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/build_double_tiled_witness_compiler.py --attempt new-name
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/summarize_double_reindexed_tiling.py --validate
```

已构建 `build/affine-double-tiling/compiler-attempts/native-v4/ccomp`。后续继续
完整 corpus、initialized／multiple-bound／loaded source、一般 affine/skew、
ISS／其他顺序 phases、原 BT／LLVM／SPEC 与 larger tiers。条件尺寸、runtime
work、接受域和完整调用成本分别验收；本阶段不算完整 goal 完成。
