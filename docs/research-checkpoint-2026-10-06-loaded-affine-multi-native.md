# Deep affine＋loaded bound：真实 C 与提取编译器

2026-10-06。接续 [候选与完整编译证明](research-checkpoint-2026-10-06-loaded-affine-multi.md)。
当前声明范围的 C 输入、真实检查、非空候选／原源回退和 CompCert backend 已连通。
再次 fetch `topdown/research-positioning` 仍是 `226ba94`，main narrative 正文一致。
这是一项阶段结果；紧凑条件、成本与同例人工工作尚未完成，完整目标保持 active。

## 实际入口与资源修复

[提取脚本](../scripts/build_loaded_affine_multi.py)使用已经证明的
`ClightGuardedLoadedAffineMultiCompiler.compile_loaded_affine_multi_regions`。
运行入口为 `build/loaded-affine-multi/compiler/ccomp`；CompCert v3.18、Rocq／Stdlib 9.2。
[不受信任 frontend](../prototype/affine-nest/native/GuardLoadedAffineCandidate.ml)从真实
`i<*limit` AST 提出 private cache、旧 affine metadata 和候选；实际 source key、模型、条件、
候选和 code lowering 仍逐项由已证明 checker 核对。metadata 用 cached header 描述模型，
不会把原 source AST 替换为 cached key。

首轮提取时所有合法候选也被静态拒绝。原因是完整整数 private pool 包含 captured cache，
而 backend 要求所有 candidate counter resources 与受保护 inputs 分离。
[factory 修复](../prototype/interface/ClightLoadedAffineMultiFactory.v)保留整个 pool 的类型／
allocation 检查，仅从 candidate counter pairs 过滤包含 cache 的 pair。旧 disjointness checker、
候选执行证明和语言 host 继续使用；没有绕过保护条件。frontend 的结果 flag 预留在两份完整
scan controls 之后，单 pointer 和多 pointer 都不占用 scan 的受保护 slots。

当前 driver 分配 32 个 private integer slots。提案失败、validator 不接受或 oracle 资源不足，
均保留原源。oracle 仍为 bounded Fourier–Motzkin＋checked LCF certificate；沿用旧 42 项假设，
没有新全局公理或新 kernel 字段。

## 完整 C 中观察到的行为

[C fixture](../examples/native_loaded_affine_multi.c)包括：

- 两／三层根为 `i<*limit`、child 为 `j<i+m`、grandchild 为 `k<j+p` 的参数化源。
- 真正读改写、三个数组的读写、常量 store 和存在真实依赖的 chain。
- 同一函数中的两段原循环，各自独立 guard／候选／回退。
- 条件初始化的 private source 参数，空路径上不可读；null body pointer 的零／非活动迭代。
- 独立 bound、同 block 未写 word、同 block 分离 slices、相同／部分重叠 body pointers。
- body 将 bound 写成 1，分别在第一 row 和第二 row 提前停止。
- 只有两 word 的合法源：初始 bound=3，第二次写入将 bound 改为 1；guard 不得比较第三 word。

独立 Python word 模型逐次更新真实 bound、每个数组 word 和所有公开 control 出口。
GCC `-O0 -fwrapv` 参考与模型相同；六种生成配置均与它们一致。数据加法回绕按 word 语义核对，
control 范围失败保留原程序。signed wrap 的合法 source case 与编译器优化前提分开，
不以 GCC 参考代替 CompCert 定理。

| 配置 | 静态安装／实际结果 | 新完整 C 调用 |
| --- | --- | --- |
| disabled | 全部保留原源，对照 | 104 |
| interchange | 安全递归／多数组候选安装；真实 chain 依赖拒绝 | 104 |
| tile-2-3 | 安全源安装 2×3 tiling | 104 |
| wrong-reindex | 错误变换拒绝 | 104 |
| invalid-domain | 缺失源域候选拒绝 | 104 |
| resource-limit | FM rows=0，保守拒绝 | 104 |

共 **624 次**新 assembly 调用。每次核对完整 A/B/C 数组、公开 i/j/k/K/L 和最终 bound，
没有只比较 checksum。真正 chain 依赖另有模型反例：交换会改变最终数据，因此其静态拒绝
不是一个可任意放宽的 frontend 限制。旧 native 矩阵没有重跑，也不累计到本次结果。

两套独立 GCC 编译的 emitted-Clight 插桩各运行 104 次，共 **208 次**，每处 fast/fallback
计数及最终结果均符合期望。每套观察到 41 次 fast、62 次 fallback 分派；无安装的 chain 不计
分派，同函数两次 rewrite 可贡献两次。该固定 fixture 结果不算 benchmark 接受率。

另有 **21 个未修改汇编的 GDB 探针**核对实际 stores、值、公开出口和 bound：

| 路径 | 三个 watched offsets 的实际写序 |
| --- | --- |
| 原源 | 48、128、256 |
| interchange | 128、256、48 |
| tile-2-3 | 128、48、256 |

三轴、多数组和两次 rewrite 均观察到对应候选顺序。同 block 分离 slices 走候选；相同／
部分重叠 body pointers 走原序。bound 首 row 被改写后只执行第一 row；第二 row 被改写后
公开 i=2。短数组探针直接观察 pointer-comparison instruction，只比较 offsets 0、1，
没有比较未来未获许可的 offset 2。Clight 插桩不计作机器路径证明。

GDB 在 Codex 受限 sandbox 中无法启动 inferior；同一未修改 binary 在授权的本地调试环境中
通过全部探针。模型／普通 native calls 在 sandbox 中已通过；这是工具执行权限差异，非语义回退。

## 证明、绑定与复现

资源修复后独立审计仍通过 **32 端点／692 递归依赖／1,021 源摘要**。
新 compiler 与旧 deep／当前 cursor regression 均保持原 42 项假设；kernel composition 闭合。
scan、旧 materialized 和当前 cursor 的 source/object bindings 保持。
前一报告 `build/loaded-affine-multi/proof/report.json` 原样保存；当前只有 factory source 与它
不同，该报告不再声称绑定当前 factory／其消费者对象。新证明报告单独记录这一变化。

| 产物 | SHA-256 |
| --- | --- |
| `build/loaded-affine-multi-native/proof/report.json` | `bad5c8b43b4997abf35901145ca21d819ebc8ca3fd58227331c029dda3094ce1` |
| `build/loaded-affine-multi/compiler/.guard-build.json` | `e792af7782abd49a43931f91dc568697e339bb4b75dcf53e2df4605f97043868` |
| `build/loaded-affine-multi/native/report.json` | `3c4a107e11a92c2c0a99b771d0f63c3d8d85c25c32e0481d728147cf58ff7285` |
| `build/loaded-affine-multi/native/path-report.json` | `0743a70c865f6d5f47ef9bba2d52d0e0464ca68081ec41a205bfe9c15d8ec631` |

[validator](../scripts/validate_loaded_affine_multi.py)复核当前 proof sources/objects、build stamp、
提取 driver/native modules、compiler、C source、六配置 Clight／assembly／binary／完整输出，
并在 `--paths` 下核对路径 helper、命令、日志、branch binary 和原机器程序摘要。
本轮全部通过；旧冻结报告不重写。

已有继承证明基线和 toolchain 下的复现命令：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make loaded-affine-multi-native
make loaded-affine-multi-validate
```

`loaded-affine-multi-proof` 现指向新的 resource audit；旧 audit 脚本和历史报告保留。
各 report hashes 属于此次产物，不承诺在不同工具链重新构建时保持相同字节。

## 下一项：紧凑条件与可用性

当前仍是 canonical recursive children＋单个 loaded root；多观察 dependent header 的深层组合、
typed pointer stores、非 canonical 控制、一般动态 stride 和其它 source domains 仍有功能差距。
域证明覆盖任意有限 canonical depth，本轮 native 验收的深度是二／三层。
局部 contract 仍是原 source 的有限正常完成；整程序进展／控制由语言 host 提供，
不会据此宣称任意局部 divergence equivalence。

本次 linked 函数大小可独立核对，例如三轴 accumulator：原源 236 bytes，interchange 896，
tile-2-3 1,016；多数组为 270／2,061／2,156。它们包含 guard、候选与 fallback，
不是 guard 单独大小，更不是运行成本。cursor 形式没有消除逐点稳定性／alias 扫描；未测量性能。

按 narrative 进入已声明范围的 compact entry 条件，不等待全部 future extensions。
优先考虑 affine write footprint 的充分分离条件，复用 actual source receipt、numeric envelope
与 byte separation；接受安全后跳过相应 scan，不能用未来稳定性许可检查。
候选与 host 的契约保持时继续复用；不同条件的原入口／checked-entry 连接必须有证书。
同步选择 CGO 2017 Figure 2 的 C 源例和 kernel，记录适配、自动化／人工 metadata、
变换、接受域及 guard 成本；算法、frontend、未完证明和实际语义差异分别归因。
