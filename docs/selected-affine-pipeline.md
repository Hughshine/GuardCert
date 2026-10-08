# 同一标注编译入口：非矩形 affine 与 loaded-word 实例

2026-10-08；从 main `86f8a0e` 继续。重新 fetch 后 narrative 可见最新提交
仍为 `topdown/research-positioning@12419c1`，两份正文与 main 一致。
本阶段按其“真实 polyhedral pipeline 是必做接入”的要求，把已有 recursive
affine 源证明接到标注区域 host 和实际 Pluto/prepared codegen。

## 使用方式与已经实现的范围

源码用户给普通 C、区域标注和策略选项，不写目标 Loop 或语义 callback：

```c
int i = start, j = 77, K = 79;
#pragma scop
for (; i < n; i++) {
  K = i + m;
  for (j = 0; j < K; j++)
    a[64*i + 8*j] = b[64*i + 8*j] + alpha + i - j;
}
#pragma endscop
/* continuation 可以读取数组、i、j、K 和其他公开状态 */
```

这是实际 child bound 随 parent 变化的非矩形域；不把它改成覆盖矩形。
已验收 profile 为 `GUARDCERT_AFFINE_FLOOR=0`、`CAP=4`、
`BOUND_LOW=-2`、`BOUND_HIGH=4`。这些是 guard 所检查的范围策略，不是
framework 的固定数学上限。原 C 的负起点、超出 cap、body word overflow
或 pointer overlap 等输入仍可执行源 fallback；并不保证所有这样的输入
都被优化。支持的 body 仍由旧 checked affine leaf grammar 决定。

可运行入口为
`build/selected-affine-pipeline/profiled-compiler-v1/ccomp`：

```sh
GUARDCERT_TENSOR_MODE=pipeline \
GUARDCERT_POLYHEDRAL_MODE=tile \
GUARDCERT_PLUTO="$PWD/build/polyhedral-pipeline/pluto-source/tool/pluto" \
GUARDCERT_AFFINE_FLOOR=0 GUARDCERT_AFFINE_CAP=4 \
GUARDCERT_AFFINE_BOUND_LOW=-2 GUARDCERT_AFFINE_BOUND_HIGH=4 \
GUARDCERT_PIPELINE_DUMP=/tmp/guard-affine-phases \
build/selected-affine-pipeline/profiled-compiler-v1/ccomp \
  -fall -stdlib build/selected-affine-pipeline/profiled-compiler-v1/runtime \
  -dclight -S input.c
```

`schedule` 调用实际 scheduler，不带 `--identity`；`tile` 使用 identity
schedule 的实际 tiling phase。混合 rank 未指定 tile sizes 时按实际 rank
给默认 sizes；显式 sizes 必须匹配该次 request 的 rank。外部 scheduler、
数据导入、bound adaptation 或最终检查失败都允许静态 refusal。

## 接口与证明责任

`ClightCertifiedRegionBuilder.v` 是 **Clight 语言库** 的接口，位于 kernel
之上。它不使 framework 理解 polyhedra，也不新增任意 OCaml proof callback。

```text
build_certified_region public typed_pool source
    : imp (option target)

build_certified_region_sound:
    mayReturn (... source) (Some target)
    -> projected_region_contract public source target
```

这里的 sound 字段是新 domain 实现作者一次证明的责任。两个已证明的
factory 注册这个 record；实际 C driver 只调用它们的封闭组合。普通 metadata
与 candidate proposer 仍是任意数据函数，由 factory/checker 验证。

| 责任层 | 本阶段提供／复用的内容 |
| --- | --- |
| Kernel | 原局部 guard、preservation 与 choice 证书组合保持不变 |
| Domain 实现 | Word factory 与 materialized recursive affine factory 各自生产同一种 projected guarantee；各自保留 source/model/guard/candidate 的具体证明 |
| Clight library | Builder 的静态 `or_else`、原 frontend key 的 trim transport、有限 table soundness，以及一次通用 selected compiler 证明 |
| Site/host | 原 selected host 检查 annotation、实际 source progress、scope 和 private pool，再连接 continuation 与 CompCert backend |
| 普通源码用户 | 标注 C、范围和 phase 选项；不提供局部语义定理或手写目标 |

`certified_region_or_else` 只在前一个 builder 静态返回 `None` 时尝试后者。
运行时拒绝是在 builder 已返回的 statement 内执行源 fallback。不得把两者
混称为同一条件。两个 builder 的 source models 和语义前提也没有被等同。

`ClightPolyhedralRegionBuilders.v` 注册原双 loaded-word factory 和旧 affine
materialized factory。Affine factory 检查去掉行政 skips 的实际 source；
既有通用 trim 契约将 guarantee 运输回原 frontend source key。
`ClightSelectedCertifiedCompiler.v` 的 table/installation/backend 证明与
具体 optimizer 无关；`ClightSelectedPolyhedralCompiler.v` 只实例化该证明。
新实例不再复制一份完整程序证明。它仍是 finite normal-returning host，
不提供 open/divergence 或非静默多出口的通用安装。

## 实际多面体路径与范围前提

旧 affine route 的实际 checked package 已提供
`affine_candidate_request`：source Loop、实际 context/pointers、validator
bounds 和 axes。新的普通 proposer 消费该 request：

```text
实际 source AST 的静态 package 检查
  -> request 的真实 parameterized affine Loop
  -> 提出小范围参数 guard 的 source model
  -> PolCert extraction / OpenScop export
  -> 实际 Pluto 调度或 tiling
  -> affine import/dependence + tiling transition validation
  -> 每 statement 的实际 prepared codegen
  -> proposed coordinate/bound adaptation
  -> 针对原 request/source/bounds 的完整 candidate checker
  -> 实际 Clight candidate lowering / source-point guard / public restore
  -> selected host / CompCert Asm
```

没有用 `memory_scalar_rectangle` 替代这条 affine request 的源。
`source.loop` 保存原 request；`pipeline-source.loop` 保存加入小范围 facts
的提案。大型 signed-word intervals 不送到 Pluto 的 signed-int transport；
其他区间按 inclusive endpoints 编码。最终 checker 仍消费原源与原完整
bounds，因此这些普通提案不扩大 trusted base。其接受蕴含原
`memory_bounded_source_certificate`，再由旧实际源／候选执行桥使用。

给 scheduler 范围 facts 是实际需要：不带它们时，无界参数允许 strided
地址碰撞，Pluto 产生当前 evidence interface 不接受的 skew 或部分轴
tiling。本阶段通过 final checking 认证结果，没有另行宣称一个 proved
projection algorithm 或最弱前提合成器。

源许可继续由旧实际 affine source execution 与 reached-point scan 取得。
非矩形 guard 不能借用最新 rectangle service 的 covering-box receipts；
未被原源访问的单元不因此获得读取许可。候选执行与退出恢复、materialized
choice law、private/public transport 全部使用原证明。

## 新证据与确切限制

四个新 Rocq 模块共 208 行，9 个端点、1,594 个可达绑定，全部在旧 42-global
CompCert baseline 内，无新增公理。行数不代表作者时间或 total proof burden。

| 证据 | 路径 | SHA-256 |
| --- | --- | --- |
| 新 proof closure | `build/selected-affine-pipeline/proof-v1/report.json` | `58c7f48419fd4abd23b4c2e5727cb6fd42a0df6cbe402cdb2b14b21d3f2e001b` |
| 新 extracted compiler | `profiled-compiler-v1/ccomp`（同一 build 根） | `92e164fa0c10ba16788fa7001de3f3b060e62eee3370c919d834f11c242dcdc2` |
| 二层 affine matrix | `build/selected-affine-pipeline/affine-2d-native-v2/report.json` | `e1115730b8863d0335c3e4b5841043f49f3259b1ffa37117fe68f63cb000bbb0` |
| 原 loaded-word 回归 | `build/selected-affine-pipeline/word-regression-v1/report.json` | `77f4b54df5fc0346cdb422d35276bf1d7db7c0a64c5c72b9e9f410c2f1647124` |
| 分开的不完整 attempts | `build/selected-affine-pipeline/attempts-v1/report.json` | `9951de0f1eb3ce8af7e81f272474fd84990f7d92be2c84fd72edcd518f916270` |

二层 matrix 的 tile、schedule、unannotated、disabled、scheduler failure、
resource refusal 共 1,008 次未插桩 Asm 和 1,008 次独立 emitted-Clight 检查。
独立 word/memory 模型与 GCC reference 核对所有三数组单元、五个 controls
和 continuation。正常配置安装一处 triangular region 和同一函数的两处
region；每配置实际观察 27 次 candidate selection、57 次 runtime refusal。
不同 blocks、同一 block 的分离 shifted views 各观察 9 次接受；同址模式
零接受。True-dependence chain 的 unsupported generated result 静态拒绝。
两个三层函数在该 matrix 明确未标注，不算新三层优化覆盖。

同一 binary 的 loaded-word route 回归 row tiling、schedule、unannotated 和
disabled，共 400 Asm／400 Clight 检查通过。两组分别报告，调用总数不能
替代一般性、收益或原生机器路径测量。本阶段未测成本／盈利性；旧成本
报告仍只描述旧 binary。

负坐标 profile 会暴露现有 bound adapter 的 zero lower enclosure 局限；
final checker 返回 false、原源保持。非负起点 tier 的 guard 拒绝负起点
运行输入。三层 profiled tiling 已通过 affine/tiling phase，但首个 statement
的 prepared codegen 未在该次 600 秒 compiler deadline 内完成；进程因
`subprocess.TimeoutExpired` 停止，没有 assembly。其他功能检查曾并发运行，
这不是独立 compilation cost 测量。完整矩阵没有将它计作成功。已有三层源证明和
手写候选测试不代替真实流水线的这项缺口。

下一项：一般 signed affine enclosure 与实际候选对应、三层 codegen 成本／
失败原因；随后把 nonrect source-point licensing 与 loaded-word 观察、
更一般 body/chunks 接成联合实例。当前只是共享语言安装入口，尚未合并
这两套语义域。紧凑条件／有用接受域和 OLO 源级功能仍在完整 active goal。

验证冻结结果：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_selected_affine_pipeline.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/native_profiled_affine_2d_validation.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/native_selected_affine_word_regression.py
```

历史 compiler 和失败 smoke 保持；完整三层诊断入口
`native_selected_affine_pipeline.py` 不是当前通过的 tier 验证命令。
