# Tensor 原 AST factory 与完整编译

后继于 [坐标条件服务](tensor-coordinate-guard.md)。当前受限实例将实际 Clight
源、静态 metadata、运行条件、候选 checker、kernel certificate 和语言 host
连接到 `ClightTensorRegionCompiler.compile_tensor_regions_correct` 的
Csem→Asm backward simulation。完整多面体目标仍 active。

## 使用者提供什么

优化策略选择实际 source，提出 `tensor_region_description`：dimensions、
scalar identifiers、pointer 与逻辑 array、每个 read/write 的 affine coordinates、
value expression、count cap 和静态 profile。Candidate proposer 提出 mapped
Loop AST 与 reindex witness，或正的二维 tile sizes。策略不受信任。

例如真实 C 输入可以是：

```c
for (; i < n; i++)
  for (j = 0; j < columns; j++)
    for (k = 0; k < components; k++)
      a[((i * ld) + j) * 5 + k] = a[((i * ld) + j) * 5 + k] + alpha;
```

本例提出 dimensions `[n, ld, 5]`、scalars `[ld, alpha]`、coordinates `[i,j,k]`，
value 为一次 load 加布局 `[i,j,k,ld,alpha]` 中位置4的参数。参数 profile 接受 n／columns≤32、
components≤5、1≤ld<1000 和任意 signed32 alpha。完整实际 guard 还检查 root
i=0、positive layout／volume 和全部坐标 BOX；columns>ld 会拒绝。
这些是保守的充分条件，不是推断出的 weakest precondition。

`check_tensor_region_description` 将数据重新绑定到实际 AST，核对 reset 和
nest shapes、unique／protected identifiers、维度读许可、真实 RHS 参数使用，
然后执行 safe coordinate compiler。它自动生产 source/model 证明所需的静态
证据。使用者不提交 SOURCE、bindings、BOX 或退出语义 callback。
支持别的表达式／访问模式时，domain 必须另证明并接入相应 source/checker。

## 源执行如何接到模型和 kernel

前端实际 leaf 有行政 skip。新的 `ClightLoopAdministrative.trim_loop_skips`
去掉 sequence 的 skip，在 loop 内保留 header／increment 并规范化 body。
其 equivalence theorem 保持所有已有完成执行的 trace、outcome、temps、memory；
quiet／writes certificates 也可回运到原 AST。Labels 和 switches 保持原样。
这不是完整控制规范化或小步 divergence 证明。

Package 保存规范化源等式和真实 operation 证书；`tensor_region_source_execution`
从实际原源取得模型使用的 nested execution。Full guard 的安全域由该原执行
许可读取；接受生产 profile、layout、全部 read/write BOX、pointer 和参数视图。
Mapped／tiled checker 接到真实候选执行，再接 `memory_recursive_restore`，
得到同一最终 memory 和 public live-temp agreement。

`ClightReadonlyPreservationKernel` 是新的可复用语言桥：从已有 readonly
preserving rule 构造 kernel preservation certificate，实际调用
`guardify_preservation`，再通过 direct/shared realization 得到 projected
region contract。它不增加 kernel 定义，也不把语言安装藏进 kernel。

## 安装仍需语言 host

Checked factory 从实际程序 candidates 构造有证书的 source/target table。
语言 pool 提出 21 个 signed32 private temps：一个 shared Boolean 和十个
counter pairs。候选 lowering 自己核对 pool／live freshness；资源不足拒绝。
Host 核对实际原源的 structured progress、scope、private names 和 label 边界，
以 continuation simulation 安装满足合同的局部替换。

因此局部正常完成 theorem 不直接充当全程序证明。原源 progress 与 placement
由 host 另行处理，actual fallback 仍是原 AST。SimplExpr／SimplLocals 与经过
证明的 Clight backend 继续组合到 Csem→Asm。失败的描述器、候选或安装核对
保留原源；运行时 guard 拒绝也执行原源。

Proof owner 的进一步核对见
[narrative 澄清吸收](narrative-implementation-check-2026-10-07.md)。三方责任与
四条逻辑链保持；norm、readonly adapter 和 program host 是语言服务，source／
box／dependence／candidate correspondence 是 domain 服务。

## 证明与复现入口

独立报告：`build/tensor-region-factory/proof/report.json`。
SHA256 `640d768bbbe74f456e04c7bfbbf848f994fbcaa6c4018c31ecc82a32feb4e4e3`。
26 entry modules／368 required dependencies；181 端点＝此前142＋新39，89 闭合。
完整 compiler 的42个 globals均属于独立查询的旧 CompCert／checker baseline；
零新增 global axioms，kernel 闭合。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_region.mk native
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_region.mk validate
```

新完整 compiler 与 native matrix 使用自己的目录、helper 和 digest bindings，
不改写原 tensor source／box／backend 或旧 nested compiler 的报告。
Native matrix 比较完整数组、公开 counters、首个 rewrite 出口和外围 effects；
路径插桩另记录实际候选分派。具体运行证据在本轮 checkpoint 单列。

## 当前能力边界和下一项

当前 source class 是 positive rectangular temp-bound nests、单个 Horner-address
RMW leaf、一个 tensor。候选仍由原 affine／tiling checker 保证依赖正确性。
没有 literal-bound transport、多 statement leaf、跨 tensor alias 或完整 BT。
[同例成本](tensor-region-cost.md)现已验收30轮／960批次完整调用和独立guard诊断；
当前行连续源没有重排净收益。[证明归属清单](tensor-proof-ownership.md)记录数据
使用者和新domain／语言的责任，尚未测量其他framework同例作者工时。
新入口的source-only rebuild仍待验收。

下一项用已有parametric coordinates接入坐标次序不同的真实源，再扩展source/domain。
规范化与数据 factory 的成功不证明任意优化前提可自动抽取，也不证明当前 guard
已最小或有收益。
