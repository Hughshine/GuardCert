# Double tiling：最终候选到整程序的证明接线

2026-10-09。本次重新 fetch `topdown/research-positioning`，可见 head 仍为
`8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9`，两份 topdown 正文与 main 一致。
继续采用 [narrative](topdown/paper-narrative.md) 的责任边界和原程序验收标准。
本阶段完成证明接线；真实 double tiling 的 native producer 和原案例安装验收
尚未完成。原 corpus 安装／非恒等计数不变，不报告性能结果。

## 交付内容与责任

| 提供者 | 本阶段的工作 | 使用者还需要什么 |
| --- | --- | --- |
| 最小 framework kernel | 复用局部 guarded correctness；没有改接口或新增语义定律 | 新语言／变换实例仍须交付适用证书 |
| Clight 语言实例 | 复用真实 candidate lowering、safe capture、private/public frame、I64 出口、source progress 和 scoped host | 实际 source、资源和 placement 必须通过检查 |
| Polyhedral domain 库 | 将构造性 multiple-statement tiling progress 参数化为 `POLIRS` functor；实例化 double；检查最终实际候选 | 源族受 checked factory 限制，不是任意 C 或任意变换的自动证明 |
| 不受信任 producer | 提议 phase OpenScop、point-space witnesses 和最终 bound adaptation | 提议仍要通过 phase、最终候选和 lowering 检查；本阶段尚未交付 native producer |

源码用户给 marked C 和策略数据。Source/model、入口范围、实际检查执行、
候选、frame 和安装的适用义务由支持族的 factory 内部闭合，用户不逐 site
提供 semantic callbacks。新增 source/transformation family 的实现者仍负责
新增对应定律；这与已支持族的源码用户接口不同。

`PolCertTilingProgressFor` 是 domain 库，不是扩大后的 generic kernel。
它使用既有 `POLIRS` 的 instruction/state/access 定律。精确终态版本显式
接收 `State.eq` 推出 Leibniz equality 的证明；double 实例在库内证明该事实，
没有把它加入全局公理或交给 C 用户。

## 实际证明链

新入口为
`DoubleTiledChoicesCompiler.compile_selected_tiled_choices_program`，对应
`..._correct` 是原 `Csyntax.program` 的 `Csem→Asm` backward simulation。
其检查路径为：

1. Checked actual Clight source 生产 common-bound I64 nest description、
   actual double instruction、tensor metadata 和原 source progress。
2. Extractor 得到 source polyhedral model，uniform exporter 提交 OpenScop；
   producer 返回 affine middle、tiled after 和 statement witnesses。
3. Checked affine import/validation 和 tiling import/validation 后，prepared
   codegen 产生 raw Loop。
4. Producer 提议最终 Loop；最终 checker 重新提取其实际 body，核对完整
   point domain、instruction/access、tiling witnesses 和依赖。构造性 progress
   证明它在**实际捕获参数**下有执行，并保持原 model 的最终 memory。
5. Existing backend 降低这个最终 body，range/resource 检查和执行证明覆盖
   机器计算；guard 复用原 safe capture，拒绝执行 literal original source。
   接受执行后恢复原公开 I64 controls。
6. Checked factory 生产 projected region contract，现有 selected host 检查
   actual scope、private resources 和 placement，再接 verified CompCert backend。

原 Clight 执行是 correctness proof 的语义起点，不是 runtime 预执行。
静态 metadata、runtime capture/acceptance、state transport 和原执行 receipts
分别提供适用前提。此处 guard 没有因为使用 tiling 自动增加 alias test；
支持族仍沿用实际 globals 的静态 block 分离和已验证的 footprint limit。

Raw prepared-codegen 的 backward theorem 与最终 adapted candidate 的 forward
progress 分开。没有假设 raw→adapted equivalence；最终检查实际安装的 body。
失败或 unknown 保留原 source。后续旧 affine/source pass 以 tiled intermediate
program 为输入，重新计算 scope 和资源，并由两次完整程序 simulation 组合。
这没有把旧程序的 site 证据沿用到新程序。

## 验证范围

六模块共 1,132 行，Rocq 9.2 编译通过；独立审计 16 端点、495 reachable
sources 和 8,698 bindings。3 个端点 closed，最大 42 inherited globals，
无新增 global axiom。报告：
[double-tiling-proof.json](double-tiling-proof.json)，SHA-256
`544baf92231d6b58803a73202c181f704063d6efa5cadb3c810058735041c4c2`。

失败 proof attempts 的 snapshots/logs/metadata 已保留并绑定。第一次 audit
误用 generic functor 的 root 名称，保留在
`build/double-tiling/installation-proof-v1/`；第二次通过 concrete instance
查询，报告在 `installation-proof-v2/`。既有成功源／objects 和 baseline 不改。

复核本地冻结证据：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_double_tiled_installation.py --validate
```

本路线当前只支持共同 global bound、从零开始的非空语法 nest，leaf 是一个
checked IEEE-double assignment；运行域可以为空。Initialized double、多个
bound、一般 affine domains 和其他原 source structures 仍需自己的扩展。
证明可接受任意 producer 数据，但不保证能找到候选、提议被接受或得到收益。

## 下一项原程序验收

先让 native producer 在原 `mvt`／`matmul-seq` 等已支持源码上运行真实 Pluto
tiling，保留 before/middle/after、witness、raw/final Loop 和 actual installed
Clight。不能要求用户手写 target，也不能用现有 word fixtures 增加原案例覆盖。
Bound adaptation 必须保留生成的 loop skeleton 和 instruction arguments，
提议 affine enclosure／membership 后由最终 checker 核对；同时避免宽包络
产生大量无效迭代。Default scratch 数量及 unit-tile 坐标是待验的实际资源／
表示问题，不能靠定理端点存在宣称支持。

随后在同一 compiler 上验收原始 double/I64 输入、positive/zero/negative
runtime paths、外部／最终 checker／resource refusal、multiple marked 与
unmarked neighbor、公开出口和 continuation。分别记录检查 code size、运行
工作、接受域与完整调用成本。完整 PolCert sequential phases、CGO 原 BT、
LLVM／SPEC 和 larger tiers 继续保留，完整 goal active。
