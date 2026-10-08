# 实际 affine 访问的静态 runtime scan

日期：2026-10-08。前置 checkpoint 为 `fa265c0` 的
[data source factory](multi-array-data-factory.md)。本后继把同一 source package
和 typed allocator 接到泛化扫描，仍是局部服务，未安装新族编译器。

## 改变的能力

旧 pair scan 对两个逻辑数组扫描原循环点坐标。本后继提取 checked
assignment list 中每条 write/read 的实际 `AccessFunction`，在 private
source-domain cursors 与稳定 scalar parameters 上求 affine 坐标，再计算
实际 tensor 地址。本轮的独立实际 AST 与普通 metadata 为：

```c
for (i = 0; i < n; ++i)
  for (j = 0; j < m; ++j) {
    A[i+1][j] = B[i][j+q] + q + alpha;
    C[i][j] = A[i+1][j] + alpha;
  }
```

扫描在任意两个源点求这四个访问模板，并检查跨逻辑数组的单元地址。
证明量化数组 identifiers、访问数、循环 rank、tensor rank 和 scalars，
不要求访问坐标等于迭代坐标或两种 rank 相同。同一逻辑数组的 pairs
生成常量 true，无 runtime pointer comparison。不同坐标的分离来自
layout injectivity；同一 cell 的有意依赖保留给既有依赖验证器。

生成 AST 只依赖静态 metadata 和资源。未知 counts、parameters、dimensions
和 pointer bindings 在运行时读取；源 trace／footprint lists 是证明规格。

## 接口与证据生产

使用者仍交实际 source、普通 description、caller-live names 和 typed
private pool。`check_multi_tensor_region_source` 生产 package。新入口为：

```text
multi_tensor_affine_package_allocate package live pool
    -> option typed allocation
multi_tensor_affine_package_guard package live allocation
    -> actual flag-initialization + Clight scan statement
```

Allocator 自动保护 source temps、bounds、实际访问 pointers、dimensions、
scalars 与 caller-live names，为两个 source-rank cursor vectors 和 flag
选择 fresh int32 slots。Guard 自行初始化 flag／cursors，无 incoming private
value 定义性要求。资源不足、重复或冲突仍静态拒绝。

`multi_tensor_affine_package_source_scan` 从任意实际原源的完成执行、完整
setup 在原 entry 接受，以及 current／original 的公开 frame，生产实际
scan 完成执行、memory 保持、所有 source/caller temps 的 frame、原源 Loop
执行及 computed flag。True flag 导出 actual source footprint 上的受限
locator NonAlias。Numeric/layout/box、访问许可和 NonAlias 不由源码使用者
填写 callback。

本端点消费已有 `decision_run` setup 接受证据；它尚未把完整 setup AST、
泛化 scan 和 candidate 分支组装为新的 versioned compiler。Source/model
结论仍使用 original entry locator，下一项须运输到 actual scan exit。

## 证明链与责任

| 环节 | 证据与责任 |
| --- | --- |
| 完整 setup／checked source | Domain factory 与语言 source 服务生产 numeric/layout/box 和 actual Loop 执行 |
| 原源 trace | 语言 memory/store 服务运输每个实际访问的 entry Readable 许可，不运输数据值 |
| affine/address 编码 | 语言服务证明 pure、typed、可求值的 valid/aligned 地址 |
| static tests／双矩形 | 语言循环与 Boolean 服务证明实际执行、flag 结果和 memory/public frame |
| coverage／接受充分性 | Domain footprint 与语言 layout／比较定律生产局部 separation |
| 局部 guarded 组合 | Framework kernel 保持，消费证书 |
| 候选／整程序 | 后续 domain 保证与语言 host placement／安装／Csem→Asm 接线 |

检查安全不依赖待检查的 NonAlias，许可来自原源实际执行。沿 stores
运输 permissions 不能把后来初始化的值前移到 entry。检查只求地址，
不读数组数据，使用已许可的 pointer equality/inequality；未生成跨
CompCert blocks 的 relational pointer range comparison。

## 证据与边界

六个 successor modules 提供 affine receipts、完整 footprint membership、
static Boolean tests、actual scan execution、package 接线和计算例子。
独立审计查询 28 个端点：18 个闭合，其余最多 6 项既有 globals，绑定
141 个文件及已验证 parent closure；保持旧 42-global baseline，零新增公理。
[报告](../build/multi-tensor-affine-scan/proof/report.json) SHA-256 为
`34c289cc930bfd31f00e1bb3dd7de15894ee24f0ce65197c22beb5994ed7460f`。
九个闭合计算覆盖三数组源接受、四个精确 affine templates、typed
resources、十六个静态 pairs、shift／parameter cells、同数组无 pointer
test，以及 coordinate-only parameter 的边界。这些运行 Rocq checker，
没有执行新的 native C 或 Asm。

目前 scalar 可观察性 gate 要求它出现在 dimension suffix 或 RHS，例子
让 `q` 也出现在 RHS。另一个普通 metadata 与 actual body 匹配、但 `q`
只用于下标的源被安全拒绝，未把该子集声称为已支持。保留的 diagnostic
分别核对 body recognition、progress、scalar use 与 condition lowering。

对 `N` 个源点和 `a` 个模板，pair 访问工作为 `O(N² a²)`，另含 affine／
address 求值成本。静态代码大小依赖模板与 rank，不依赖 runtime `N`。
False flag 后仍执行原源许可的检查。本轮没有紧凑条件或成本测量。

下一步按 narrative `12419c1` 的证书链运输 source/model 与受限 locator
到实际出口，接 checked candidate／iterator restore／原 AST fallback，
生产 projected guarantee 交 selected host。Loaded 两 store 的 header/prefix、
一般 affine domains、condition 成本与完整 OLO 可用性保持 active。

## 重现

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/compile_multi_tensor_affine_scan_sources.py
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_multi_tensor_affine_scan.py --validate
```

Builder 保留成功 `.vo`；audit 核对 data-factory prerequisite closure、全部
新 assumptions、源／对象绑定及旧 42-global compiler baseline。失败编译
日志保存在 `build/multi-tensor-affine-scan/source-build/`。
