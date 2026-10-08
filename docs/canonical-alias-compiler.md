# Canonical alias：从条件服务到完整编译器

2026-10-08。本阶段将冻结的 [domain 服务](canonical-alias-condition.md)和
[实际 Clight encoder](canonical-alias-scanner.md)接入双 loaded-bound、
多数组赋值源族。新的编译入口已提取并通过真实 Pluto／prepared codegen
和完整程序运行矩阵。Kernel、candidate checker 和 selected host contract
保持；本阶段不扩展一般参数化 affine source grammar。

## 源码用户看到什么

支持族的用户仍提供标注 C 与调度／tiling 选项，不填写语义证明、permission
receipts 或 source-execution callback。普通数据 proposer 从实际规范化 AST
识别 source 和候选；已验证 factory 重新检查数据并安装替换。

例如两轴 loaded 矩形中的以下 body，可继续请求调度或分块：

```c
a[i * stride + j] = b[i * stride + j] + alpha;
b[i * stride + j] = a[i * stride + j] + alpha;
```

两数组之间有顺序依赖，候选仍须通过原依赖／schedule／tiling 与实际代码
checker。Canonical 服务只改变 nonalias 前提的运行时求值，不授权任意
交换这两条语句。RHS 采用当前支持的 CompCert word semantics；本例不是
任意 C scalar 或 overflow 语义的推广。

静态 eligibility 检查所有 access templates 的完整 affine maps 相同，且
`2 * cap - 1 <= Int.max_signed`。Pointer roots 可以不同，也可以指向同一
allocation 内的切片；没有 hidden same-block 要求或跨 block 的 pointer
ordering。Eligible 时使用差值 scanner，否则安装原 point-pair scanner。
这是编译时的算法选择，不是 runtime refusal。

运行时仍依次执行原 loaded-header guard、原 numeric/layout/box/profile
setup、新／旧 alias guard 和候选分派。Header 拒绝运行原 loaded AST；
inner setup／alias 拒绝运行已证明对应的 cached source。Outer 空域绕过
child capture 和全部内层准备，允许 child／数组在原源入口尚无定义。

## 自动生产哪些证明前提

`canonical_package_source_scan` 从原 source 的完成执行、原 setup 接受和
guard 入口的 port agreement 出发，自动生产 source-model execution、原
box 的 entry-memory Readable receipts，以及 count ranges。Ranges 来自
原 profile cap 和 numeric setup，加上静态 `2*cap-1` 检查，不增加 runtime
probe，也不要求 caller 补证明。实际 scanner 比较的 canonical points
均属于原 source box；许可来自原源执行。

`allocate_canonical_scan` 复用原 checked typed allocator，在 rank 的两倍
上取得资源，再精确分成 positions、limits、left、right 四个 rank-length
向量和一个 flag。列表 typed、NoDup，并相对 source、read ports 和 caller
public set fresh。Candidate scratch pool 排除全部四组及 flag；不能只
排除 fallback 用到的 left/right。二维需要九个 slots，原 scanner 需要五个。
即使 static eligibility 不匹配，这一 factory 仍保留全部九个资源；因而
不声称有限 pool 下的静态 installation 接受域与旧 factory 完全相同。

新的 guard 出口提供真实 silent normal Clight execution、unchanged memory、
source/read-port/caller-temp frame，并且 flag **精确等于原 alias Boolean**。
Eligible 分支用 domain exactness，ineligible 分支直接用旧 scanner 定理。
因此可在新实际出口复用原 candidate-at-exit、source-at-exit 和公开 iterator
恢复证明，再生产原 `projected_region_contract`。

局部证明消费完成执行，整程序进度另由原 expression-progress host 检查。
这里没有从有限完成自行推导发散匹配。最终入口为
`compile_selected_word_nested_store_canonical_regions`；其 `_correct` 定理
在编译返回 `OK target` 时给出 `backward_simulation (Csem.semantics source)
(Asm.semantics target)`。数据 proposer 均被量化，最终候选重检保持。

## 与 narrative 的责任分工

| 交付 | 本阶段提供者 | 复用／新增 |
| --- | --- | --- |
| `C_derive`：差值比较覆盖原访问对，接受推出 restricted nonalias | Domain 库 | 复用冻结 canonical domain 定理 |
| `C_guard`：machine bounds／coordinates／pointer tests 的安全执行 | Clight 服务 | 复用冻结 encoder；新增 cap→ranges 桥 |
| Fresh typed resources 与 source→receipts producer | Clight allocator／domain factory | 新增四向量分配、setup/source 运输和两个静态分支 |
| `C_opt` 与实际候选对应 | Domain／candidate 库 | 复用原 checker 和 candidate-at-exit |
| `C_host` 局部分派与 region guarantee | Clight 服务／factory | 新 guard execution 接原 fallback、出口恢复和 projected guarantee |
| Context requirement、site installation、progress 与 backend | 语言 selected host | 复用既有 host；新增 compiler 入口组合 |
| Kernel 的局部证书组合 | Generic framework | 保持，无 pointer／affine／Clight 知识 |

新条件服务的作者承担实际 execution／producer／guarantee 接线，支持族源码
用户只承担标注与策略。Framework 没有自动发现优化前提。`C_host` 的局部
choice law 也没有替代语言的整程序 installation 证明。

## 模块与审计

| 新模块 | 查询端点数 |
| --- | ---: |
| [ClightCanonicalScanAllocation.v](../prototype/interface/ClightCanonicalScanAllocation.v) | 8 |
| [GuardMemoryCanonicalRange.v](../adapters/compcert-memory/GuardMemoryCanonicalRange.v) | 1 |
| [ClightCanonicalPackageScan.v](../prototype/interface/ClightCanonicalPackageScan.v) | 1 |
| [ClightCanonicalVersioned.v](../prototype/interface/ClightCanonicalVersioned.v) | 2 |
| [ClightCanonicalMemoSetup.v](../prototype/interface/ClightCanonicalMemoSetup.v) | 3 |
| [ClightWordNestedStoreCanonical.v](../prototype/interface/ClightWordNestedStoreCanonical.v) | 6 |
| [ClightSelectedWordNestedStoreCanonicalCompiler.v](../prototype/interface/ClightSelectedWordNestedStoreCanonicalCompiler.v) | 2 |

23 端点、10 closed、最多 42 项继承的 CompCert／PolCert globals，1,410 可达
source/object/helper/output bindings。冻结 parent 的 692 bindings 核对 hash，
不重跑历史 transitive audits；零新增 axiom/admission。端点计数只包含新
模块本地声明，不重复计算 footer 中的 imported theorem queries。工具链
为 CompCert 3.18、Rocq／Stdlib 9.2、OCaml 4.14.1。

Proof report：`build/multi-word-nested-canonical/proof-v1/report.json`，SHA-256
`f9b3950efd04c164fe778b08ca9cbb105c9732a7497bd8b357a53477827c9e36`。
Extracted compiler：`build/multi-word-nested-canonical/compiler-v1/ccomp`，SHA-256
`307db26683b0d7bff1b2db48e58f39581bf68803b209fe74d0c677b975c3b5fa`。
Successful snapshots、objects、logs 与失败记录均保留。

## 实际安装与运行

同一十配置矩阵通过 1,000 次未插桩 assembly 和 1,000 次独立 printed-Clight
执行。每次核对全部 1,024 arena words、公开 exits／初始 iterators 与分派
路径；包括 row／column／parameter stride、非单位／部分单位／全部单位
tile、实际 schedule、重复 sites／continuation、header／inner refusal、空域、
未标注／disabled／scheduler failure。成功配置各安装四 sites。生成 Clight
中的实际 `bound + bound - 1` assignments 确认新 scanner 已发射。

另外用 `b[i*16+(j+1)]` 和 `b[i*16+j]` 的不同 maps 源程序检验静态 fallback。
四配置共 180 Asm／180 Clight calls，完整 outputs／paths 保持；真实候选仍
安装，生成代码使用旧 scan。因此 eligibility 不匹配没有变成全 region
静态拒绝。Cap 静态不匹配有证明，尚无独立 native case；runtime count
超 cap 的 setup refusal 不能替代这一测试。

两个 native reports：

- `build/multi-word-nested-canonical/native-v1/report.json`，SHA-256
  `68d4aeb5e30d82a509059f503c03a5f08d6d31801e8b24312aee7ca2c73126fa`。
- `build/multi-word-nested-canonical/nonuniform-native-v1/report.json`，SHA-256
  `27d18cd4df354cc919d53738bd5a6fd3151e2daf57f9f2ebccce4cb071eb639a`。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_word_nested_canonical.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_word_nested_canonical.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_word_nested_canonical_nonuniform.py --validate
```

这些命令核对冻结证据；不是 fresh-build 完整 artifact。Build helper 拒绝
覆盖成功 compiler，新的实验需要新 work path。成本另见
[完整调用测量](canonical-alias-complete-cost.md)：运行正确不等于优化有收益。

## 仍未完成

本族仍为两个 loaded bounds 的矩形源族、Mint32 数组和既有 scalar grammar，
默认 cap 8；不是一般参数化／非矩形 affine 域，也不是完整 OLO 联合能力。
Header stability 仍逐点扫描，新 alias scan 仍在首次 false 后继续，且保留
重复 access-template 比较。理论的差值空间大小不等于实际 guard test 数。
最小 liveness、通用 boundary clause algebra、作者时间和代表性 workload
收益尚未给出。完整 goal 保持 active。
