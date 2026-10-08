# Loaded affine source：checked factory 与整程序证明连接

2026-10-08，接续 [N/M stability scan](affine-snapshot-stability-scan.md)。
新路径从原 `i<*N; K=i+*M` AST 自动构造静态证据，捕获私有 N/M，运行
原源许可的条件，并连接既有 mapped／tiling／schedule checker、实际候选
执行、公开出口、selected installation 与 Csem→Asm。九模块 852 行已编译；
独立审计 37 个端点，其中 17 closed，1,644 个摘要绑定，沿旧 allowed
baseline 至多 42 globals，无新增公理。这里还没有新族的提取 binary、
实际 marked C/native 或成本结果；完整目标继续 active。

## 实际变换与证明方向

示意的原片段如下；真实 leaf 由既有 affine-pointer checker 识别：

```c
rq = *q; rp = *p;             /* 原有读取，保留 */
for (; i < *N; ++i) {
  K = i + *M;
  for (j = 0; j < K; ++j)
    p[32 + 64*i + j] = q[4096 + 64*i + j] + a;
}
/* 原 suffix/公开 continuation 继续保留 */
```

Factory 产出的实际 Clight 具有以下顺序；它不会在运行时先执行原 loop：

```text
retained original loads
Ncache := *N
if original first outer comparison is active: Mcache := *M
numeric preparation
N/M stability checks, stop later probes on refusal
existing nonalias and candidate-range checks
if all accepted: checked/lowered candidate + public exit restore
else: original repeated-load loop
retained original suffix
```

Capture 写两个已检查的私有 temps，memory 不变；readonly condition 从
捕获后的入口读取，保持这个 check entry。候选允许改变自己的私有 temps，
最终 memory 与给定原执行相同，公开 `live` temps 一致。False 只表示回退，
不证明稳定性、nonalias 或范围条件的否定。空 outer 路径不捕获 M；旧
numeric preparation 会拒绝该优化路径，再执行原 loop。

具体语义链逐段保留方向：

```text
给定原 repeated-load Clight 执行
  -> source-licensed private captures / preparation / accepted stability
  -> 同一实际出口的 cached Clight 执行
  -> 既有 cached Clight -> source Loop execution decoder
  -> 既有 checked polyhedral candidate correspondence
  -> 既有 Loop -> candidate Clight execution + public restore
  -> projected finite-region contract
  -> checked original site / selected Clight installation / Csem -> Asm
```

`affine_snapshot_checked_cached_execution` 使用 quiet determinacy，把用于
条件许可的原 completion 与调用者给定的那次实际原执行对齐，运输完整
temp/memory 出口。它没有把任意模型 equivalence 当作 Clight equivalence。
Source-to-Loop 消费
`memory_affine_inner_pointer_region_source_under_ranges`；候选侧复用
`affine_inner_pointer_candidate_execution`，包含原模型检查、实际 lowering
和 restore。方向性的执行构造和完整 compiler simulation 分别陈述。

## 用户输入与谁提供证明

支持族的源码用户仍给 marked C 和策略；底层 proposer/profile 仅返回普通
元数据、实际 candidate/schedule/tiling 和证据数据。源码用户不提供
`exec_stmt`、cached completion、point preservation 或 region-contract
callback。增加新的 transformation 族的库作者仍须证明自己的 source/model
桥与条件充分性；框架不能从任意两个片段自动提取充分前提。

| 责任 | 本路径的具体交付 |
| --- | --- |
| Kernel／组合框架 | 沿用 readonly dependent composition、prefix scan 和局部证书规律，没有修改。 |
| Language 服务 | 沿用实际 capture、load replacement、prefix reachability、point/store permissions、whole-loop transport、quiet determinacy、public/memory frame 和 administrative normalization。 |
| Domain/library 实现者 | 新 source/condition/candidate 连接，把原源许可与 stability 接到原 source/model/candidate 定理；原 candidate checker 没有改变。 |
| Checked factory | 核对实际 original/cached AST、grammar、protected ports、cache membership、fresh scope 与 typed cache allocation；只在实际 codegen 和独立候选检查接受时产出 target/guarantee。 |
| Language host/site | 使用原 source 为安装 key，重新检查 scope、placement、private resources、progress 与 continuation；`compile_selected_certified_regions_correct` 提供已有 Csem→Asm 连接。 |

Compiler specialization 的 `existing` 参数是已经证明的 library builder，
不是 C 源码用户提供的语义接口。提取 driver 下一步应把它实例化为既有
word／recursive affine／private-loaded registry，再加本族；不能在 OCaml
端构造任意未证明的 builder 并把它称为 theorem 覆盖的配置。

## 接口与前提来源

| 接口 | Ordinary inputs / requires / accepted ensures |
| --- | --- |
| [ClightAffineSnapshotSyntax.v](../prototype/interface/ClightAffineSnapshotSyntax.v)：`describe_affine_snapshot_source` | 原 loop、两个 cache identifiers、普通 profile。独立 source checker 生产 actual source equality、signed-word header grammar、M read membership、protected identifiers、stable-cache membership 和 exact cached-body shape。 |
| [ClightAffineSnapshotCaptureCandidate.v](../prototype/interface/ClightAffineSnapshotCaptureCandidate.v)：`check_affine_snapshot_capture` | Checked site 与 public `live`。检查 frameable 原 source、两个 cache 对 original temps/public/pointer ports 的 freshness，以及 cache distinctness。Typed cache declaration 另由 source factory/pool 检查。 |
| [ClightAffineSnapshotCandidateCondition.v](../prototype/interface/ClightAffineSnapshotCandidateCondition.v)：`affine_snapshot_candidate_condition` | Static package 和 width/alias compilation facts；safe domain 是 conditional original receipts、原完成执行与 retained pointer observations。接受生产 ready、N/M point preservation、footprint-restricted nonalias 与实际 candidate ranges；complete cached source 在调用原 alias/range 服务前被生产。 |
| [ClightAffineSnapshotCandidateExecution.v](../prototype/interface/ClightAffineSnapshotCandidateExecution.v)：`affine_snapshot_guarded_candidate_execution` | 上述 domain 加一次具体原执行。接受运行已验证实际 candidate；拒绝运行原 source。两分支输出原 final memory 与 public-temp agreement。Guard AST 与证明所用的 function-entry/observation relation 无关。 |
| Capture 文件：`affine_snapshot_observed_captured_candidate_contract` | 自动 checked capture resources、实际 candidate certificate/codegen、原 retained loads 的 observations check。把 capture、全部条件、candidate/fallback 接成共用 finite host 的 `projected_region_contract`。 |
| [ClightAffineSnapshotCandidates.v](../prototype/interface/ClightAffineSnapshotCandidates.v)：`check_affine_snapshot_source` | Ordinary actual source、typed private pool、profile/proposal。保留原 prefix/suffix；从 pool 保留两个 signed-int caches，自动检查 source/capture，消费 mapped／tiling／generated-schedule 的完整 checker与原 codegen；返回 Some 时证明原 source 的实际 region guarantee。 |
| [ClightAffineSnapshotRegionBuilders.v](../prototype/interface/ClightAffineSnapshotRegionBuilders.v) / [ClightSelectedAffineSnapshotCompiler.v](../prototype/interface/ClightSelectedAffineSnapshotCompiler.v) | 注册新族，静态 refusal 后从旧 registry 进入本 factory。原 administrative equivalence 运输 frontend grouping；selected host 的 scope/progress/install/backend 保持。Successful `OK target` 得 Csem→Asm backward simulation。 |

来源必须分开：grammar/shape/resources 是静态检查结果；read receipts、
ready/stability/nonalias/ranges 是 capture/guard/transport 给出的动态事实；
原程序完成执行是语义证明起点。不是每个 theorem premise 都需要一个
emitted test，也没有一个检查能在任意未定义入口上安全探测全部 memory。
这与 narrative `c4b1395` 的澄清一致。

## 接受域与尚未验收的范围

- Header grammar 先允许 signed-int constants/temps、单 pointer raw loads 与
  add/sub/mul，再由既有 affine checker限制 cached expression。重复同一个
  M load 的实例被接受；额外未编码 pointer、`i * *M`、division 和 unsigned
  header annotation 的实例被拒绝。这不是任意 expression/presumption encoder。
- 当前族是一个 loaded root、一个独立 raw-child observer 和 checked 二维
  affine-pointer leaf；原 AST 与 canonical setup 的 equality 严格核对。
  已证 normalization 的实际 C grouping 是否足够，须由 parser/native验收。
- Retained `*p`/`*q` 原读取目前许可 base-pointer comparison；不能从 shifted
  loop accesses 或 box 推出 base allocation。Factory 不插入无许可 preload。
- 继承首个 child 必须 positive 的 preparation 和旧 alias envelope；
  first-empty-child 后继非空、distinct allocations 的接受域、value-preserving
  header aliases、一般 recursive loaded domains、scalar/chunk 扩展仍待工作。
- 当前 guard 仍枚举 source-licensed probes，而且 legacy condition 重复一部分
  numeric preparation。这里没有紧凑 guard、工作量/代码尺寸或收益测量。
- Finite contract 使用原 `E0 / Out_normal` completion；program installation
  另消费实际原 source progress，不把它扩展为任意 open/diverging host 定理。

## 审计、保留证据与下一步骤

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_affine_snapshot_installation.py --validate
```

Report：`build/affine-snapshot-installation/proof-v1/report.json`；SHA-256：
`f6387b00777a5e93db249ab834e63796c975d0a56cb4043adc52c42b4add0b6b`。
Rocq 9.2／OCaml 4.14.1／当前 CompCert 3.18 输入；37 endpoints／17 closed／
1,644 bindings／max 42 inherited globals／0 additional axioms。父 stability
report 的 1,314 bindings 同时复核；新模块的实际 reachable source/object
closure、helpers、compatibility report、全部 build snapshots/logs 都绑定。
27 attempts 保留：9 成功、18 proof-source 拒绝，其中包含 stale example
object 的加载失败；原成功对象未重建或覆盖，后继改用独立 actual AST fixture。
这些 failures 不是 native 误编译证据。模块数量不是新颖性或作者时间测量。

十二个 closed computations 核对 actual AST selection 与 capture resources，
包括公共 root/child cache 的拒绝。它们不是 actual C parser、完整安装或
runtime matrix 的替代品；本轮未重跑祖先 native 作为新族证据。

下一工作按实际 pipeline 推进：实例化旧 registry 和 ordinary real Pluto
adapter、提取新 compiler，然后在原 `i<*N; K=i+*M` marked C 上检查真实
安装及每个数组/公开出口/continuation。矩阵包含 N/M header alias 改变
循环次数、empty outer 且 M 不可读、wrapping/cap 拒绝、多个 sites与同 binary
旧族回归。随后继续上述接受域缺口、compact sufficient conditions 和完整
guard/candidate 成本；不会以本阶段 library/compiler theorem 代替完整目标。
