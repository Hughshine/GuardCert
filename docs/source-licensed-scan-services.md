# Source-licensed scan：共用条件服务接口

2026-10-08。本阶段把原 pair scan 与 canonical scan 接到同一份 factory、
loaded-source region 和 selected compiler 证明。新增接口位于 Clight／domain
库之中；语言无关 kernel 不改变，也不获得自动 context lifting。

## 接口真正要求什么

[ClightSourceLicensedScan.v](../prototype/interface/ClightSourceLicensedScan.v)
定义 `source_licensed_scan source ports public ready accepted_fact`。
`ready` 和 `accepted_fact` 是 `clight_entry -> Prop`，不固定为某个 Boolean
specification 或 affine 语义。一个服务包含实际 statement、结果 flag，以及
如下执行定律：

```text
原 source 的 silent normal 完成执行
ready(original entry)
ports 上 original 与 current 一致
    =>
存在实际 guard execution 和 Boolean answer：
  有限、E0、Out_normal
  memory 完全不变
  source temporaries + public 保持
  ports 保持
  result flag = machine Boolean(answer)
  answer=true => accepted_fact(original entry)
```

Current 可以已有私有 capture／control 状态；无需完整 entry equality。
检查可以写私有 scratch 和 flag，但不能破坏上述 source/read/caller frame。
服务不要求所有私有状态与原入口相等，也不要求新条件与旧条件的 Boolean
精确相等。这允许以后使用更便宜、接受域不同的充分条件。

`licensed_scan_choice_execution` 消费这个边界，以及针对 accepted/refused
实际出口的 branch proofs，组合实际 guarded choice 和所需 postcondition。
它是语言局部组合服务，源执行前提目前是完成的 `Out_normal` 执行；不是
一般发散／非局部控制协议。源 progress、source scope、placement、private
declarations、continuation 和整程序 installation 仍由实际语言 host 负责。

`Prop` 参数的表达力不等于通用 synthesis：接口不会把任意 predicate 自动
编码成 C。新服务作者必须提供可执行 AST 和上述安全／frame／充分性证明。
源码用户不填写这一证明，也不向提取器提交任意 semantic callback。

## 多面体实例怎样使用

[ClightMultiTensorScanService.v](../prototype/interface/ClightMultiTensorScanService.v)
为现有 checked source package 实例化这层边界：

- `ready` 是原 numeric/layout/box/profile setup 接受。
- `accepted_fact` 是入口 layout observation 与原 source footprint 的
  restricted nonalias，正是已有 candidate-at-exit 定理需要的事实。
- `ports` 使用原完整 bounds／pointers／dimensions／scalars／source／caller
  保护集合；没有把扫描器的额外私有状态加入 public。
- `multi_tensor_prepared_scan` 组合该执行证书和候选 scratch pool。
- `multi_tensor_scan_builder` 从 checked package、public 和 typed pool
  返回准备好的服务，或因资源等静态不匹配返回 `None`。

这里的 builder 是**已经证明的服务实现**，与普通不受信任的 source metadata
和 candidate proposer 不同。两个已注册实现均由源码中的 checked allocator
和执行定理构造；proof fields 在 extraction 中擦除，运行 driver 只能选择
已注册实现。将来增加服务，需要先证明它，再注册；不允许把未证明的
OCaml scan callback 当作有证书的 builder。

`pair_scan_builder` 复用旧两向量 allocator 和实际 point-pair scanner。
`canonical_scan_builder` 复用四向量 allocator、严格 uniform-map／cap
eligibility 和新／旧 scanner 两分支。两者从原 source/setup 自动生产内部
许可，支持族的源作者仍只给标注 C 与策略。它们保留旧 alias Boolean 是
各实例已有的强性质，不是共用接口的额外要求。

## 共用 factory 的运行与证明

[ClightMultiTensorServiceFactory.v](../prototype/interface/ClightMultiTensorServiceFactory.v)
只写一次以下链条：

```text
prepare checked package / resources
    -> 原 actual candidate checker
    -> readonly-probe setup + shared dispatch
    -> service statement + private result decision
       accepted: candidate + public iterator restore
       refused: source
```

Setup 拒绝跳过 scan；接受后，`scan_service_alias_execution` 只用 service
提供的实际出口、public／ports frame 和 entry fact，调用原 candidate-at-exit
或 source-at-exit 定理。它不展开两个 scanner 的循环、pointer tests、
Boolean specification 或 source-model receipts。

`check_scan_service_full_execution` 对任意已证明 builder 统一给出局部
source→target actual execution 与 public exit。两条额外 computation
theorems 给出对所有 checked packages／资源／candidate proposals 的等式：

```text
check_scan_service_full pair_scan_builder
  = frozen check_multi_tensor_memo_setup_full
check_scan_service_full canonical_scan_builder
  = frozen check_canonical_memo_setup_full
```

等式包含 allocator、candidate checks、setup result selection 和 emitted
fallback／candidate AST，不是只有观察层面的测试吻合。它没有把九 slots
的 canonical allocator 改回旧五 slots，也不宣称两策略的静态接受域相同。

## 从 loaded source 接到完整程序

[ClightWordNestedStoreScanService.v](../prototype/interface/ClightWordNestedStoreScanService.v)
一次性参数化原 loaded-header connection：header refusal 跑原 loaded AST，
接受后获得 cached-source execution；outer empty 跳过整个 inner preparation。
Inner setup／alias refusal 跑对应的 cached AST。该证明只调用共用 factory
定理，生产既有 `projected_region_contract`。

[ClightSelectedWordNestedStoreServiceCompiler.v](../prototype/interface/ClightSelectedWordNestedStoreServiceCompiler.v)
一次性把 builder 参数接到原 selected expression host 和 backend。
`compile_selected_word_nested_store_service_regions_correct` 仍是编译成功时的
Csem→Asm backward simulation；metadata／candidate proposers 被量化。
新的服务不需要复制这两个模块或再证明 host installation。

接口对 `C_guard`／`C_derive` 的分工如下：语言服务负责实际求值、memory／
public frame 与 source 许可；domain 提供足够的 entry fact 和候选证明。
Factory 负责把它们在同一 actual exit 接好；host 提供 scope／progress／
installation。新服务的本地执行证明可以继续使用原 domain 和语言小定理，
不会由 common factory 自动推断。Clause algebra 和另一个 host 的复用尚未
实现；两个算法在同一个 Clight host 上的复用不能冒充跨语言证明。

## 本阶段证据与后续

五个模块已编译；独立审计 19 端点，最多 42 项继承 globals，1,414 可达
bindings，零新增 axioms。0 closed：这些接口／记录类型携带实际 Clight
语义或服务实例证明，依赖旧 semantics／classical／compiler globals。
所有 endpoint globals 均核对既有 42-global baseline，不把这一数量解释
为新语言公理。

Proof report：`build/scan-services/proof-v1/report.json`，SHA-256
`2bb64dae927665370a52d5a27e81f4f9f5cbcb6fdfec9732ecb366080448e498`。
Parent 的 1,410 bindings 核对 hash，不重跑旧 audits；成功 source／objects／
snapshots 与全部失败日志保留。

提取器在 `build/scan-services/compiler-v1/ccomp` 安装这个 common entry。
Compiler SHA-256：
`6ad8ce726fbe4ece057312078959644b7096de9c65ead7884dcf1fab172e048c`。
`GUARDCERT_ALIAS_SCAN=canonical` 是默认策略，`pair` 选原策略；其他值报告
参数错误。每个策略均通过相同十配置的 1,000 次未插桩 assembly 和
1,000 次独立 printed-Clight calls，完整 1,024 arena words、public exits、
初始 iterators 和 dispatch paths 都匹配源模型。成功配置各安装四 sites；
row／column／parameter stride、实际 schedule／tiling、单位 tiles、重复
sites／continuation、header／inner refusal、空域与失败 scheduler 均覆盖。

两份 native reports：

- `build/scan-services/native-canonical-v1/report.json`，SHA-256
  `0d2aaeba8e9cb48e372b70c5e941313a561785597fe37ef05791be3b2f7bed04`。
- `build/scan-services/native-pair-v1/report.json`，SHA-256
  `24305a9001d6114fd112ce7c642d26fbd38e3f607149a1ed8783df1ac02543d9`。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_scan_services.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_scan_services.py --validate
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_scan_services.py --service pair --work build/scan-services/native-pair-v1 --validate
```

这个阶段整理证明复用，不降低扫描工作、不扩展一般 affine source 或 OLO
接受域，也不新增 CPU 收益结论。原完整成本仍见
[canonical 测量](canonical-alias-complete-cost.md)。下一项是通过第三个服务
减少重复／常量 tests 和 false 后的工作，再接同一 factory/compiler 验证。
接口能否充分降低作者负担，要由这个第三实例继续检验，不能只看抽象定义。
完整 goal 保持 active。
