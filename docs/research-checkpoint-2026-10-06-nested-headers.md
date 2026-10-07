# 2026-10-06：ordered child capture 与层次源前缀

本阶段补上第二 loaded header 的语言／domain 服务。完整 goal 继续 active；
当前仍不能安装 OLO Figure 2 的优化。[接口 walkthrough](nested-header-services.md)
说明输入、证明结果和验证责任。

## 已完成

十个新增 Rocq 模块：

- `ClightNestedExpressionCapture`：原 outer/child headers 许可 ordered captures，
  inactive outer 不求值 child；原 source completion 和 public 出口保持。
- `ClightExpressionReachedPrefix`、`ClightNestedExpressionPrefix`：从 actual
  child execution 打开 global observation／permission anchor 的 inner prefix；
  source witness 保留实际 memory，这一 row 的 inner preservation 成立才推进 outer。
- `ClightNestedExpressionTransport`：单 row 只消费这一 row 的 preservation；
  完整 nested transport 在全部观察保持后导出双缓存 execution 和 exact 出口。
- `ClightSignedIndexedOffsetHeader`、`ClightNestedLoadedOffset`：`shape[k]+delta`
  的 typed read／raw snapshot／computed word 定律，以及双 direct loaded＋offset
  client 的实际 captures、joint observations 和 accepted cached-source bridge。
- `AffineNestCapturedDomain`、`ClightCapturedAffineNumericGuard`：captured
  parameter words 与 bound dependencies 许可旧 numeric probe；无需 cached-source
  completion，接受仍复用原 math-domain 编码定理。
- `ClightNestedHeaderExamples`、`ClightNestedHeaderStoreExample`：真实 Clight
  captures、原源执行、point comparisons、prefix 和 cached-source fixtures。

最小 kernel、旧 candidate validator、current compiler 和 native sources 保持。
这些是 kernel 上的语言／domain 库；本阶段没有新完整 guarded candidate rule、
factory、compiler entrypoint、extraction 或 native execution。

## 实际 fixtures

1. 空 outer：只要求 `shape[0]` 的实际 read；`shape[1]`、child cache／counter 和
   output pointer 不要求定义。conditional capture 执行并保持 memory；raw=-1
   和 INT_MAX＋1 回绕两条路径单列。
2. active outer／empty indexed child：同 block 的 `shape[0]=2, shape[1]=1`
   配合减一 bounds，原 SOURCE 进入 outer、reset child 并读取 `shape[1]`。
   capture 得到 `(1,0)`，guard entry 的 child counter 和 output pointer 不要求定义。
3. changing child：两个原 loaded＋offset headers 都执行，初次 caches 为 `(1,3)`；
   stores 改写共享 bound，原 inner 执行两次、outer 一 row。capture 安全，
   第一个实际地址比较拒绝自别名。
4. 同 allocation 相邻 word：bound 在 offset 0，store 在 offset 4。原 1×1
   nest 执行真实 Mint32 store，point comparison 接受、两项观察保持；actual
   child prefix 可打开，outer prefix 从 0 推进到 1，导出两层缓存源实际执行和
   相同 final memory／temps。
5. numeric：在任意 memory、output pointer 和未来 public controls 未定义时，
   已定义 words 足以执行旧 numeric guard 并接受。此例不提供 data-access 或
   candidate-correctness 证据。

point check 是已有 Mint32 地址分离 primitive 的实际 decision，不是完整新
nested scan。源执行、prefix 和 cache transport 是真实 Clight big-step 证明，
本阶段没有汇编运行证据。

## 验证

在当前已生成 inherited proof artifacts 的 checkout：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make nested-header-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make nested-header-validate
opam exec --root=/tmp/guard-opam --switch=guard -- make loaded-offset-affine-validate
opam exec --root=/tmp/guard-opam --switch=guard -- make expression-header-validate
opam exec --root=/tmp/guard-opam --switch=guard -- make loaded-affine-multi-validate
```

独立 `build/nested-headers/proof/report.json`：

- 48 endpoints：27 language、4 domain、17 fixtures；
- 571 required proof sources；1,057 source digests；
- 每个新端点最多 6 项原 CompCert global assumptions，无新增公理；
- current loaded＋offset Csem→Asm regression 保持原 42 项 assumptions；
- inherited loaded＋offset sources 和 compiled objects 在编译前后保持；
- report SHA-256：`e7ec0838dfab389e36da1b0314f3bc49839194fea8820f4b98bf5e1c742676a7`。

工具链为 pinned CompCert 3.18／Rocq 和 Stdlib 9.2。audit 绑定 source、`.vo`、
辅助脚本和 assumptions log；没有新增 admitted proof 或 axiom。此前 native／
path／guard-work 报告只复核摘要和对象绑定，不累计为新运行次数。从空 build
开始重建全部历史 prerequisites 仍未单独验收。

## 最难的三个后继连接

1. **Physical scan 许可和覆盖。** reached inner body → affine child／grandchild
   decode／word view → 实际 write footprints，在 global entry memory 比较每个
   write 与全部 observations。point 接受才推进 child，row 接受才推进 outer；
   不借用尚未证明的完整 canonical body completion。
2. **原源到 canonical model。** 当前 two-cache transport 保留原 nested AST；
   affine model 需要独立 captured parameter／private bound 的 assignment，
   Figure 2 的第三层原 `<5` 也需要桥。必须证明额外 assignments 的 projected
   execution，保持 public counters 和 final memory。只改 proposer metadata 不够。
3. **安装、运行和成本。** checker 绑定 original AST、typed cache／bound／cursor
   pool 和 public scope，复用 old candidate checker／fallback／host；取得新
   Csem→Asm、提取和完整 C 接受／回退。接通后继续 compact condition generation
   的实际工作量、接受范围和同版 CompCert 计时，不把 scan 当成最终自动化结果。

一般 row-dependent loaded expression、此前含 stores 的 later capture、typed
pointer-store BODY 和通用 projection 仍各需实例与证明，本步不扩张支持声明。
