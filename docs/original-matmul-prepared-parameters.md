# 原 matmul：生成 Loop 在同一 captured 参数下的 backward source 连接

2026-10-09 后继关闭[conditional capture 阶段](original-matmul-capture.md)所留的
固定参数 backward 缺口。实际 pipeline 的生成 Loop 在本次捕获的 M/N/K 下
完成执行，能恢复同一组参数下的 source Loop 与原 Clight source，并恢复精确
公开 i/j/k 出口。两模块 409 行、10 审计端点，无新增公理。**这仍不证明
候选一定能执行；candidate Clight lowering、forward progress 和 selected
Csem→Asm 仍缺。新 optimized benchmark 数保持零。**

## 为什么 wrapped theorem 不够

原 `prepared_codegen_correct` 消费 `Loop.semantics`，其中参数环境存在量化。
当前 double `InitEnv` 只约束长度，不能由它推出某次运行的 actual captured
values。因而不能先包装 generated execution，再从 source wrapped theorem
取另一组参数并宣称它等于本次 M/N/K。

实际 codegen 的内部定理 `complete_generate_many_preserve_sem` 保留显式
environment，prepared collection 也保留同一 environment。后继在这些
定理上补 fixed-parameter 组合，不改变冻结的 optimizer 实现。

## 可复用接口与责任

`PolCertPreparedParameters(IRs : POLIRS)` 是 optimizer 适配库，使用原
`IRs.Loop`、`IRs.PolyLang` 和 instruction semantics，kernel 不改。它提供：

| 端点 | 输入 | 结论 |
| --- | --- | --- |
| `prepare_codegen_semantics_correct_at` | prepared model 在显式 env 下的执行、wf 与长度 | 原 model 在同一 env 下的 point-list execution |
| `prepared_codegen_raw_correct_at` | 实际 raw codegen receipt、wf、长度和 generated body 在 θ 下的执行 | 原 model 在 rev θ 下的 point-list execution |
| `prepared_codegen_correct_at` | 实际 cleanup 后输出与同上输入 | 同一结论；cleanup 不换参数 |
| `extractor_correct_at` | actual extractor receipt、长度和 model 在 rev θ 下的 point-list execution | 原 source body 在 θ 下执行，final states 满足原 `State.eq` |

第一项组合保留 vendored prepared semantics proof 的 collection／sorting
步骤；复用原收集与顺序定理。Raw generation 复用原 generator correctness；
cleanup 复用实际 singleton cleanup 的 fixed-env equivalence；extractor
复用内部 syntax reconstruction。它们没有强加新的具体语言语义。任意
`POLIRS` 实例的原 instruction/exchange 责任仍由实例提供。

`GuardMemoryDoublePreparedAt` 实例化这些服务：成功 validator 保持 named
parameter context，因此参数长度只从 source 输入要求一次。它将实际
OpenScop callback／import／validate／prepared codegen receipt 接到：

```text
generated body executes at θ
    => candidate polyhedral model executes at rev θ
    => source polyhedral model executes at rev θ
    => original source Loop executes at θ
```

依赖 validator 消费 `NonAlias`。原 matmul 用实际 global location registry
自动生产它；不是新增 runtime alias test。Double instruction、IEEE 运算树
和 memory state 使用既有实例，source 和 target 没有换另一套 IR 或语义。
这条有限执行定理不蕴含 generated progress，也没有 source→generated
的 execution theorem。

## 连接实际 original region 与 captured state

`OriginalMatmulPreparedParameters.original_matmul_generated_model_at` 消费
同一原 matmul pipeline request 和 actual pipeline receipt；在任意三个参数
下保持上述方向。`original_matmul_capture_to_generated_source` 再接实际
exported selected AST、fresh capture pool 与先前 source/fallback transport。
接受时返回实际 cache 对应的三维 nat values；任何 pipeline 返回的 generated
Loop 若在这些值下完成执行，就生产从 checked entry 出发的原 Clight source
execution，memory 是该 model execution 的 final memory，公开 controls
为 `double_matmul_nest_exit` 的精确原源结果。

原 finite normal source execution 仍是安全 capture 的证明起点；static/layout
和 ge/locals 的 global bindings 仍是前提。Header load 和范围前提由实际
capture 交付。这里不会在运行时先执行 source。最终 factory 仍需自动生产
静态事实，并交付适用 host 的 progress／scope／typing／placement 义务。

## 证据与剩余工作

机器摘要见 [original-matmul-prepared-parameters.json](original-matmul-prepared-parameters.json)。
Audit 跟踪 249 reachable sources、7,387 bindings；10 端点均有继承 globals，
最多14项，全部属于原42-global baseline，无新增公理。三次成功与11次失败
证明尝试保留。Generic theorem 的 audit 在实际 double 实例上进行。

- Proof：`build/original-matmul/prepared-parameter-proof-v1/report.json`，SHA-256
  `c9502f90c7ef3ed1f6e52ef6b55fc627898332c50769c603161f2a808952abea`。
- Actual source：`build/original-matmul/source-prepared-parameters-v1/report.json`，SHA-256
  `d97f52eb782654fbe57486313734ed408d9d2a8f729a567567090e5049648fa8`。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_original_matmul_prepared_parameters.py --validate
python3 scripts/summarize_original_matmul_prepared_parameters.py --validate
```

本阶段未改变 extracted executable，未新增 native／cost 实验。此前[真实
Pluto i/k/j pipeline probe](original-matmul-prepared-pipeline.md)与[capture-only
boundary probe](original-matmul-capture.md)仍只代表各自范围，不组合成已运行的
优化程序。成功 proofs／helpers／reports 冻结，后继保持独立检查点。

下一条链必须从原 source 的许可取得 generated candidate 的 forward
execution／progress，完成实际 double Clight lowering 与公开出口恢复，然后
接入现有 selected host 的 Csem→Asm theorem。Finite backward correspondence
不能代替这些义务；全 corpus 顺序功能、实际变换与成本验收继续保留。
