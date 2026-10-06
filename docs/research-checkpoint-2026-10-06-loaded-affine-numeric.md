# Deep affine＋loaded bound：原源 receipt 与 numeric guard

2026-10-06。当前已将递归 affine numeric guard 的安全证据接到真正 loaded
源，关闭 [narrative 实现核对](narrative-implementation-check-2026-10-06.md)
中的 first-path producer 缺口。完整目标继续 active。本阶段还没有新的
稳定性扫描、candidate rewrite、compiler 入口、提取或原生运行。

## 本阶段得到什么

原源的 root header 是 `i < *bound`，body 可以是已有 canonical affine IR
中的任意有限深度。Child bounds 仍是稳定 temps／包围坐标的仿射表达式，
leaf 仍使用已检查的 Mint32 pointer operations。

```text
原 loaded 源的有限正常执行
  → 首次真实 header 的 Mint32 read
  → fresh private cache 的实际写入及原源 temp 运输
  → 原 loaded 源首次到达的 body
  → recursive first-header／active-first-path 参数 receipt
  → 既有 numeric guard 的实际执行
  → 当前 guard certificate＋接受时的 affine_math_domain
```

没有使用完整缓存源执行来许可检查。原 body 可以改变 bound 单元；首次
receipt 不要求该观察以后保持。检查的 source domain 仍要求原源有限正常
完成，不因此提供任意 divergence 的语言宿主。

## 接口、使用者与责任

| 模块 | 实际交付 | 责任／调用者证据 |
| --- | --- | --- |
| [FirstBodyReceipt](../prototype/interface/ClightAffineFirstBodyReceipt.v) | 从 root word 与条件性的实际 first body 取得 recursive first headers、first leaf 及已用参数定义性 | Domain library；消费真实 shapes、controls freshness 和 leaf certificate，复用旧 child decode／first-leaf 证明 |
| [LoadedFirstPath](../prototype/interface/ClightLoadedAffineFirstPath.v) | 原 loaded header 取得 first body；安全 private capture、公开 temp 运输及零次迭代执行 | Clight 服务；消费 normal／quiet body、frameability、private freshness 与原源执行，不消费未来稳定性 |
| [NumericGuard](../prototype/interface/ClightLoadedAffineNumericGuard.v) | 既有 package guard 的 receipt 入口、prepared-domain producer 和实际 `guard_certificate` | Domain 实例连接；复用旧 probe／numeric／math-profile 编码及语言的 `materialized_execution_certificate` |
| [NumericSite](../prototype/interface/ClightLoadedAffineNumericSite.v) | 静态核对完整原 loaded AST、cache freshness、cached model package、实际检查代码；证明 capture＋check 真实执行、公开 frame 和已赋值 cache/result | Source/site 证据；这里只构造 numeric checking site，不是完整优化 factory 或 placement 证明 |
| [Examples](../prototype/interface/ClightLoadedAffineNumericExamples.v) | 三层源识别／拒绝、非空 numeric flag、零次源／检查实际执行与具体 CompCert allocation | 证明 fixtures，分别标明 Boolean 和实际执行边界 |

`affine_loaded_numeric_domain` 包含原 loaded 源完成及 cache 与**当前入口**
Mint32 load 的值一致。后者由 `affine_loaded_numeric_capture_domain` 从真实
private capture 生产，不是使用者预置的未来稳定性。语言运输允许 cache 的
原初值不同；original public scope 与 package 的保护集分别传入。

`affine_loaded_numeric_certificate` 对 capture 后的 prepared entry 工作。
前提固定在该次检查的原入口，guard 保留其 protected ports，包括 cache。
原 source→prepared source 的运输属于语言 preparation 桥；完整安装时仍需
投影回原 public scope，并保持真正原 AST 作 source key。

接口使用顺序是：对实际原 AST 与 proposal 调用
`check_loaded_affine_numeric_site`；使用者从原源执行调用 capture-domain
producer；将返回的 prepared domain 交给 numeric certificate。静态 checker
会拒绝公开 cache、source/model 不一致和不受支持的检查体。选择和 proposal
仍由优化实现者提供，没有通用 assumption extraction。

接受结论只有 numeric flag 和 `affine_math_domain`，尚未包括 memory-bound
稳定性、完整 physical separation 或候选正确性。它不能单独作为重排 loaded
源的 `C_opt` 前提。`lnf_site` 的非空接受目前是 Boolean fixture；没有新增
非空 loaded source／candidate 的原生运行证据。

## 实际验证

命令（使用现有 `/tmp/guard-opam` 的 `guard` switch）：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make loaded-affine-numeric-proof
python3 scripts/validate_affine_nest_materialized.py
```

| 验收 | 结果 |
| --- | --- |
| 新增 `.v` | 5 个，全部 Rocq 9.2 编译通过 |
| 新证明端点 | 25：4 个 Clight 服务、10 个 domain/site、11 个 fixtures |
| 实际依赖与源绑定 | 660 个依赖对象，987 份源摘要 |
| 新端点假设 | 最多 6 项，均在原 CompCert baseline 内；无新增全局公理 |
| 两个当前 compiler 回归 | deep materialized 与 dependent cursor 的 Csem→Asm 端点均保持原 42 项假设 |
| 旧当前 proof 对象 | materialized／current cursor 报告绑定的对象摘要全部不变 |
| 旧 native 绑定 | 十二配置／5,118 次历史调用的 validator 通过；本轮未重跑矩阵 |

证明报告为 `build/loaded-affine-numeric/proof/report.json`，SHA-256：

```text
1081a35140b3ce8c882105d3cc78b3046807f4811809a2643e82f62a1642db8e
```

零次迭代 fixture 证明实际 Clight 的 capture＋check 安全完成、memory 和
公开 temps 保持、cache/result 赋零；child 参数、scalar 与 body pointer
保持未定义。具体四字节 CompCert allocation 与真实 store/load 见证说明其
domain 非空。该 fixture 不把 Boolean 判断冒充机器级读取次数测量。

审计保留已有 proof/native 报告，新增报告单独绑定当前源码和 `.vo`；
新增 endpoint 没有引用旧 full cached-source guard theorem 的执行前提。
Kernel 与既有 candidate checker 均未修改。

## 后继最难义务

下一项是递归 physical scan 与原 loaded 源的前缀连接。每个比较需要已到达
访问的许可；只有前缀检查成功，才能用实际 stores 的字节分离取得观察保持，
再安全推进。Domain 必须生产完整点覆盖和 fuel；第一次访问或包络端点有
权限，不能替代整个数学包络的权限。

具体次序是先扫描实际 reached writes 与 bound 单元的分离，接受后取得
cached-source execution，再复用旧 deep multi-pointer 的跨点依赖／alias
检查。提前执行旧全域 pair scan 仍可能比较尚未获许可的未来点，不能用它
跳过 loaded 稳定性这一层。

完整扫描接受后才能运输到缓存源并消费原 candidate certificate，再接
typed pool、original fallback、scope／公开出口、独立 source progress 和
全程序 host。Dependent headers 与更一般深层源的组合、typed pointer
stores、P4 计时和同例作者责任比较继续保留。上述工作按 narrative
`7d94d81` 的三方责任推进，不需要因本次 receipt 接入修改 kernel。
