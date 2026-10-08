# Readonly probe 消除：实际 loaded-loop compiler 后继

2026-10-08。Parent 是 [shared setup](word-nested-store-shared-setup.md)。
本阶段在实际 numeric/layout/box/profile 条件里删除路径上重复的表达式检查，
沿用原 header、alias、candidate 和语言 host。新 compiler 已提取、运行，
kernel 和 host contract 保持。完整 active goal 尚未完成。

## 服务接口和证明

`ClightReadonlyProbeMemo.v` 提供：

```text
memo_readonly_tree facts tree
readonly_probe_facts entry facts
memo_readonly_tree_exact
memo_readonly_empty_exact
```

`facts` 是 `(Clight expression, Boolean result)` 列表，其证明要求每个结果
在同一 readonly entry 上成立。编译算法用完整 expression 相等判定，包含
类型等语法信息。遇到已知 probe 时选其已知子树；否则保留原 test，并仅
在相应子树追加该 test 的 true/false 事实。Compiler 从空 facts 开始，不向
源码用户要求额外事实。

例如以下树的第二个 `root > 0` 可以删除：

```text
test(root > 0,
     test(child > 0, test(root > 0, accept, refuse), refuse),
     refuse)
```

`root <= 0` 时两棵树都不读取 child。服务没有前移读取，也没有在 loop body
或 mutable scan 之间保留事实。固定 Clight entry 上的 Boolean determinacy
覆盖普通 readonly loads；首次 test 的定义性仍由原条件证书负责。当前
compiler 将服务应用于 **cached numeric setup**，不是 header/alias scan。

`memo_readonly_tree_exact` 证明在有效 facts 下，新旧树对每个 Boolean 结果
的 `decision_run` 等价。空 facts 推论无需前置事实。原树的安全/可用性与
接受充分性由此沿用；不重新证明 polyhedral 候选。

`ClightReadonlyProbeMemoCost.v` 另定义带 `nat` 计数的 `readonly_tree_work`：
leaf 为零，每次执行 test 增加一。它证明该关系与普通完成执行的对应，并
证明 `memo_readonly_tree_work_bound`：新树存在同结果执行，计数不超过原树。
这里的一次是一次 Boolean expression test，不是一个机器指令、一次 load
或一个 CPU cycle。不同表达式本身的计算成本可能不同。

这是 Clight 的、与具体优化器无关的条件库；还不是任意语言的 memoization
API，也没有加入算术推理、跨表达式的逻辑蕴涵或自动静态事实发现。

## 实际接入与责任

`ClightMultiTensorMemoSetup.v` 从 package 的原 setup guard 构造 memo 后的
check-plan；在候选检查后选 checked fresh typed flag。原 setup 从真实源
execution 得到许可，新旧 Boolean 结果定理将该许可运输到新树。原 alias/
candidate execution 使用原 setup 证据；check-plan/private/public frame
服务负责实际 dispatch。Source/model/candidate 证明保持。

`ClightWordNestedStoreMemo.v` 沿用完整 loaded-header rewrite 的实际出口：
header 拒绝执行原 AST；outer 空域跳过 child 和整个 setup；活跃路径执行
新的内层 statement；setup/alias 拒绝执行已证明对应的 cached source。
Factory 生产同类 `PrivateRegion.projected_region_contract`。

`ClightSelectedWordNestedStoreMemoCompiler.v` 消费既有 selected expression
host，保留原源 progress、scope、合法位置和 private pool 检查，给出
`compile_selected_word_nested_store_memo_regions_correct` 的 Csem→Asm
backward simulation。任意 data/candidate proposer 均被量化，不依赖一个
proposer 提供语义 callback。

职责对应 [narrative 对照](narrative-kernel-host-review-2026-10-08.md)：kernel
消费局部证书；语言证明 partial readonly expression、lowering/frame/progress
及安装；域库证明原 setup 的充分性与 source/model/candidate 对应。新库
只处理重复 probe 的语义运输。源码用户仍给 marked C 与 phase/tile 选项，
不手写目标 loop、NonAlias/no-wrap 前提或 semantic callback。

## 审计和真实运行

报告 `build/multi-word-nested-memo/proof-v1/report.json`：五模块、18 端点，
1 闭合，最多 42 项既有 globals，1,380 可达绑定；核对 parent 的 1,376
绑定，无新增公理。报告 SHA-256：

```text
86751923c5d1873d2bd93504cad6c1fd87778bdd0a5463e3353a2ffcf729a2b1
```

提取入口：

```text
ClightSelectedWordNestedStoreMemoCompiler.compile_selected_word_nested_store_memo_regions
```

Compiler checkpoint 为 `build/multi-word-nested-memo/compiler-v1`，普通 ML
metadata、真实两轴 Pluto、per-statement prepared codegen 和完整候选 checker
保持，100 个 private int32 slots 保持，不增加虚拟 axis。

`build/multi-word-nested-memo/native-v1/report.json` 的相同十配置通过
1,000 次未插桩 CompCert Asm 调用和 1,000 次独立 GCC/Clight 分支诊断。
完整 1,024-word memory、公开/首次 iterator 出口与实际逐次读取 header 的
源模型一致。每个正常配置安装 `[1,0,2,1,0]` 个 sites，接受/两层回退、
空域、重复标注、continuation、未标注/unsupported exclusion、disabled 和
scheduler failure 的观察路径与 parent 相同。报告 SHA-256：

```text
06171874a71853c25c999b4db0f5b5c7ed89ce21e117822a787e492a432cf335
```

条件语义的精确结果定理与本矩阵的安装结果是不同证据。这里没有证明任意
资源池下两个静态 factory 的接受集合完全相同，也没有扩大到一般 affine
source/domain。

## 配对工作和尺寸

`measure_word_nested_store_memo_work.py` 读取并核对两份冻结 native report。
它定位 actual printed Clight 中 header 接受后的 setup tree，给其中每个
`if` expression 插入计数；保留完整 region 执行与原观察路径计数。每组新旧
各 100 calls，共 2,000 次额外 GCC 诊断；完整输出/观察路径再次核对。
Diagnostic 不是未插桩 Asm 的动态指令或 CPU 计数。

以下动态次数是每配置 100 calls 的合计；bytes 是 `nm -S` 的 linked
CompCert `loaded_pair` function 尺寸。

| 配置 | Setup tests 前→后 | 静态 setup nodes 前→后 | Function bytes 前→后 |
| --- | --- | --- | --- |
| 行，2×3 | 972→468 | 33→15 | 1,442→1,344 |
| 行，1×3 | 972→468 | 33→15 | 1,332→1,207 |
| 行，1×1 | 972→468 | 33→15 | 1,181→1,084 |
| 列，2×3 | 972→468 | 33→15 | 1,426→1,329 |
| 行，参数 stride | 852→444 | 37→17 | 1,594→1,471 |
| 列，参数 stride | 852→444 | 37→17 | 1,596→1,468 |
| 实际 schedule | 972→468 | 33→15 | 1,181→1,084 |
| 未标注/disabled/scheduler failure，各 | 0→0 | 0→0 | 113→113 |

每个配对 call 的 setup 计数均不增加。成功条件通常执行 33→15 次；早期
拒绝可保持 3→3、4→4 或 5→5。Root-source 副本仍为单 site 4、重复 site 8；
未标注/unsupported/driver/main 尺寸保持。全部配置 setup 合计 6,564→3,228。

报告 `build/multi-word-nested-memo/work-v1/report.json` SHA-256：

```text
f40a6b16e5d6e933091e04cb7856b6d810de7405a9e1c64794d2336928bde3c0
```

这没有改善 header 逐点 scan、跨数组 point-pair scan 的复杂度或 cap 8，
也没有证明全调用 CPU 收益。与 OLO 的紧凑条件、参数化源覆盖和作者负担
比较仍未完成。下一项直接做完整配对成本并继续构造紧凑充分条件，不用
更多 source grammar 延后已经闭合族的 OLO 可用性验收。

## 当前 workspace 的检查入口

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python scripts/audit_word_nested_store_memo.py --validate
python scripts/native_word_nested_store_memo.py --validate
python scripts/measure_word_nested_store_memo_work.py --validate
```

Compiler/native/proof helpers 可用新的 `--work` 路径创建后继 checkpoint，
不覆盖已有成功对象或报告。这些检查消费当前 workspace 的已构建依赖；
本轮没有验收一个 clean-clone release artifact。
