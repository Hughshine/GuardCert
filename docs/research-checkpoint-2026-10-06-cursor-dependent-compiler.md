# 循环化 dependent guard：完整编译器与真实程序验收

2026-10-06。后继于 [逐行 cursor 服务](research-checkpoint-2026-10-06-cursor-scan.md)
和 [dependent compiler](research-checkpoint-2026-10-06-dependent-compiler.md)。
本阶段将实际 guard 的两层扫描改为两个私有 cursor 循环，接通 checked
source package、候选 factory、完整编译定理、提取和真实 C。完整研究 goal
仍 active；一般深层 affine 域、复杂 body、physical alias 扩展、性能与
同例作者负担比较仍未完成。

## 结果与最新 Narrative 边界

再次 fetch 后，`origin/topdown/research-positioning` 的最新 narrative 是
`7d94d810685a691efbf07df734f5fad8abfb4724`；main 的
[paper narrative](topdown/paper-narrative.md) 和
[context lifting](topdown/context-lifting.md) 与远端正文一致。
最新澄清约束本次实现：最小 kernel 止于局部 guarded correctness；条件
处理／prefix scan 是上层库，完整程序安装属于语言 host。没有重排文件、
增加 kernel API 或把安装义务放进一个未经实现的 lifting 字段。

新入口是
`ClightGuardedAffineCursorDependentCompiler.compile_guarded_affine_cursor_dependent`，
[完整正确性定理](../prototype/interface/ClightGuardedAffineCursorDependentCompiler.v)
为对应的 `_correct`，结论仍是 Csem→Asm backward simulation。
它保留真正 `i<**root` source key、ordered private captures、原三类候选
checker、公开出口恢复、原 compound-load fallback 和已有语言 host。

## 实际实现与责任

| 责任层 | 本阶段新增／消费 | 仍不是该层自动提供的事实 |
| --- | --- | --- |
| 最小 kernel | 保持既有局部证书组合接口，无新增定律 | 不理解 affine 域、pointer cells、Clight loops 或全程序 context |
| Clight 上层库 | [NestedCursorScan](../prototype/interface/ClightNestedCursorScan.v) 证明两个实际私有 cursor 的执行；[StagedCheck](../prototype/interface/ClightStagedCheck.v) 顺序连接前置检查、循环扫描、候选检查和最终分派 | 调用者仍需提供逻辑检查可用性、模板读取范围与私有资源；不能从一个 loop AST 推出未来访问安全 |
| Domain／实例 | [双坐标模板](../adapters/compcert-memory/GuardMemoryAffineNestedCursorProbes.v) 和 [完整 scan 对应](../prototype/interface/ClightAffineDependentCursorScan.v) 精确等于原 stability condition；实际 checked package 填完 callbacks，复用 reached-write receipts、观察保持及全部 rows 覆盖 | 候选正确性、原 source/model 对应和 `B⇒A` 不由 kernel 推断；没有新增通用 projection |
| 静态资源适配 | [Resources](../prototype/interface/ClightAffineDependentCursorResources.v) 用有限语法检查证明名字分离、public read scope 和模板 freshness | 私有资源数量不是最小值；拒绝不等于条件不可能成立 |
| 具体 rewrite／语言 host | [Rewrite](../prototype/interface/ClightAffineDependentCursorRewrite.v) 复用原局部候选链；[Factories](../prototype/interface/ClightAffineCursorDependentCandidates.v) 和新 compiler 消费原 source preparation、scope、progress、typed pool 与 whole-program simulation | finite normal region 不能直接扩大为任意控制出口／无限行为的整段优化 |

前置检查失败时不进入 scan；某 point 拒绝时不 increment，也不执行后续
activity 或地址比较；只有 scan 返回 true 才进入后置候选检查。每个 loop
初始化自己的 cursor，result 由实际代码写入后再读取。语言定理保留精确
memory 和公开 temps，并将原入口的 branch 执行运输到检查后的状态。

这揭示一个具体的边界义务：当前 branch 运输保守保护整个
`statement_temps`，其中包含候选 counters。guard cursors 必须与它们不同，
不能直接复用旧 counter pool 的头两个槽。新 build 默认分配 **21 个**槽：
pointer cache、integer bound、两个 guard cursors、Boolean result、16 个
candidate counters。类型与 freshness 由实际 factory／pool checker 核对；
调用者提供更小 pool 时可以静态拒绝。若以后想复用已初始化的 counters，
须证明更精确的读取／liveness 运输，不能只改槽数。

原 prefix condition 已证明检查沿真实源前缀取得许可；新 lowering 复用它，
没有把未来 bound／pointer stability 塞进 D。逻辑展开树仍用于证明规格，
提取代码不包含 `check_plan_tree`、`bounded_check_tree` 或
`affine_dependent_stability_tree` 的展开函数。资源 checker 也只检查有限
模板，不用完整展开树计算 read scope。

## 证明与构建绑定

`scripts/audit_affine_cursor_dependent.py` 审计八个新模块的 **43 端点**，
其中 13 个通用 Clight 库端点和 21 个 concrete guard 服务端点均在原
CompCert 基线内，最多六项假设。实际依赖 closure 为 **537**，绑定
**976** 份 source 摘要。新 compiler 与独立旧 dependent compiler 回归均
保持原 **42 项** CompCert／PolCert／VPL 假设；没有新增全局公理。
本次核对完整 closure 的编译新鲜度，并编译所有新模块；没有声明 clean
重编译全部 inherited closure。

| 产物 | SHA-256 |
| --- | --- |
| 新 proof report | `0a177e7aaab2ef73c51aca1de1833cb1da2c9751ac2db12e9efa94bc1c4c6340` |
| 新 `ccomp` | `78a17e3dbf4d392a1a6c5277f3ca3fcc30411f7dd857896c179ffac72f6906a0` |
| 新 build stamp | `69d3a27f7dc0d7b0642222039195ee3fb9f7a249c026cc535337b949df752371` |
| 新 triangle native report | `607179a822cb4a0cec60d8d582c0b8c319b18b80e7eb9a4dcf2b54f79a8910a3` |
| 新 ragged native report | `9b54c2d92a7657d7fc514a8ab2126a1c4eec33af307bb9eece69487cc0debd94` |
| 新 triangle guard-probes／size report | `ddc8429933ec8870187a2de986d4f2a7d7f9d08c5dc5d87dde5c7788af78feea` |
| 新 ragged guard-probes／size report | `39fba0ee54c16b21abc2440bcd7013fa2851f29882a04df8718821cdd0c758bd` |

目录为 `build/affine-cursor-dependent-compiler/` 下的 `proof`、`compiler`、
`native` 和 `native-ragged`。旧 dependent compiler、row cursor 服务的
report／source／compiled objects 均分别绑定；没有改写旧 build 或重新
计入旧 native 矩阵。

## 完整 C 与机器路径

复用两个合法 C source：
[triangle](../examples/native_affine_dependent_loaded.c) 与
[ragged](../examples/native_affine_dependent_ragged.c)，后者内层为
`j<2*i+1`。每种域六个配置：mapped、schedule、2×3、4×1、默认 64×64
caps、无效候选；每配置 37 次调用，共 **444 次新入口调用**。Python 源
模型、独立 GCC reference 与新 compiler 的完整 buffers、公开出口和
外围 context 一致。74 次旧 private compiler 同源不安装调用单列。

28 个 store-order 机器探针含两个旧入口对照；接受时观察到 reordered
writes `32,160,97`，拒绝时保持源顺序。不同 blocks 和同 block 非写
offset 的 bound 接受；第一／第二行写中 bound、body alias、不同 body
base 和 cap 拒绝保持源的真实提前停止及公开 marker=123。

另有 **18 个新 guard comparison 探针**，独立于 native report 的
store-order suite。GDB 在实际三个比较指令上读取地址操作数，核对每点
依次比较 pointer-cell 起点、末四字节起点、bound-cell：

- 三角源 `n=3` 的接受检查为 6 个源点、18 次比较；ragged 为 9 点、27 次。
- 第一行 bound 冲突和短数组均只有 index 32 的三次比较。
- 第二行冲突检查 `32,96,97` 后停止，共九次比较；未检查后续点。
- 小 cap 拒绝没有进入扫描比较；默认 cap 的 `n=5` 分别观察 45／75 次。

每个循环只有三个静态 comparison sites，逻辑点的增多复用同一份机器
指令。探针按当前 x86-64 System V 生成形状验证操作数，不是可移植
compiler tracer，也不是合法 pointer-store body 的运行证据。源 body
仍为 Mint32 operations，pointer cell 自身是合法独立 pointer object。

## 实际代码规模

下表比较旧 dependent compiler 与新 cursor compiler：同一 source、
候选文本和 cap 配置，产物及输出摘要均核对。Clight 字节是**整个函数
打印体**；机器字节来自 linked binary 的函数符号大小，不是纯 guard
大小。两个完整私有 guard loops 加两个候选 counter loops 共四个。

| 域／caps | Clight if：旧→新 | Clight 打印字节：旧→新 | linked 函数字节：旧→新 |
| --- | --- | --- | --- |
| triangle 4×4 | 190→111 | 34,009→24,756 | 1,090→879 |
| triangle 64×64 | 20,710→111 | 12,974,466→24,771 | 72,083→879 |
| ragged 4×8 | 271→112 | 51,084→24,877 | 1,356→916 |
| ragged 64×64 | 20,711→112 | 13,264,404→24,892 | 105,857→916 |

增加 caps 不再增加 if／loop 数量。旧 default cap 的扫描展开增长在这两
个实际 compiler 使用者中已关闭。前置／后置范围检查仍有重复；是否
消除它们需另有证书。**没有编译时间、guard 执行时间、程序性能或总
proof burden 收益结论**，也没有完成 P4 的同版原 CompCert 对照。

## 复现与后继验收

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_affine_cursor_dependent.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/build_affine_cursor_dependent.py
python3 scripts/native_affine_cursor_dependent.py
python3 scripts/native_affine_cursor_dependent.py --ragged
python3 scripts/validate_affine_cursor_dependent.py
python3 scripts/validate_affine_cursor_dependent.py --ragged
python3 scripts/probe_affine_cursor_dependent.py
python3 scripts/probe_affine_cursor_dependent.py --ragged
python3 scripts/probe_affine_cursor_dependent.py --validate
python3 scripts/probe_affine_cursor_dependent.py --ragged --validate
```

GDB 运行须在允许本地 ptrace 的环境。仅 `--validate` 不重跑 GDB，重新
核对保存的 commands、logs、operands、源／候选／compiler 和 size 绑定。
Makefile 提供对应 proof、compiler 与两个 native targets。工具链沿
`toolchain.lock.json` 的 CompCert v3.18 commit 和 Rocq 9.2.0；上游版本
文件自报 3.17，lock 已单独记录该值，不以 assembly banner 改称另一个
baseline。

后续按实际义务推进：推广一般深层 affine source／多参数布局和复杂
body；增加不同 body bases 的物理 alias 接受；实现合法 typed
pointer-store body 与双观察拒绝；独立完成 P4 计时和同例已有工作／
作者 obligations 比较。已有 temp／memory／private frame 服务继续
复用，只有真实受阻实例才讨论更弱的 guarantee/requirement 或新 kernel
能力。计数和代码大小不代替 generality、novelty 或 profitability。
