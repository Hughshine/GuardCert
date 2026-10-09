# 独立边界：局部证书到实际完整编译器

这是 [source/capture 阶段](rectangular-double-nests.md) 的安装后继。
支持族保留各轴独立的 global I64 上界，实际 double 数组读写及原 IEEE
运算树。Factory 已闭合 source/model 的适用前提，并连接局部执行、
当前程序安装和 Csem→Asm；C 使用者只给 `#pragma scop` 标注与配置。

本轮 fetch 的 narrative 是 `8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9`，
`paper-narrative.md` 和 `context-lifting.md` 与 main 相同。这里落实它们
对最小 kernel、语言/host 与优化实现者的责任区分，不另外宣布新的 API。

## 从原 matmul 走过证据链

原语料的核心是：

```c
for (long long i=0; i<M; ++i)
  for (long long j=0; j<N; ++j)
    for (long long k=0; k<K; ++k)
      C[i+2][j+2] = beta*C[i+2][j+2]
                  + alpha*A[i+2][k+2]*B[k+2][j+2];
```

模型环境是 `[m,n,k]`；各 instruction arguments 是 iterator coordinates，
不把参数混入 iterator 列表，也不假设三个值相等。Domain 的实际 AST
checker、layouts 和逐轴 cap checker 给出源形状、数学 footprint、机器
表示及 reached location 解析所需事实。数学范围不会凭空产生 `Mem` 权限；
原执行和模型执行中的真实 loads/stores 仍须遵守 CompCert memory semantics。

Language 服务按轴检查正值与 cap 并缓存精确 I32 参数。原执行许可下一个
实际观察；任一步拒绝就停止后续 capture 并运行 source fallback。读取许可、
接受后的范围、header stability 和 private state transport 分别证明。
原 source execution 是证明起点，运行时不会预执行原循环。

接受时，factory 消费真实 observation receipts，接入固定参数的原 Loop
执行。实际 polyhedral pipeline 提议调度、tiling 和 intratile 变换，再由
逐轴范围限制下的最终 checker 验证实际 adapted body。Raw generated code、
point-normalized proposal 和最终 proposal 分别保留。原 matmul 的实际 Pluto
结果把 tile 内 `(i,j,k)` 改为 `(i,k,j)`，保留各 C cell 的 k 顺序和浮点运算树。

Language lowering 接实际 I32 counter/check ranges、typed cache view 和模型
candidate execution，再从各轴自己的 cache 恢复公开 I64 iterator exits。
拒绝分支运输 private capture 后的入口到原 source；在空外层等路径上保持
尚未进入的内层 iterator。Progress 由 actual raw source 单独构造，不从
有限执行 iff 推出。

Scoped selected host 检查 globals、caller locals、公开 temps、private pool、
placement 和 progress，并安装到实际 intermediate Clight program。
后续 header/quotient passes 读取这份当前程序；最后组合 literal normalization、
优化与 CompCert backend 的 simulation，得到原 Csyntax 的 Csem→Asm backward
simulation。Kernel 和 host laws 没有改变。

## 三方接口与复用

| 谁提供 | 输入与证据 | 下游实际使用 |
| --- | --- | --- |
| Generic kernel/library | 已有局部条件与 preservation 接口；Loop assumption execution 服务 | `DoubleAssumption.guard_execution` 被条件化 candidate proof 消费；Clight 分支直接证明，不冒称调用 generic guardify |
| Language/IR/host | 安全 capture、typed values、private/public frame、实际 candidate lowering、source progress、scope/placement 与 backend | 原 capture、reached source/model、candidate execution、公开出口和完整 compiler |
| Domain/factory | actual source decoder、足够的 cap vector、模型对应、footprint checker、最终 candidate validator | 为支持族自动闭合适用前提，不交给 C 用户填写 |
| Untrusted policy | caps、external phases、bound/point proposals、coordinate choices | 只提供数据；实际 checker 决定是否安装 |

新条件实例跨越 guard-library 的 arithmetic、range、observation preservation
和 conditional-control 类别。安全调用需要原 source 许可的具体
观察；acceptance 给精确值、范围和 cache relation；refusal 给可继续执行原源
的公开入口关系，不推出前提的否定。Generated checks 保持 memory、公开状态
和事件，写入的 flag/caches 是 private。当前是生成式 Clight templates，
不是已经证明调用/链接契约的 runtime C library。

## Pool 组织的实际拒绝与修复

首构建 `native-v1` 安装原 matmul，但 `intratileopt1–4`、`seq`、`spatial`
均没有进入 phase。单独链接的诊断 executable 在这些实际原输入上运行相同
normalization 和 extracted decoder，确认它们的完整二维 source 都接受。
拒绝来自资源组织：取出 flag 和逐轴 cache 后，剩余 pool 必须被旧 parser
完整拆成 counter pairs；二维与三维所需的奇偶性不同。

`RectangularDoubleTiledFactoryPadded` 优先调用旧 pair parser；拒绝时允许
舍弃一个未使用的 private declaration 后再次解析。没有生成新标识符或改变
类型；实际 candidate compiler 仍检查返回的 pairs。新 factory soundness
复用同一个 `rectangular_tiled_double_region_contract`，selected host 和新
Csem→Asm 端点继续闭合所有资源义务。成功的 v1 inputs、拒绝与失败 probe
均保持原样；padding 后继单独构建与验收。

## 已固定的证明与运行证据

初始安装证明十模块 1,107 行、33 queried endpoints，十个 closed，最大
assumption set 是既有 compiler 的 42 globals；没有新增全局假设。
审计跟踪 544 reachable sources 并固定 9,423 bindings。Pool 后继三模块
287 行、四端点，也没有新增 globals；审计固定 9,454 bindings。

`native-v1` 首轮七原例完整输出均匹配，但只有 matmul 安装新族。相同 build
完整重跑 62 原例与两项 disclosed adaptations：60 raw 加两 adapted 输出
匹配、两项既有 frontend 拒绝、没有 timeout 或 mismatch。16 个原例安装
33 sites，比前一 header build 增加原 matmul 一处；这不是全部变换配置覆盖。

23 个 disclosed matmul contexts 检查不同 M/N/K、三轴非正边界、逐轴 runtime
cap refusal、无效 cap/rank、错误候选、资源/phase refusal、unit/mixed-unit
分块、多个标注与 unmarked neighbor，完整输出和公开 exits 全部匹配。
十次 GDB observations 在未修改的 assembly 上观察 actual acceptance/fallback：
接受的 cache 值为 `[23,31,33]`、`[33,23,31]` 和 `[98,5,7]`；非正/逐轴
超 cap 路径都进入原 fallback。首轮 GDB 因 sandbox ptrace 权限拒绝保留；
后继授权运行通过。诊断不会写入 target，也不是独立的 compiler proof。

## Padding 后继的实际验收

`native-v2` 在同一原 62＋两适配完整重放中得到 60raw＋2adapted 输出匹配，
两项既有 frontend 拒绝、零 compiler timeout／native mismatch。22 原例安装
39 sites，其中新族七处分别在 fdtd-2d、intratileopt1–4、matmul、spatial；
既有共同边界／header／quotient 族为另外32处，不能重复计数。Compiled
originals 中没有 tiling phase 的数量从首 build 的42降到35；其余失败还要
按真实阶段处理，安装不等于所有source／配置／sequential phases覆盖。

本 build 的三维23＋二维13 context checks全部通过，另有十次 unchanged
assembly路径通过。二维实际使用 `[23,31]` 和 `[31,23]`，保留原intratileopt1
数组和运算树；所有公开 exits、非正／cap refusal、unit/mixed-unit、多个标注
及unmarked邻居匹配。旧build的23＋10项证据分别保留，不换标签。

`seq` 当前通过actual source decoder和98/98 cap，但external producer报告
`missing tiled point space`。实际Pluto前后T(S1)均为(i0,i1)，没有candidate；
这与tricky2的untiled result契约是共同blocker，不是泛称source或validator拒绝。

其他goal命令结束后，对本build原matmul做一组warmup和七组交替完整调用。
标注／未标注是相同compiler与flags，完整输出全部匹配。Wall medians为
0.005166783／0.007069233秒，optimized/unmarked比值0.730883；本次观察中
median较低约26.91%。包含startup、初始化、优化区域及30,002值摘要，guard
未隔离，CPU affinity／外部host load未控制；短调用未建立稳定或普遍收益。
这份新测量不改变旧polynomial/header build的成本记录。

固定摘要见 [rectangular-double-installation.json](rectangular-double-installation.json)。
它合并16份报告，保存成功／失败inputs并检查各自bindings；复验使用：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/summarize_rectangular_double_installation.py --validate
```

## 下一验收与明确限制

接下来处理实际 untiled/mixed pipeline result 的契约、最终checker的剩余
拒绝，以及非零/affine/inclusive bounds、
statement sequences 和 mixed/untiled phase results。当前源形状仍是零起点、
严格 global I64 上界与 perfect assignment nests。

本族尚无 private quotient vector 或 compact dynamic affine tile bounds。
常数范围包络、membership 和 private scans 的成本仍需在较长调用与对应
配置评估；程序输出与安装数不能建立 useful speedup。原 BT、LLVM/SPEC、larger
inputs、其余 sequential phases 和 CGO17 condition derivation/handling 继续
属于 active goal。接口、证明库和这次阶段交付都不是整个目标完成。
