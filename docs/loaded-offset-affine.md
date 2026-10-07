# Loaded＋offset 根的 guarded affine rewrite

本实例支持实际源 header `i < *limit + delta`，其中 delta 是 signed32 常量；child 是任意
有限层的 canonical affine loop。读取、原地更新、多数组访问、仿射调度和分块继续使用既有
候选验证与 lowering。新的 frontend proposer 从真实 Clight 提出 metadata，checked site
核对整个原源 AST；并没有把用户输入改写成“已稳定缓存的参数”后才证明。

[阶段验收](research-checkpoint-2026-10-06-loaded-offset-affine.md)提供 Rocq、提取、native
与实际路径证据。Figure 2 的 loaded child 和高效条件生成仍未完成。

## 一个需要条件的例子

```c
for (i = 0; i < *limit + 1; i++) {
  K = i + m;
  for (j = 0; j < K; j++) {
    L = j + p;
    for (k = 0; k < L; k++)
      a[128*i + 16*j + k] += alpha + i - j + k;
  }
}
```

交换或分块需要实际机器控制、仿射域及地址计算与候选模型对应，还需要写操作不改变
`*limit` 的观察，以及相应跨数组 non-alias 条件。普通输入没有这些静态保证。
实现捕获原 header 的整个计算结果，执行 numeric／first-path 检查，再执行短路稳定性 scan；
仅接受后执行跨数组 alias 检查及候选。失败分支保留原 `*limit + 1` 的重复读取。

例如原 load 为 2 时 cache 是 3。若 body 将 limit 写成 1，原循环在 row 2 停止；捕获首值
不能独自许可运行三轮。Rocq fixture 证明 guard 拒绝并运行原两轮源。实际 native 的第一次
写中 bound／第二行写中 bound 两例也保留真实 public exits。读取位置和写入位置位于同一
block 的不相交 offsets 时，可以接受，不能把“同 block”当作必然拒绝。

`load + delta` 按 CompCert 的 `Int.add` 求值；cache 存的是结果，数学 snapshot 存的是实际
raw load。`INT_MAX + 1` 的机器结果为负时，源第一轮为空，guard 可拒绝；不能用无界整数
加一所得正数去许可 child 或 data 访问。本阶段没有引入硬件 overflow flag。

## 安全检查的证明顺序

1. 语言的 signed-expression capture 从原源执行取得实际 header 求值，证明私有 cache
   不影响原源执行和 public observations。
2. numeric checker 消费首个实际 body receipt；空域和未到达参数的处理沿用现有 first-path
   服务，不要求未定义 child 参数已有值。
3. [Body receipt](../prototype/interface/ClightAffineBodyReceipt.v)抽取实际到达 body 的执行、
   stable temps 和权限回推关系。此接口不要求 raw observation 等于 computed upper。
   既有 affine body decoder据此产生当前行的访问权限。
4. [Write tests](../prototype/interface/ClightAffineObservedWriteTest.v)用原 load 的可读性和实际
   write capability 许可安全地址比较。[递归扫描](../prototype/interface/ClightAffineObservedBodyScan.v)
   复用原生成代码；接受检查证明 writes 与 raw observation 的字节范围分离。
5. [Offset prefix](../prototype/interface/ClightLoadedOffsetAffineBody.v)由接受的当前行检查保持
   原观察，再推进实际源前缀。[Root scan](../prototype/interface/ClightLoadedOffsetAffineRootScan.v)
   拒绝后不再扫描未来行。[Cache bridge](../prototype/interface/ClightLoadedOffsetAffineCache.v)
   在所有检查接受后导出 cached-source 执行；该执行不是 scan 的输入前提。
6. [完整 guard](../prototype/interface/ClightLoadedOffsetAffineMultiGuard.v)由原源 completion
   生产 semantic P 和 checked-entry transport。旧 alias-only checker、依赖验证和候选
   执行证明消费 cached source，框架 kernel 组合这些 certificate。

source completion 是证明安全检查的语义域，不是交给运行时的 oracle。完整程序 host 以实际
源进展、region contract 和 simulation 安装检查／候选。程序入口没有新增 numeric、稳定性
或“cached source 已可执行”假设。

## 用户提供什么，哪一层证明什么

| 层 | 本例提供的内容 | 责任 |
| --- | --- | --- |
| Framework kernel | guard／local-preservation certificates 与抽象 choice | 组合单次 guarded rewrite；有限次组合沿用 host 的正确性 |
| CompCert language | signed-expression capture、prefix／cache transport、private frame、source progress、[installation host](../prototype/interface/ClightExpressionRegionHost.v) | check 的实际定义性、只读 memory／trace、public state 与控制边界、完整程序衔接 |
| Affine domain library | checked source package、body receipt decoder、byte separation、prefix scan、entry transport | semantic conditions 充分；实际 Boolean 接受蕴含 P；保守拒绝允许 |
| Optimization implementation | 原源位置／metadata、candidate 与 dependence evidence、条件域和资源提案 | 源和模型绑定、候选在 P 下正确；提案通过 verified checkers 才可安装 |

本实例的用户可以复用 [factory](../prototype/interface/ClightLoadedOffsetAffineMultiFactory.v)，
提供 source proposer 和 candidate proposer；两者是可拒绝的不受信任生产者。checked package
验证 leaf operations／仿射表达式／范围／名称，候选检查器验证域和依赖，typed private pool
与 host 验证安装。本阶段的 native proposer自动从支持的 header 提出 pointer／delta 和已有
recursive affine metadata。支持 grammar 内每个 C 样例不再单独提交 body-stability 定理。

要接入另一种 bound expression，仍需给出该 expression 的 reached capture、observation
含义与接受后保持到 header 求值的语言／domain 实例。更复杂 child 不能直接套这里的完整
body decoder；此处的 child 控制和 affine 参数在 body 中保持。任何这些库参数都不代表
框架能自动提取任意 source/candidate pair 的 assumptions。

## 完整程序端点和当前限制

[Compiler](../prototype/interface/ClightGuardedLoadedOffsetAffineMultiCompiler.v)的
`compile_offset_affine_multi_regions_correct` 证明实际 Csem→Asm backward simulation。
任意提案的成功返回仍须通过 factory、region contract、private pool、进展和 CompCert tail；
检查失败保留源。程序中多个 region 可安装独立 rewrite；native 已验证同函数两次改写。

当前主要限制是：

- native 根语法只自动识别 `load + signed constant`，body reads 为本模型的非 volatile Mint32；
- loaded child／多个在条件下才可读取的 observation 未接通同一 recursive package；
- 稳定性仍逐点扫描，跨数组仍逐点对扫描；强 non-alias 模型仍检查部分 read-read 对；
- 没有一般 projection／最弱条件推导，也没有本阶段的独立运行计时或性能收益结论；
- 新接口用了旧库但仍有 header-specific assembly proof 重复，需要在真实 second-loaded-child
  接入后评估可复用接口和每实例人工负担，不能用模块数量代替这个评估。

条件简化后可继续消费同一候选和 host 契约；新 guard 必须证明自己的安全性、接受蕴含所需
条件及 entry transport，不要求与旧 scan 的接受集合完全相等。
