# 实际 source Loop 接口与整段 tricky3 融合

读者是新增 conditional transformation 的语言／优化库作者。
本后继接在 [common-coordinate 模型](double-tree-common.md) 之后，解决当前
`tricky3` 整段候选的拒绝，并保留其条件、fallback 和完整编译器证明。
[证明摘要](double-tree-source.json)和[实际运行摘要](double-tree-source-native.json)
分别记录证明与运行证据。此 checkpoint 不完成整个 PolCert／CGO17 目标。

## 接口与验证责任

优化器作者提供以下不受信任的提案接口：

```text
adapt : accepted_parameter_intervals -> actual_source_Loop -> raw_candidate_Loop
        -> result candidate_Loop
```

`GuardMemoryDoubleTreeSourcePrepared` 先运行原实际 extraction、polyhedral phases、
验证及 prepared codegen，再将原 source Loop 和 raw output 交给 `adapt`。
它随后用既有最终 domain/dependence／representation checker 检查将被降低的
实际 candidate。接口不要求 `adapt` 的语义证明：拒绝返回原源，接受的正确性
来自最终 checker。提供 source 数据不意味着信任 proposer 的指令、域或坐标。

| 提供者 | 本后继中的责任 |
| --- | --- |
| Kernel | 既有局部 guarded correctness 组合定律；本次未修改 |
| 语言／IR host | source-licensed reads、private captures、实际 IEEE/Mem lowering、准确公开出口、scope／progress 和当前完整程序安装 |
| 优化器／domain 库 | source 模型与 accepted parameter facts、候选提案、实际最终 domain/dependence／表示验证 |
| 具体 rewrite site | 经 checker 取得的原 statement、资源和 placement 证据，由 factory 消费 |

新的 factory 自动消费实际 source/model、guard、candidate 与出口证明；C 用户
仍只标注区域、提供 phase/profile 数据，不补动态语义 callback。
`DoubleTreeSourceCompiler.compile_selected_source_double_tree_program_correct`
接到同一个当前 Csyntax 程序，终点是 Csem→Asm backward simulation。
有限正常 source/model 对应和独立 source progress 继续分开。

## 整段案例与提案边界

原 `tricky3` 有四个 scalar double zero assignments：outer `dist_min=0`，
第一个 child 的 `dist=0;kmin=0`，第二个 child 的 `clusterv=0`。
Prepared codegen 有十九个副本。本 untrusted proposer 从原实际 extractor
读取四个 typed instructions、domain rows 和 `pi_transformation`，提出：

```c
for (p = 0; p < pointc; ++p) {
  dist_min = 0;
  for (j = 0; j < cap; ++j) {
    if (j < clusterc) { dist = 0; kmin = 0; }
    if (j < dims) { clusterv = 0; }
  }
}
```

这是结构示意；实际 Loop/Clight 保留原 domain membership guards。
原程序 cap 为 4096，runtime adaptation 为 32。四个 point shifts 均为零。
最终实际 checker 接受四个候选位置，machine lowering 和新 factory 消费结果。
Emitted Clight 有两个 candidate loops、三个原 fallback loops；public counters
恢复原值，包括空 outer 时未执行 child 的入口 temporaries。

该 proposer 支持 common outer、先 depth-one 再 depth-two 的独立参数矩形域，
保留实际 affine argument rows。它不处理 coupled iterator bounds、任意深度或
general ISS/piece partition。Mixed-depth 候选从 source 重建，**不保留 raw
scheduled codegen 的形状**；因此这里证实的是 source-derived 候选的检查与
整段安装，尚未建立 general codegen-piece correspondence，也不把执行过
phase 等同于覆盖了所有请求的 transformation。Requested tiled 配置仍产生
同一未分块 shape，不能计作新增 tiling 支持。

第一 box 提案及 trace 单独保留。它以 `TConstantTest true` 开始 membership
合取；实际 `ExtractorFrontend.wf_affine_test` 仅接受 LE/EQ/And，故该提案
含不支持的 test。后继从第一个 affine test 开始合取。此前参数／坐标显示
差异没有被证实为该拒绝的根因；不能据此报告已修复的参数编码错误。

## 实际验收

四个新 Rocq 模块共 389 行，查询八个端点；零 closed、最多 42 inherited
globals，未新增 global assumptions。四个 module attempts 均编译通过。
证明审计遍历 563 个 reachable sources，绑定 10,490 个文件。

原 fusion1、五阶段 stencil 和 tricky3 各五配置，共 15/15 完整输出匹配
same-source strict-FP GCC。普通 marked 配置各安装一个完整区域；unmarked 和
错误 shifts 均零安装。这是三例证据，未重跑完整 62 例 corpus。

Runtime adaptation 仅将三个常量 globals 改为 argv inputs，计算区域逐字保留。
同一 profile [0,32] binary 的 21/21 outputs 匹配，包括负值、空范围、不同
child 长度、边界和超界回退。空 outer 时极端 I64 child bounds 不被读取。

九次 GDB 观察使用未改汇编、未插桩 binary。实际 capture counts 确认空 outer
只检查 pointc，拒绝后短路剩余 headers。输入 (2,3,5) 的 unmarked 原源和
accepted 融合分别观察到 24 次 stores，counts 均为 [2,6,6,10]；前者先完成
cluster child 再完成 dims child，后者交错这两组 stores。完整输出相同。
这提供真实顺序变化的证据，尤其因为原 assignments 都是幂等 scalar zero。

两个 observer 失败保留：首 attempt 对 nm/objdump 地址做字符串比较，次 attempt
的 whitespace regex 跨 continuation newline。第三 attempt 数值匹配并只解析
行内 whitespace，九路径和源／融合顺序全部通过。它们是观察工具问题，不是
编译器输出拒绝；没有修改被观察的汇编来让计数通过。

## 仍需完成

实际 inner enclosure 仍为常量 cap。接受且 pointc>0 时，每个 outer iteration
执行 32 次内层循环，两处 enclosure comparisons 各 32 次，即使 child counts
为零。没有 runtime max-bound pruning、CPU 成本、speedup 或 OLO compact
condition construction 完成结果。

下一步用实际 blocker 推动共享服务：去掉无效内层尾段并接 machine lowering；
处理 general pieces／ISS 的 forward/progress 及真实 tiling；推进紧凑条件推导、
安全算术、共享检查消除与完整调用成本。随后继续原 corpus/configurations 和
CGO17 原程序／tiers，所有扩展立即接当前 host／Csem→Asm。

## 复核入口

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_double_tree_source_adapter.py --validate
```

Native 摘要由 `scripts/summarize_double_tree_source.py` 绑定冻结 reports、
提案、emitted code、输出、observer snapshots 和完整证明。
