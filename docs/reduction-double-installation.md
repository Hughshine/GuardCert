# 无 initializer 的 double 循环嵌套：实际 mvt 整程序安装

2026-10-09。继 [initialized factory](initialized-double-installation.md)，新增实际
typed source family：非空 signed-I64 loop nest、各层使用同一个 global I64 bound、
leaf 为一个 checked double assignment。它不要求每行有 initializer，也不要求
assignment 是特定 reduction 模板。原 `mvt` 的两个相继矩阵向量 reduction 均安装；
第二个从 `i/j` 改为 `j/i`，原 IEEE 表达式、double 数组和 I64 源计算保留。
非恒等原案例覆盖增加为4/62。完整目标仍未完成。

[机器摘要](reduction-double-installation.json)绑定全部证明、编译器、成功和失败实验。

## 使用与证明责任

源码用户提供 marked C 和数据策略；无需补 source/model、scope、guard 或 context
的 semantic callbacks。变换实现者若扩展到新语法族，仍需提供 checked source
correspondence、前提 producer 和必要的 source progress。当前 whole-program 入口为：

```text
compile_selected_reduction_choices_program
  chosen_labels private_count schedule inherited_swaps per_site_witness_choices
  actual_Csyntax_program
```

旧 matmul／initialized 路线保留；各 pass 自行检查 actual declarations、scope 和
private resources。`private_count` 仍是资源参数，native 默认16；不足静态拒绝。
新增 `check_reduction_double_choices` 按 site 尝试见证列表，首次成功调用已有
factory 的 scoped guarantee。当前提议为 `[]`、`[0]`；最终 checker 决定接受。
这不是通用 permutation synthesis，任意变换的坐标见证政策仍需扩展。

对应 narrative 的三层责任：framework kernel 组合局部证书；language instance
提供实际执行、检查安全、private/public frame、control exits、progress 和安装；
domain 识别实际 source/model、生产 footprints 与充分条件、提出候选和见证。
本次未改 minimal kernel 或 host。`C_opt/C_derive/C_guard/C_host` 是证据来源，
不是要求 C 用户填写四份 record。

## 条件与局部到整体的证明

实际声明、affine accesses、tensor layouts、iterator IDs 和 IEEE 运算树来自
checker。32步搜索提议 cap，verified interval footprint checker 再核对；不假定
搜索最优性。原 extent100/padding2 给出 `0 <= N <= 98`，extent104 给出102。
Runtime 复用两次有序 I64 比较、接受后的 exact I32 capture 和私有 flag 分派。
每处循环各有一个 guard；本次未合并跨 site 的 runtime checks。

检查安全、接受事实和拒绝运输分别证明。原 source execution 许可读取 header，
这是证明起点，不是 runtime 预执行。接受产生 count 和每个 reached access 的
resolution；静态 checked global-block separation 保持 header 稳定，没有新增
runtime alias test。Footprints/span 不单独证明 allocation 或 load permission。

完整链为 literal Clight → safe capture → source Loop → 实际 PolCert/Pluto 与
最终 candidate checker → lowered Clight → public I64 exits → scoped guarantee →
whole Clight → Csem→Asm。局部 source/model iff 是有限正常执行性质；独立的
raw-source progress 与既有 selected host 负责安装所需的进展义务。

公共出口精确保留未到达的内层计数器。初值 `(17,23,29)` 在正 N 下成为
`(96,96,29)`；零和负 N 下成为 `(0,23,29)`。负 N 走原程序回退。

## 实验与实际修复

第一份提取编译器能安装 identity，但 affine 模式只安装第一处：它沿用三层
循环的 `[1]` 见证，最终 checker 拒绝二维 interchange。逐 site 尝试 `[]`／`[0]`
解除这个实际 blocker；native 缓存相同 OpenScop 提议，见证重试不重复调用 Pluto。
同一个 marked region 中两处 source nest 分别改写，两份 identical marked
regions 安装四处，只调用两次外部调度。Identical unmarked 邻居保持原程序。

- 原 mvt 八项：affine、identity、unmarked、external refusal、reverse dependence、
  malformed schedule、负 N、零 N，全部符合安装预期并匹配 GCC modeled-state digest。
- Context／出口十四项：改名、改维度、多 marked、marked/unmarked、类型／资源拒绝、
  dynamic bounds、三个 public exits，以及缺少正确 coordinate witness，全部通过。
  错见证只安装第一处，拒绝真正 interchanged 的第二处。
- 旧 mxv／matmul-init 的六项 public-exit 检查及原 matmul 回归全部通过。
- 三次 GDB 在 unchanged assembly 上观测：普通／零 N 分别为两次接受、零次回退；
  负 N 为零次接受、两次回退。没有修改 source、compiler 或汇编加入探针。

十二个新 proof modules 共1,488行／55 audited endpoints，8 closed，490 reachable
sources；最大42 inherited globals，无新增公理。28次 proof attempts 包含12成功、
16失败。两份 native builds、三份失败 suite reports 和全部快照／日志保留。
第二份 context suite 的唯一失败是 memoization 将外部调用数从预期4降为2；四处
安装和 digest 已正确，后继测试修正了调用计数并增加错见证案例。

观察范围是 modeled scalar/array digest 与额外 public controls，不能替代定理的
完整语义结论。完整调用时长含初始化／digest，本阶段三个检查 suite 并行运行，
仅作小输入诊断，不作 profitability、单独 guard 成本或受控性能比较结论。

## 后续验收

继续实现其他原 source structures、多参数界限与实际 sequential tiling／ISS 等
配置，并随每项扩展连接到整程序证明。BT、LLVM/SPEC、candidate-derived scratch
数量和更一般见证政策、larger tiers／完整成本比较仍需完成。相继 site 的复用和
更多证明端点不能代替这些验收。
