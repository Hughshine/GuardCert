# Narrative 澄清：literal-bound 接入中的证明责任

2026-10-07 再次 fetch `origin/topdown/research-positioning`，远端仍为
`271f6fc941910456da43a76e9f0eed38e8a5e200`，`paper-narrative.md` 和
`context-lifting.md` 与 main 相同。本页把其中的约束用于当前接入；不声称发现了
新的远端提交。前一轮综合核对见 [narrative implementation check](narrative-implementation-check-2026-10-07.md)。

## 具体问题与接口

实际源的第三层是 `for(k=0;k<5;k++)`，既有 tensor factory 接受临时变量上界。
将 `5` 在 AST 中替换为 fresh helper 只解决语法：原入口的 helper 尚未初始化，
模型入口、检查出口和继续执行的实际状态也不相同。这里必须生产执行证明。

新增 chooser 仅提出一个 int32 literal，既有 descriptor 和 candidate 仍是数据
提案。语言 mapper 仅改精确匹配的 typed signed comparison，保留地址、RHS 和
store 语法。框架不搜索片段或推断任意 source/candidate 的前提。独立查验器核对
实际 canonical AST、metadata、profile、namespace 和候选。

## 三方归属与四条链

| 责任方 | 本例提供的设施／证据 | 代码位置 |
| --- | --- | --- |
| Framework kernel | 从实际 check certificate 与 conditional preservation 得到局部 guarded preservation | 既有 `GuardInterface.guardify_preservation`；新接入经 `materialized_preserving_region_contract` 消费它 |
| Clight 语言库 | 真正的 helper 赋值，原程序到已准备程序的执行运输，private frame，实际 dispatch；progress、typed allocation 和 continuation 安装 | 新 `ClightLiteralBoundPreparation`；既有 materialized check／preservation 与 `ClightExpressionRegionHost` |
| Tensor domain | 原完成执行提供 canonical source-definedness；完整 guard 取得模型前提；检查后入口到候选真实执行与公开出口 | 新 `ClightTensorLiteralPreservation`；复用原 tensor package／guard／candidate proofs |
| 优化策略与 site | 选择 literal、维度／访问／profile、候选和位置；提交数据交查验器，host 查验原源 progress 和 private pool | 新 `ClightTensorLiteralCompiler` 与不受信任 native policy |

Domain 库和具体 site 策略都归优化实现方；表中分列的是复用库与一次使用的
不同角色，并未增加第四个证明责任方。

四条链仍是逻辑分解，使用者不填写四份语义 callback。`C_derive` 生产 canonical
source 许可与模型义务；`C_guard` 证明初始化及检查实际执行、安全、接受 soundness
和 frame；`C_opt` 复用既有候选 checker 并补齐实际状态到候选的连接；`C_host`
由 materialized choice realization 和随后独立的语言 installation theorem 交付。

## 最难的连接如何处理

Check prefix 先执行 `helper := upper`，再执行共享 Boolean 检查。安全域取原源的
silent normal completion，不假设优化前提已经成立。公开 ports 包含原源及 guard
所读的公开 temps，排除 private helper 和 Boolean；所有 memory 保持。

逻辑前提锚定在 prepared original entry，而非假装原入口已含 helper word。局部
候选先重新初始化 helper，再调用既有 tensor branch。这使局部规则可以消费任意
满足公开 ports agreement 的实际检查后状态，而不把 helper 定义性偷偷添加到
公共 frame。拒绝分支保留原 AST，继续执行原 literal test。私有写入由语言 frame
和 freshness 证明保护；它不是 raw whole-state identity，也不是用户可见副作用。

实际安装采用 expression-progress host，因为旧 temp-bound host 拒绝 literal
子循环。源有限进展、placement、scope 和资源仍分别查验；局部完成 theorem
不能直接代替整个程序入口的进展证明。Kernel 无须修改，也不为此增加任意
contract-clause algebra。

## 验收与后续顺序

新语言、领域、编译器与 fixture 已完成编译。独立208端点／440依赖审计和提取
通过，无新增全局公理；真实C八配置1,152次完整汇编调用、432次独立Clight
观察通过，覆盖两种地址次序、literal 3／5／0／6、重复site及goto／memory
上下文。[完整阶段证据](tensor-literal-bound.md)分别记录proof、真实运行、
code bytes和未测成本，不把调用数当作通用性或收益。约定子集已闭合并同步
论文与证据；加载
`grid[0]`／`grid[1]+1` 与动态 Horner layout 的实际组合仍是下一功能项，不能把
固定布局 loaded 证据和这里的 tensor 证据相加称完整 BT。更广 body、cross-tensor
alias、affine domains、代表性成本和比较作者工时继续独立验收。
