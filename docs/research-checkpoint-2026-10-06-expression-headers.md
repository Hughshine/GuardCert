# 表达式 header 的 capture、前缀与缓存运输

本阶段的父提交为 `50ec27c`。再次 fetch 后 narrative 仍为 `226ba94`，main 正文一致。
新增服务放在 Clight language library 与 affine numeric client；最小 kernel 和现有 candidate
validator 没有修改。使用步骤、输入义务和困难位置见 [接口 walkthrough](expression-header-services.md)。

## 已完成的证明

七个新 `.v` 提供 signed-expression header 的成功求值事实、第一次实际 header 与安全
private capture、第一次真实 body receipt，以及保留原 compound header 的 source transport。
这些证明不要求未来 observation stability，也不要求 cached source 先完成。

`ClightExpressionBodyPrefix` 将源许可前缀推广到任意 structured body 和一组 memory
observations，不再把 raw load 等同于 computed cache。它生产当前真实 body 的 receipt，
只在 body observation-preservation check 接受后推进，消费已有 readonly prefix algebra。
`ClightExpressionBodyTransport` 在全部所需 body 保持观察后，从原 source 推出相同出口的
cached source；body-preservation、protected writes 和 HEADER 对应是明确的实例义务。

`ClightLoadedOffsetHeader` 实例化 `*limit + delta`，按实际 `Int.add` 关联 raw word 和 cache，
包括机器回绕。`ClightExpressionAffineNumericSite` 核对真实 source／bound／private cache，
复用现有递归 affine numeric guard，并从真实第一 body 取得数值检查可用性。
这只是第一检查阶段，尚不是完整 guarded candidate rule。

## 实例与验证

静态计算 fixtures 接受三层 canonical affine body 的 load＋1 numeric descriptor；错误 delta、
pointer、unsigned header 和公开 cache 被拒绝。实际 Clight 检查证明覆盖 `raw=-1` 得到零，
以及 `INT_MAX+1` 得到 `INT_MIN` 的空域：检查正常返回 false，memory／公开 temps 保持，
未初始化的 child 参数与 body pointer 保持 undefined。这些是语义执行证明，不是新 native
矩阵；有效第一次 load 作为这些空域实例的输入事实。

另一个具体 CompCert allocation/store/load 例把 bound 从 2 写成 1。虽然入口 cache 为 3，
真实 repeated-load-plus-one 源只执行两轮；第一 store 后 raw observation 改变的证明已闭合。
这检验了捕获值与稳定性义务的区别，没有声称新的完整 alias guard 已安装。

`make expression-header-proof` 通过：**43 端点／548 实际依赖／1,030 source 摘要**，其中
24 个 language、2 个 numeric-domain、17 个 fixture 端点。新增端点最多六项原 CompCert
全局假设，没有增加公理；接口中的 HEADER／body check 等证明参数仍须实例化，这个计数
不消除它们。原完整 loaded-affine compiler 回归保持 42 项假设，kernel 无全局假设。

独立报告为 `build/expression-headers/proof/report.json`，SHA-256：
`afe33983bfe3e8c97f82ce35e362270605116ca77ff13c2b14a98498f4c19b7b`。
它绑定新 source／object、审计 source／object／log、helpers 和工具链，并核对原 reduced
报告所有 source／object 保持。548 是本阶段所选模块及旧 compiler 的实际依赖闭包，
不与父报告包含额外回归模块的 694 个依赖相加。

`make expression-header-validate loaded-affine-multi-validate` 通过，复核本阶段证明绑定与原
compiler/native、Figure 2 和 guard-work 产物；未重跑旧矩阵。命令基于现存已验证的 reduced
报告及依赖对象，空 build 的独立 bootstrap 尚未验收。

原 reduced proof/build/native 报告、extracted compiler 和二进制没有重写。本阶段没有新的
compiler entrypoint、extraction、native 优化、timing 或作者负担比较；Figure 2 的完整源仍
记录为 optimizer unsupported，之前 16 次原源调用不改算成本阶段的优化运行结果。

## 接入责任与下一步

1. Recursive domain 要把新的 prefix receipt 接到现有真实 body decode、write trace coverage
   和 cursor separation，使 body-check 接受实际推出全部 raw observations 保持；同时关闭
   cap/fuel 对实际源轮次的覆盖。
2. 原入口／checked-entry relation 要保留 computed cache 与 raw observation 的关系，并运输
   已接受 numeric facts。不能沿用旧 `raw load = cache` snapshot，也不能用 cached completion
   许可稳定性检查。
3. Factory／typed host 要绑定真实 expression AST，分配 private cache/cursors，消费 source
   progress、scope 和 placement，并重新接 candidate 与完整 Csem→Asm 端点及提取运行。
4. 再把第二 loaded child 的 reached capture、读许可与观察保持接到同一三层 package。
   已支持源的 compact write-vs-observation sufficient conditions 与 guard 工作量改进继续是
   验收要求；本阶段没有消除此前测得的 46／6,394 次 pointer comparisons。

完整目标继续 active，不把服务、参数或静态 descriptor 接受计成最终多面体覆盖或自动化收益。
