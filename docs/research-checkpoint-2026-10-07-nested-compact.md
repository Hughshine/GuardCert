# 本轮 checkpoint：精确出口、实际候选与成本对照

基线 `c83f365`。本轮继续完整多面体目标；重新 fetch narrative 分支，仍为
`271f6fc`，`paper-narrative.md` 和 `context-lifting.md` 与 main 正文一致。

已交付的功能见 [紧凑公开出口](nested-compact-exit.md)。此前 guard 已可在
same-word 单数组路径跳过域扫描，但候选结束后仍用 shadow loops 恢复公开
counter。这轮在已有 accepted uniform nested 模型上证明五个 temp 赋值取得
实际 source 的精确出口，消费实际检查后 entry 的 cache frame，并接到新的
data-only factory、local preservation、projected region 和 Csem→Asm compiler。

语言库交付幂等 control BODY 循环执行以及 fixed patch 的 lookup、交换、frame。
Domain 从 existing model anchor 和 actual source execution 推出 int32 words、
root 活跃、child 正计数，实例化三层定律。实际 component count 的正性来自
static site。空循环保持 fallback，不能无条件改写 child counter。Kernel、guard
及 host 不改；memory validator/lowering 复用，candidate exit 对应新增。
具体 site 使用者继续提交既有数据，没有新 source/exit 语义回调。

## 已通过的验证

- 新 proof：42 endpoints、606 required dependencies、905 bound sources；
  kernel 闭合，完整 compiler 42-global baseline 保持，无新增 global axiom。
  报告 `7446909a2cd059f47b98b59eaacd3ab0d2d8510887fca6de3fcf1b01b926370e`。
- 新 compiler：提取成功，binary
  `7cd55f3379f40e3b6a324554077c44ff24abf535dcb3b18d6d044a61b6cb7529`。
- 原矩阵：762 assembly calls、381 Clight dispatch calls，通过全部数组、
  headers、公开 exits 和 context markers 核对；重复 sites、拒绝和早退出保留。
  报告 `59090ec1155d4ee4fbf6bae08e86aa4d825f6501b73a3acd7a1b05153e02a879`。
- 较大域：60 new assembly calls、45 Clight calls、九个未修改汇编 probes；
  source/interchange/tiling 写序及两项 header alias 下的公开出口得到区分。
  报告 `2606062b1320944df1fecd1ae91b0e5f78a59a54946f5e26adcd36b95f2422d8`。
- Kernel bytes：source 161，identity/interchange/tiling 为 587/626/719，
  前一版为 611/644/755；这个变化不单独构成优化收益证据。

完整成本使用另一独立目录，与相同 guard 的前一版 shadow compiler 和 source
配对。它核对所有 guard-prefix decisions/loads 相同，保留原源 fallback、header
reset、完整数组核对、30 轮 randomized CPU batches；正式采样不与 proof/build
重叠。[完整报告](nested-compact-cost.md)已通过，hash
`540f83698417f637a8b35ddf9198322f30becf04833a9e80b5010d21513f294a`。
同值独立 interchange 由配对 shadow 的 1,521.1ns 降至 1,229.8ns，仍约为
source 的 1.35×；identity 约为 source 的 0.88×。非同值 interchange/tile
仍为 source 的约 5.73×/7.65×；公开退出恢复简化没有为重排取得一般净收益。
回退布局变化也影响计时，不把完整差值等同于纯 shadow 的 CPU 成本。

稿件、evidence-map 和当前计划已同步。LNCS manuscript 离线构建为 18 页，
无 undefined refs/citations 或 overfull boxes；第 10/16/17 页实际渲染核对了
出口证明段落及两份独立成本表。旧 source-only Makefile 和四份绑定 helpers
保持，本阶段使用独立 proof/native/cost 目录及命令入口。

## 下一项和范围

继续非同值 stability／多数组 alias 的 compact footprint 条件、更广 affine
source 和参数化域变换、动态布局／delinearization 与完整 BT。并建立语言库、
domain 实现和具体 site 作者需交付的共同例子对照。当前五赋值定理不支持任意
dependent child last-path，不是一般 exit synthesizer；新 compiler 的 source-only
fresh rebuild 仍需独立验收。此前 empty-tree 重现属于旧阶段。

这是一项活动目标中的进展；完整目标未结束。论文同时维护，不将 C_host 的
语言安装义务计入最小 kernel，也不把 callback 类型或计时调用数当作功能覆盖。
