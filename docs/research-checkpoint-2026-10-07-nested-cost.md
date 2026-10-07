# 本轮 checkpoint：范围事实与完整调用成本

基线 `1aac569`，前一 goal turn 为 progress：已完成单份备用扫描、较大域验证、
稿件同步及 main push。本轮继续完整目标，未把 literal-word 类重定义为终点。

本轮有两项交付：

1. [已知 word 的 numeric facts](nested-numeric-word-facts.md)：纯数据 checker 和
   四个闭合定理，从实际 cache/row bindings 生产原 numeric flag 和 affine math
   domain。七个 fixtures 包括正确 `[1,17)` count profile 的 checked site、word=1/15、
   越界/wrap/空 count/未知参数拒绝。独立 34-endpoint/600-dependency/899-source
   audit；kernel 闭合、compiler 42-global baseline 保持，无新增 global axiom。
   没有修改生产 guard，也没有用静态 flag 替代实际执行 receipt。
2. [完整成本](nested-stability-cost.md)：30 轮、8 个输入、5 个版本，共 1,200
   fresh-process CPU batches，包含每次重置 aliased headers 和完整调用。每批前后
   核对全部数组、headers、公开 counters 和 markers，未对被计时汇编插桩。
   Guard-prefix decisions 另用 GCC diagnostic 统计，明确排除最后一次 dispatch。

同值独立输入 interchange：旧 scans-only 2,725.1ns、新版 1,503.4ns、source
909.9ns；新版仍约 1.65× source。非同值 6×8×5 输入约 5.91× source；负结果
完整保留。Same-word prefix decisions 4,673→17、header loads 均为 2；这是 prefix
计数，不能当作全部机器操作或 complete-program speedup。

成本核对纠正上一阶段计划：numeric 是 first-path 加 interval tree，并非逐 point
扫描。单数组 same-word 接受时 stability scan 被跳过、alias-only 为 `skip`，guard
工作已不随域大小增长；candidate traversal/public-exit 恢复仍有实际迭代成本。
公共出口责任属于实际候选/语言服务，不能由 kernel 消费更弱出口关系掩盖。

## 本轮可核对的证据

- Numeric proof report：
  `8f0dc06f7c6d578fc4c1fda2392f2218066c4e16b297d47773b2a57f43a94281`。
- Cost report：
  `8490f3a6a2a03fa197e7a9c782b91fa712cf0d243b70522bd653dc0f296d0542`。
- Runtime compiler 保持：
  `cf565f8f8374af84631e08878cb8f67ee56b44cd16ba884a0b2eae329a0d8a59`。
- 既有 native/large 报告通过成本脚本的源、objects、binary、artifact binding 复核；
  没有将计时数目当作新的源类/功能覆盖。
- 稿件/evidence-map 已更新，离线构建 17 页，无 undefined refs/citations 或 overfull
  boxes；新表首次需要的 cmr9/cmmi9 字体已缓存，随后离线重建通过。
  第 9/10/15 页实际渲染核对。最终 paper report：
  `1624e6c6c65d3b5defe670e353f177c1ee9cbdf2f92344e595f71ab000a22670`。

## 下一项与完整目标

`affine_multi_candidate_code` 目前在候选之后运行 `affine_shadow_source` 恢复公开
counters。已有 `affine_exit_statement` 能紧凑恢复出口，但其域不能未经证明用于
空 child 或一般 dependent bounds。下一项从实际 accepted rectangular nested
site 生产 exit-domain/frame，证明可替代 shadow traversal，接回原 candidate/host
证明与 compiler，复用本轮计时比较净效果。现在没有做成本归因或替代正确性声明。

非同值 stability、多数组 alias 的 compact footprint 条件、更广 affine source/
参数化基本域变换、动态布局/delinearization、完整 BT、作者负担与更广 OLO
kernel 对照仍未完成。完整 goal active；generic 最小 kernel 和三方责任边界保持。
