# 已有工作接口补核：Chamois 与 Peek

2026-10-06。此记录补充 [cf4d442 的历史证据矩阵](evidence-to-claim-2026-10-05.md)，不改写旧评审的时间边界。主张继续采用 [topdown narrative](topdown/paper-narrative.md) 的三方责任与四张证书。下面核对的是一手论文／公开接口；未编译这些外部 artifacts。

## Chamois：不受信任 oracle 与实际 CFG 扩展

已取得此前未能读取的 [BTL_BlockOptimizer API](https://certicompil.gricad-pages.univ-grenoble-alpes.fr/Chamois-CompCert/html/ocaml/BTL_BlockOptimizer.html)。`btl_expansions_oracle` 和 `btl_scheduling_oracle` 返回 block map、function info 与 invariants；lazy-code／store-motion 等接口返回 CFG 与 gluemap，各自还暴露 rewrite rule sets。这关闭了“未看到 oracle 签名”的未知项；签名本身不证明动态条件生成器的能力或缺席。

[BTL_ExpanseMemcpy](https://certicompil.gricad-pages.univ-grenoble-alpes.fr/Chamois-CompCert/html/compcert.arm.BTL_ExpanseMemcpy.html) 将首条 `Bmemcpy` 展开为 prologue／loop／epilogue CFG，用 XP monad 分配 fresh registers 和 program counters。`check_chk` 核对 cpychunk 的静态描述；是否展开成 loop 由静态 trip count 和阈值决定。生成 loop 的指针比较是运行时控制，不能据此把该转换描述成“合成入口 guard，失败时保留原操作”的版本化优化。

[对应 proof module](https://certicompil.gricad-pages.univ-grenoble-alpes.fr/Chamois-CompCert/html/compcert.arm.BTL_ExpanseMemcpyproof.html) 实例化 `BTL_Expansion`：`basic_simu` 从真实 block 执行得到扩展执行，并保持源寄存器 agreement；`run_expanse_iblocks_loop` 覆盖引入的循环。由此可确认“新增 CFG／私有寄存器＋局部模拟设施”已有先例。对 GuardCert 的推论是：这些设施必须比较，不能单独作为 novelty；该文件尚不能回答通用安全 guard 编码与 `B⇒A` 推导的比较。

另发现作者发布的 [EMSOFT 2026 memory-copy artifact](https://zenodo.org/records/22083398)。尚未核对对应论文的完整算法和证书，不能将 artifact 标题当作 dynamic guard 的证据；列为下一轮一手材料核对。

## Peek：local-to-program 本来就是其核心服务

[PLDI 2016 原论文](https://darzu.io/files/pldi2016.pdf) §3–4 的规则作者提供局部模拟与 source normalization；引擎通过入口／出口 liveness 连接完整程序。论文的全局证明还要求等长替换、源末条不是 label，并排除 call／return。默认 normalization measure 支持无回跳的 source；论文讨论由优化作者提供 measure 扩展回跳。这些是实际责任和能力，不支持“汇编 peephole 不涉及 context”或“它绝不可能表达条件分支”的表述。

我们的比较任务是相同 source／candidate／D／P 下，需要由规则作者、语言实例和框架分别补哪些证明。Peek 提供的是局部模拟与 liveness 宿主；GuardCert 当前复用 condition 编码／分派和 CompCert host。但只加入一个 if 或换成 C 层不构成增量。需要分别比较 guard 观察安全、机器算术、私有检查 state、`B⇒A`、source 进展和 code growth。尚未完成同例 artifact 实例化，不声称 Peek 不能实现这些例子，也不声称 GuardCert 已降低其作者证明负担。

## 吸收进当前工作

1. related-work 比较采用可核对的实际接口；保留未知项，不从名称判断表达力。
2. P2 pointer 迁移先关闭检查后状态、前提锚点和 exact dispatch；Chamois 的 fresh-resource／CFG 扩展与 Peek 的 liveness／normalization 是对照项。
3. P3／P4 独立评价领域推导算法、作者负担和实际成本；这三项不能由 kernel composition 或完整编译端点的存在推出。

当前功能证据与后续验收以 [当前计划](current-work-plan.md)、[责任矩阵](framework-responsibilities.md) 为准。
