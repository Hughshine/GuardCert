# 独立 bound pointer：完整证明连接，运行实现待验收

本阶段基于 `ac5f81a`。同步远端后，narrative 仍为 `7d94d810685a691efbf07df734f5fad8abfb4724`。遵守其职责边界：最小 kernel 不变，prefix／condition processing 属于上层库，具体 Clight host 负责程序安装。完整目标保持 active。

## 已经接通什么

源仍是二维参数化 affine 内层循环，真实数组读写，以及每次外层测试重新读取的 signed memory bound。保留源已有的 public snapshot。现在 bound pointer 可以独立于 body 使用的数组；不要求它属于 body pointer 列表，也不要求静态排除同一数组的逻辑单元 0。

新的条件依次执行 preparation、动态写地址分离、原候选 guard。拒绝时保留真正 repeated-load 源。检查比较每个实际源点的 word 写地址和 bound 地址；安全的不同 blocks 也可以接受，不能简化为数组 base 不相等。底层 `Mint32` 权限／对齐定理把地址不等接到 byte separation。

关键安全证明按源顺序推进：

1. 初始 retained load、真实 loaded 源完成和 preparation 接受，产生第 0 行的 prefix witness。
2. 已到达且活动的外层头部提供这一整行的真实执行。checked package 解码实际 body，取得该行每个写的权限 receipt，再向原 guard entry 运输权限。
3. 访问编码、机器范围和参数 word 证书证明这一行的仿射地址检查可求值；不要求未来行已经有效，也不预置 bound 稳定性。
4. 只有该行检查接受，才证明实际 stores 保持 bound load，并用剩余真实源执行产生下一行 witness。
5. preparation 的 count 上界证明 outer fuel 覆盖全部活动行；inner width 上界证明 row fuel 覆盖全部实际写。接受后得到完整写足迹分离，进而运输 repeated-load 源到 cached 源。

ghost 源执行只用于证明，不由 guard 执行。D 仍要求有限正常源完成，且不含未来 bound 稳定性。这不是一般无限源的局部协议，也没有新增 private snapshot 或依赖 preload。

## 实际代码与三方责任

| 责任 | 本次实际交付／复用 |
| --- | --- |
| 最小 kernel | 没有修改，没有新增语义接口 |
| 框架上层库 | 原 `ReadonlyPrefixScan`、readonly condition restriction／entailment／sequencing；两层扫描实际消费这些定理 |
| Clight 语言库 | 原 store 权限回运、已到达 row 取得、正结果推进 prefix、loaded→cached transport、实际分派、prefix/suffix contract、原 source-progress／table host 和 CompCert backend |
| Domain 实例 | `ClightAffinePreparedState/Footprints/Rows` 从 checked package 构造参数、范围、实际 point 值和精确 row decode；`ClightAffineLoadedPrefix/Stability` 填完该实例的 `DECODE`、`ROW_CHECK`、`PERMISSIONS`、`PRESERVE`，并证明 fuel coverage |
| 优化接入 | `ClightAffineDynamicLoadedCache/Rewrite/Syntax/Candidates` 绑定实际源、完整 guard 和原候选 checker；`ClightGuardedAffineDynamicLoadedCompiler` 复用语言 host，取得新 Csem→Asm backward simulation |

这些文件的命名和目录不是三层架构边界。没有为了 narrative 重排已有文件。这里复用的是具体已有证明；没有把新增模板、端点数或相似代码算作 proof burden 降低的证据。

新 source matcher 核对实际 AST、loop-control freshness、保留的 snapshot receipt、唯一 prefix 输出和 pointer binding 保护；metadata 与三类候选生产器继续不受信任。候选检查与公开坐标恢复沿用已有证书。新 compiler 的 theorem 覆盖其成功返回的程序，但提取／驱动绑定和实际 C 接受另有验收，不能由此自动推断。

## 验证边界

命令：`opam exec --root=/tmp/guard-opam --switch=guard -- make affine-dynamic-loaded-proof`。审计报告为 `build/affine-dynamic-loaded/proof/report.json`；编译整个选定依赖闭包时加 `--rebuild`，本阶段采用增量编译并核对所有选定对象相对 source/dependency 的时间及摘要。

审计通过 89 个端点，其中 17 个语言服务端点；580 个选定依赖、924 份 source 摘要。readonly prefix library 无全局假设，其余端点均未超出既有 CompCert／domain 基线，无新增全局公理。三个 compiler endpoints 均继承原 42 项基线假设。报告 SHA-256：`ba369f7960459a2337812d7af025dbf2ba93ab45612f838d9b9b5a50145dfbff`。

本阶段 normalized Clight fixtures 实际证明：独立 bound 源被新 selector 接受、旧静态 selector 拒绝它、缺 receipt／覆盖 bound pointer／把 bound pointer 用作 iterator 时拒绝。这些不是 C frontend、机器执行或性能证据。

原 loaded 和 cached compiler 作为独立 proof regressions；原两个 native 报告的 source/object/compiler-stamp 绑定重新核对通过，运行矩阵没有重执行。它们仍分别是此前的 1,650 和 891 次调用、各七个机器路径探针；不计作新的独立 bound pointer 运行证据。

## 运行实现暴露的问题与下一验收

直接的 `decision_bind` 会把后续行扫描接到当前行每一个成功出口。实际新 guard AST 的 fixture 在 column cap=3、每点一个写检查时得到：outer fuel=1／2／3 分别有 7／35／147 个测试；fuel=2 有 21 个接受出口。第三项仅统计 syntax，不能当作 row cap=2 package 的执行 coverage。这里统计的是实际 guard syntax，尚未测量运行时间或最终机器字节。

因此当前 tree-based compiler proof 不是可扩展的运行实现。已有 `shared_guard_statement` 可以共享 candidate/fallback，但它仍遍历展开后的 tree，不能据此声称已消除后续 scan 的复制。

下一必交付是保留 sequential/branching 结构的检查 plan 或嵌套循环 lowering：先证明它与已认证的检查短路顺序一致，再证明实际 private result/cursor 的公开 frame、checked-entry 运输和 defined dispatch，复用 host 安装。随后提取、绑定真实 frontend，并运行不同 blocks、同 block 不同 offsets、写中 bound 提前停、alias 后危险后续地址不被检查，以及 candidate/loaded-fallback 的机器路径。这些完成后才更新“可运行编译器”的能力。

依赖 preload／private snapshot、一般深层 affine 域、P4 性能和同例 related-work／作者负担对比继续在完整目标中。
