# 去重条件服务：复用同一 factory 与整程序证明

2026-10-08。前一阶段是 [source-licensed scan services](source-licensed-scan-services.md)。
本阶段实现第三个已证明的服务；kernel、候选 checker、loaded-region
contract 和语言 installation 定理保持原实现。一般 affine domains、
完整 OLO 功能和收益验收仍属于 active goal。

## 做什么，以及如何使用

对于两个赋值，原 instruction templates 可以包含 `[A,B,B,A]`。原扫描
在每个 canonical point pair 上生成 16 个 access-pair tests。严格去重后
只保留两种模板，生成四个 tests。相同 root 的恒真 tests 仍存在；本阶段
没有新增常量消除或首次拒绝停止。

去重比较数组 root 和完整 affine map 的语法相等。不同 root、不同系数
或不同常数偏移不会合并。`nodup` 保留最后的重复项；改变顺序不会改变
全体 pair checks 的 Boolean 规范，也不移动任何检查到 source 未许可的
坐标。Eligibility 仍检查原模板的严格 uniform maps 与原 cap；不匹配时
安装原 point-pair scan。因此非 uniform 输入仍可使用原候选优化。

源码用户给标注 C、scheduler／tiling 选项，可通过
`GUARDCERT_ALIAS_SCAN=dedup` 选择此服务；本阶段 compiler 默认值为 `dedup`。
同一 binary 也注册 `canonical` 和 `pair`。Marker 只请求尝试；原 static
checker、runtime fallback 和公开 iterator restore 继续适用。不能把任意
OCaml callback 注册成条件证明。

新模板处理服务的作者可复用 `processed_template_prepared_scan`：提供
处理后的模板列表及 `access_templates_equivalent` 的证明，使用原 checked
allocator。该适配器负责许可、machine execution、frame 与 entry fact。
这种成员保持的子接口只适用于保留模板集合的处理；其他充分条件服务仍须
提供 `source_licensed_scan` 所要求的安全执行和接受充分性证明。

## 验证责任与实际复用

| 责任 | 本阶段生产者 | 沿用的证明 |
| --- | --- | --- |
| Template 集合保持、point／canonical Boolean 规范精确 | `GuardMemoryAccessTemplateDedup.v` | 原 pair-check 与 difference-domain 定义 |
| 原 source 许可剩余访问，实际 Clight scan、memory／public／ports frame | `processed_template_service_execution` | 原 source/model decode、permission receipts、canonical scanner execution |
| Typed/fresh cursors、flag 和候选 scratch pool | `deduplicated_scan_builder` | 原 `canonical_package_allocate`；二维仍保留九 scan slots |
| Candidate／fallback 及公开出口 | 原共用 factory | `check_scan_service_full_execution` |
| Loaded source、site requirement 与整程序安装 | 原共用 loaded host／compiler | 原 projected contract、selection、scope、progress 和 backend 证明 |
| Csem→Asm 专门端点 | `ClightSelectedDeduplicatedScanCompiler.v` | 一行实例化原 compiler 正确性定理 |

检查许可消费原 source 的一次完成执行、原 setup 接受和入口 ports agreement。
它不自动生产 source progress 或任意 context 的安装证据。Private cursors／
flag 可以改变，memory 保持且公开 temps 被 frame；不是完整状态相等的
readonly 条件。

本阶段三个新模块共 308 行：domain 102 行，语言适配器 185 行，compiler
实例化 21 行，均包括 imports、注释和 audit queries。没有复制 factory、
loaded installation 或 backend proof body。语言适配器的证明与 domain
去重证明仍是新增工作；行数和实例化情况不是作者时间测量。通用服务接口
只导出 accepted entry fact；domain 的 Boolean 精确性与该接口要求区分。
本阶段不另声称有限 pool 下所有静态 installation 接受域相同。

## 已取得的证据

`build/deduplicated-scan/proof-v1/report.json` 查询 11 个端点，7 个闭合，
语言端点依赖六项旧 globals，整程序端点最多 42 项。1,414 个可达绑定与
冻结 parent 的 1,414 个绑定分别核对；无新增公理。仅编译三个新模块，
成功 snapshots 与失败日志保留，原 `.v`／`.vo` 不重编或覆盖。

提取 compiler：`build/deduplicated-scan/compiler-v1/ccomp`。
正常矩阵通过 1,000 次未插桩 Asm 和独立 1,000 次 Clight 检查；非 uniform
矩阵通过 180／180。比较完整 1,024-word arena、公开出口、初始 iterator
与实际路径。真实 rank-2 Pluto／prepared codegen 仍提出候选，完整 checker
重检；单位／部分单位 tiles、row／column、参数 stride、实际调度、重复标注、
continuation、两层 runtime refusal、空域、未标注与失败 scheduler 均覆盖。
非 uniform dump 不含 difference-bound assignments，确认实际安装旧 scan。

新配对成本准备通过 243 次重复 Asm 全输出检查和 81 次独立 Clight 诊断。
同一新 compiler 分别运行 disabled source、`canonical` 和 `dedup`，相同
source／phase options；每种优化 mode 各安装一个真实 site。诊断如下：

| Profile | 2×3 总 guard tests：canonical→dedup | 8×8 总 guard tests：canonical→dedup | Linked kernel bytes：canonical→dedup |
| --- | --- | --- | --- |
| Row | 361→181 | 4,741→2,041 | 1,349→1,325 |
| Column | 361→181 | 4,741→2,041 | 1,353→1,323 |
| Parameter stride | 363→183 | 4,743→2,043 | 1,543→1,473 |

Setup counts、dispatch paths 和完整输出保持。计数来自单独 GCC 执行的 printed
Clight instrumentation，不是 assembly operations、CPU cycles 或收益结论。

完整 CPU 测量在新 `build/deduplicated-scan/cost-v1` checkpoint 完成，
共 2,430 batches，全部 warmup／final 全输出匹配。计入 header reset、
capture、全部 guard、candidate／fallback 和公开恢复；array initialization、
printing／validation 在计时外。30 随机配对轮、fresh process、CPU 0 affinity、
各 mode 独立 calibration、C process CPU clock；最短 batch 0.095863 秒，
没有删去样本。环境为 AMD Ryzen 7 7800X3D／WSL2，无 core isolation 或
confidence interval，不代表 workload frequencies 或一般性能。

下表每格是 median paired `dedup/source`；并非 guard-only 时间：

| Input | Row | Column | Parameter stride |
| --- | --- | --- | --- |
| 2×3 accepted | 5.369693 | 5.623490 | 5.537515 |
| 8×8 accepted | 12.480688 | 11.964781 | 14.543850 |
| RHS word wrap | 6.218795 | 6.568021 | 6.093418 |
| Array alias refusal | 4.171967 | 4.211919 | 4.898851 |
| Start refusal | 1.009866 | 0.998765 | 1.312997 |
| Header alias refusal | 1.118733 | 1.121938 | 1.084713 |
| Cap refusal | 1.527384 | 1.577889 | 2.263176 |
| Outer empty | 1.303407 | 1.299130 | 1.301444 |
| Child empty | 1.499861 | 1.525060 | 1.467072 |

相对本次配对的 canonical mode，2×3 接受减少 12.64%–24.15%，8×8
接受减少 15.37%–27.81%。接受路径仍明显慢于 source。26/27 profile/input
medians 大于 source；column start refusal 的 0.998765 是约 0.12% 的描述性
差异，且不执行候选，不把它当作优化盈利证据。

小幅回归也保留：row／column child-empty 相对 canonical 分别增加
2.10%／2.09%，row header-alias refusal 增加 1.34%。没有统计显著性推断。
Printed Clight tests 的下降大于 CPU 成本下降；完整测量不能单独将时间
归因于 header、坐标、alias tests 或 candidate，需要进一步分项诊断。

科学图导出在 `build/deduplicated-scan/cost-plot-v1`，包含 PDF／SVG／PNG。
论文使用新 `paper/figures/deduplicated-alias-cost.pdf`；旧图不覆盖。

## 冻结报告与重现命令

| Artifact | SHA-256 |
| --- | --- |
| Proof report | `d2180f7e3102ee9ce6b4a465587cdff79193dabe0a38540838e4b4dbd233c532` |
| Compiler | `abac2e3b34d92c76888bcc49938d63768adff093e96e353b871cb70b00283262` |
| Normal native report | `487dd04f622876bcf053620d80320cac28ac1a996c38a2970b58b03cd2b1b26d` |
| Nonuniform native report | `02332af0b11bb2bb98e5ebfbd17c9899ea471a29a78f4351e58545e653cf09fd` |
| Prepared cost report | `043d650276454300404ebebb9f2a9851f4ded0be7034d87f6740d972a37842d1` |
| Timing report | `fa9ebe4feb82f2f23dbc4dc5cf4f02a28aea519cf38e076e03e8807175e2a9de` |
| Plot report | `f8d589c1807cecf1b480dbeed0d57b87d4a7a34506e37a52a83f84de690541bd` |

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_deduplicated_scan.py --validate
python3 scripts/native_deduplicated_scan.py --validate
python3 scripts/native_deduplicated_scan_nonuniform.py --validate
python3 scripts/prepare_deduplicated_scan_cost.py --validate
python3 scripts/measure_deduplicated_scan_cost.py --validate
python3 scripts/plot_deduplicated_scan_cost.py --validate
```

构建与新实验 helpers 拒绝覆盖既有 checkpoints。新的支持条件仍须证明安全、
充分性和 actual-exit transport；不能用 hidden same-block 假定缩短检查。
