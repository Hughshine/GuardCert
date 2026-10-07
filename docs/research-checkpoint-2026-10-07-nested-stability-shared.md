# Checkpoint：单份 scan 与较大 same-word 域

2026-10-07，接续 `64232ee`。本轮完成有实际代码变化的 guard lowering、独立审计、
提取及运行验收；完整多面体目标 active，未缩减其范围。
使用、责任和困难详见 [单份扫描](nested-stability-shared.md)。

## 交付

新 language service 在两项都已定义为 int32 Boolean words 时证明 eager `Oand`。
Domain 用实际 cache bindings 建立这些前提，生成一份备用 scan；不改变
`ncs_word_or_scan_execution`／receipts／candidate preservation／语言 host 的接口。
不适用于后项读取仍需前项许可的 dependent checks。

独立 audit 为 23 endpoints／598 dependencies／897 source digests，compiler
保留既有 42-global baseline，kernel 闭合，零新增 global axiom。Language lemma
单独查询为四项既有 baseline assumptions，不把它描述为独立 closed kernel 定律。
Source static fixture 同时核对 word=15 的 typed BODY 和实际 site。

原矩阵：762 新 assembly calls／381 Clight dispatch calls，接受结果保持；
旧 scan-only binary 同输入对照为 127 assembly／127 Clight calls。四个真实汇编
alias probes、二十次局部工作量诊断通过。Constant-one identity／interchange／
tiling 的函数大小从 `(728,762,867)` 变为 `(611,644,755)` bytes。旧 double-scan
binary/report 摘要核对保留；旧报告不被当作当前修改源码的 proof 验收。

较大矩阵：literal15、count≤16、15 inputs、四配置 60 新 assembly calls，另有
15 旧 binary calls；三配置 45 Clight dispatch calls，各为 6 fast／9 refusal。
完整数组、headers、公开 counters 与 markers 相同。动态 header 改写使原域
增长到 16×16 的输入执行原源；模型逐步重读 header。
九个未修改汇编 probes 在独立／两种 header alias 下分别观察 source、interchange
与 2×3 tiling 的不同写序。十四次 diagnostic Clight calls 单列稳定性阶段工作：
大同值输入的 2,560 pointer comparisons 变为两次 cache comparisons；不同值
输入仍扫描。没有声称完整 guard 常数工作或 timing/profitability 收益。

## 当前摘要

| Report | SHA-256 |
|---|---|
| `build/nested-stability-shared/proof/report.json` | `9a9ed66634b07e1c3c40b56216d484c59ca682d224ec96baaa5298345b67e0b5` |
| `build/nested-stability-shared/native/report.json` | `51a91985ae4f11edb2ceeaeedfd29a342a4e5fe9975cf433b2200f3b1bde671f` |
| `build/nested-stability-shared/native/stability-probes/report.json` | `b93ac10fb052ed72438dddf01dea14e15c58589348a0b4d80decf5e808b6b8c4` |
| `build/nested-stability-shared/large/report.json` | `0d52b982dfcd94630231601f100fa321472f68e8cc712616ac02c4cf55d8b55c` |
| `build/paper/report.json` | `036679ba5ff3b59aa24cd18b04e55cffc0a778f7dfb384eb6cbaabf16baf6703` |

Current compiler SHA-256：
`cf565f8f8374af84631e08878cb8f67ee56b44cd16ba884a0b2eae329a0d8a59`。
`make -f scripts/nested_stability.mk validate` 在 pinned opam 环境通过，包含
proof、原矩阵、对照/probes 和较大矩阵的来源与产物复核。
旧 `1d3acc0` source-only reproduction readonly validate 仍通过；没有在本轮声称
新 compiler 已完成 empty-tree rebuild。Root Makefile 与前阶段复现 helpers 保持。

Manuscript、case-study/evaluation 和 evidence map 已同步，offline Tectonic
16 页，无 unresolved citation/reference 或 overfull boxes；第 9、14、15 页已
渲染检查。重新 fetch 的 narrative 分支仍为 `271f6fc`，正文与 main 无差异。
三方责任、四条链及 kernel cutoff 继续作为实现边界。

## 下一项

现有 numeric gate 在两次 word comparisons 之前仍执行；应从固定 cache facts
自动生产可检查的 range/footprint 充分条件，使真实运行避开已证明冗余的逐点
numeric work。可以先处理只含两个 cache parameters 的 package，保留其他
package 的既有检查；不得用新增语义回调补齐 BOOL⇒DOMAIN、读许可或模型运输。

关键接口分别是 `ncs_numeric_flag`、`ncs_numeric_flag_domain`、
`ncs_prepared_receipt` 以及 `ncs_prepared_temps`。静态 numeric flag 证明不等于
已有 receipt：后者同时包含 actual run、source transport、parameter domains 和
observers。新 guard 还需证明 ordered capture 的许可、private helper frame 和
模型入口到实际 guard exit 的关系，再复用候选及语言 host。

完整 guard／program cost、作者工作比较、更广 affine source／基本域变换及
动态布局／delinearization、完整 BT 适配仍继续。本阶段没有把 constant-word
实例重定义成完整目标。

## 后继成本核对更正

先前计划中的「逐点 numeric work」不是当前实现事实。Numeric code 为固定深度
first-path probe 与参数区间 tree；逐点工作是 stability／alias scans。单数组
same-word 快捷接受时这两个扫描均不执行。后继报告单列完整 guard 决策与程序
计时；本 checkpoint 的旧计数和报告摘要保持其原始实验范围。
