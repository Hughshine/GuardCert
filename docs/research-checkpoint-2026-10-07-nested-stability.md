# Checkpoint：same-word 条件接入完整 compiler

2026-10-07，接续 `ee8b9b7` 的局部 producer。完整多面体目标保持 active；本阶段
完成 guard 替换、实际安装和限定范围验收，不代表完整 PolCert／BT 能力。
使用与证明详见 [same-word compiler](nested-stability-compiler.md)。

## Narrative 澄清的吸收

本轮重新 fetch 并阅读 `origin/topdown/research-positioning` 的
`docs/topdown/paper-narrative.md`：远端仍为
`271f6fc941910456da43a76e9f0eed38e8a5e200`，main 正文无差异。
没有改写评审分支；澄清落实在实现、责任表、当前计划和实际 manuscript 中：

- 最小 kernel 止于 local guarded correctness；条件处理在上层库，整程序
  installation 由语言 host 与具体 region／site 证据完成。
- 三方证明归属与四条逻辑链分开描述；新条件须实际生产模型义务及入口运输，
  不增加通用 assumption extractor，也不以使用者语义回调填补困难。
- 当前约定 scope 的证明链先闭合；随后替换稳定性 guard，并直接复用原
  candidate certificate／kernel／host。新的接受集合无需等同旧集合。
- 代码大小、checking work、useful acceptance 单列。局部计数不代表完整
  guard cost，代码增长也不被包装为性能收益。更广条件和作者工作仍须验收。

## 实现和实际结果

七个新 Rocq 模块提供静态 word proposal 检查、physical receipt、multi adapter、
guard certificate、preservation／frontend region contract、typed factory、新
Csem→Asm entry 及 fixtures。短条件成立跳过原 stability scan；不成立保留 scan；
未支持 BODY 保留原 guard AST。候选正确性复用原 `ncs_multi_local_certificate`。

独立 audit 查询 19 endpoints，编译 597 required dependencies，绑定 896 source
digests；kernel 闭合，compiler 仍为独立查询的既有 42-global baseline，零新增
global axiom。当前工作树已完成 extraction／OCaml build；没有在本阶段声称
从新 empty tree 重建这个新入口。

新矩阵：762 assembly calls、381 Clight dispatch calls；完整数组、双 headers、
public counters 与 context markers 对照通过。另用摘要核对的旧 binary 对同一
source 执行 127 assembly／127 Clight calls。Interchange 的 fast dispatch 为
49→51，refusal 为 77→75，矩阵内未丢失既有接受。

四个 GDB probes 观察未修改汇编：两个同值 header/data alias layouts 的写序
从 source 的 `4,9,80` 变为 interchange 的 `4,80,9`，公开出口 `(2,2,5)` 保持。
这些是独立于完整数组矩阵的实际路径验证；不借该小域写序区分 2×3 tiling。

另二十个 instrumented Clight calls 对照稳定性工作：独立双 header 同为 1 时，
header pointer comparisons 40→0，加两次 cache equalities；两个 alias layouts
分别 10→0／20→0，加两次 cache equalities。条件不成立的输入保留旧 scan。
旧 scan 在整个五次 store BODY 后检查 refusal，计数按实际代码而非理想早停。
同 source 的 interchange 函数 613→762 bytes，当前降低方式包含两份备用 scan。
没有完整 guard timing、program speedup 或 profitability 结论。

## 独立绑定和回归

| 证据 | SHA-256 |
|---|---|
| `build/nested-stability/proof/report.json` | `fd70c4022b5c3db489ebeedd0643d536368ab8c5910ce16879ea2017e8ebda7b` |
| `build/nested-stability/native/report.json` | `3e1743c280a596ad1563d2532e90e477691c6287268f58357060200cdca2ab7f` |
| `build/nested-stability/native/stability-probes/report.json` | `b367e2b5ff1b5eea741d7f3d9c78a4cab98956a7740a7b45a4b0d5fda3842414` |
| `build/paper/report.json` | `e02b0bf474dbe9447f6bb2496c8f1e6eea71b9e9e41d7d651a69de3b5a8fc7fc` |

`make -f scripts/nested_stability.mk validate` 在 pinned opam 环境通过。
新 reports 分别核对 sources、objects、helpers、compiler、输出及 probe artifacts。
独立 makefile 保持前阶段 root Makefile 的复现摘要不变。

旧 frontend coverage 的当前摘要验证也通过，report 为
`9330c60bb3a1b51bfc785d80248747203fcd2f81ecc6f5dab562e2762705d6e2`；
此处是已有产物复核，不称作重新执行旧矩阵。
原 `1d3acc0` empty-tree source-only reproduction 重新 readonly validate 通过，
report `e7e7b1422f84825f7731c72f59551e835d5e62d3940e553a923eaa92587d4afa`。
它证明此前入口的独立复现，不能自动推广到新 compiler。

前一 word/model stage 同日独立重新查询后，22 endpoints／508 dependencies／6 项
baseline 保持，当前 report 为
`4f7b40a60fca5705682721919cef435e8553db5b59ee5e9f85e3b1544d1f047d`；
seven-endpoint word observation report 摘要保持。新的 compiler audit 另行独立，
未以这些历史 proof reports 为输入。

实际 case-study／evaluation／evidence map 已同步；offline Tectonic 编译 15 页，
无 unresolved references／citations 或 overfull boxes，已渲染检查第 9、13、14 页。
PDF 是工作稿，不是最终投稿就绪主张。

## 下一项

保持 source／candidate proofs，优先消除备用 scan 的代码重复，并检验更广
range／footprint／same-value 条件。分别测完整 guard／program cost、代码大小与
接受域，并记录 kernel、语言实例、优化实现者各自的数据／证明／手工责任。
更多 affine source classes、一般参数域变换、动态布局／delinearization 和完整
BT 适配继续推进；本阶段不将 narrow constant-word condition 当作全部 OLO 验收。
