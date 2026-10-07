# CAV 2027 并行写作：首份可编译稿件

2026-10-06。重新 fetch 后 narrative 更新到 `271f6fc`，新增 CAV 2027 目标与
“实现同时写论文”的具体首项交付。main 导入了该段澄清，并保持原 proof-first
完整功能目标 active；没有将 paper skeleton 或语言 helper 当作功能验收结束。

## 实际交付

新建 [paper/](../paper/README.md)，包含实际 LNCS sections：

- Introduction：源／候选、语义前提 A、入口条件 B、可执行 guard G；检查安全
  与模型成立之间的循环依赖；三方责任和当前研究问题。
- Framework：照实际 `GuardInterface.v` 定义给出 check 后状态、accepted/refused
  entry relations、soundness、安全和存在性；分别写 refinement／preservation。
  whole-program lifting 归语言 host；readonly／prefix／condition 库在 kernel 上层。
- Related work：OLO、COVE/cSTOKE、CoreJIT／后续 effectful JIT、Peek、Chamois。
  正面写已有能力，保留 artifact 同例比较未知项，不声称对方缺少未核实能力。
- Case study：当前 loaded-root＋offset 完整编译路径，原 Figure 2 适配源的真实
  覆盖缺口，以及本阶段 private helper／constant-body 权限桥。
- Evaluation 和 conclusion：已有审计／运行证据与待执行的 acceptance、成本、
  条件生成及作者负担比较；未知结果以红色 `Pending evidence` 标注。

[evidence-map.json](../paper/evidence-map.json) 逐节列源码／定理、阶段文档和一手
文献范围。builder 核对 anchors／official template digests，报告同时绑定其实际
源码和文档摘要。它不把 anchor 的存在当作已完成新 proof 或运行；Rocq 的验证
来自相应 stage audit。paper 中既有 native 数量是已绑定的历史运行，没有重跑
矩阵，没有新 timing、speedup 或 comparative author-effort 数字。

本次 OLO、COVE、CoreJIT、Peek、CompCert 作者论文和 Chamois 作者海报／memcpy
proof API 已直接刷新。Chamois oracle API 本次访问仍失败；先前取得的接口事实
保留其旧来源，不把本次失败当作能力否定。未编译这些 external artifacts。

## 构建与检查

使用 Springer 官方未修改的 `llncs.cls`／`splncs04.bst`，Tectonic 0.15.0，
`--untrusted`、两个额外 TeX passes，以及 Poppler。模板与 binary 的来源／摘要
见 paper README 和 evidence map。

```sh
python3 scripts/build_paper.py --engine /tmp/guard-paper-toolchain/tectonic --offline
```

初次联网构建补齐公开 TeX resources 到 `build/paper/cache`；最终离线构建通过。
产物是 [10 页 PDF](../build/paper/main.pdf)、text、完整 logs 与
`build/paper/report.json`。无 unresolved citation/reference 或 overfull box。
PDF 渲染检查首页、框架公式和责任表／case-study 页，未见截断或重叠。
LNCS/amsmath 的 `vec` 重定义提示保留于 log，没有将它表述成零 warnings。

早期构建修复了上游 binary 重复打印 version 字符串和长代码标识符／表格的
overfull；这些是构建过程，不是实验结果。Docker image 查询未返回，完成的
构建使用独立 Tectonic binary，不依赖 Docker daemon。

稿件源码及官方模板提交到 git；PDF、TeX cache／logs 保持生成产物。
当前标题和匿名作者只是 working placeholders，还没有提交会议。

## 实现同步

本阶段另交付 [constant-body model／capability bridge](constant-bound-model.md)：
14 endpoints 审计通过，旧 nested-header／loaded-offset proof 及 native/path/work
绑定保持。实际 fixture 是 `component=4→5` 的一次 store tail；它改变了 offset 4
的 child header word，literal→helper loop 仍保持同一 public/internal temps 和 memory。
它不是完整五次 body、完整三层优化或新增 native 结果。

后续实现每个相关里程碑同时修改对应稿件和证据表。当前先完成 reached inner
BODY →all-observation physical scan →nested cached model →original AST factory／
Csem→Asm／native，再验收 compact sufficient condition、guard 工作量和运行成本。
接口、论文与成本测量保持同一个源范围，不延迟所有正文到功能完成之后。

## Narrative 责任澄清的后续复核

再次 fetch 后远端仍为 `271f6fc`，main narrative 和 context 正文与其一致。
[实现责任核对](narrative-implementation-check-2026-10-06.md)已更新到 `db6704c`，
删除单 loaded 根 numeric producer 仍未完成的过时表述，保留第二 header 的
实际 joint scan／安装缺口。Framework 正文新增 original-source 安全域与具体
producer 的责任；表格明确语言安装定理消费 region/site 证据。Evidence map
绑定实际 certificate、preserving rule、constant-body capabilities 和两份责任文档。

同一 offline 命令重建通过，仍为 10 页；无未解析引用或 overfull box。
渲染检查修改后的第 4、5 页，表格、公式和段落无截断或重叠。
本轮 `build/paper/report.json` SHA-256：
`c650d7cc5462e52a40c54ae5655627da1ddfa62e784aff30b119de831f15174e`。
文档 links、JSON 和 `git diff --check` 通过。本轮没有修改 kernel／证明源码，
没有重跑 Rocq、提取、native 或计时；不增加功能或实验结果。

## Constant BODY joint scan 的实现同步

[实际 BODY 消费者](constant-body-joint-scan.md)现已连接源许可、双观察地址比较、
完整子域覆盖和接受后的 inner-prefix preservation／advance。30 个 language／
domain／fixture 端点审计通过；新 fixture 包含适配 Figure 2 leaf 的完整五次原
store 和检查执行。Case-study 和 evaluation 正文同步这些 Clight 证明结果，保留
完整 inner/outer runtime loops、canonical model、factory／Csem→Asm／native 的
pending 标记。Evidence map 绑定实际端点、文档和独立 proof report 摘要。

同一 offline 构建命令通过，当前为 11 页；无未解析引用或 overfull box。
渲染检查修改后的第 6、7、9 页，代码、段落和 pending 标记无截断或重叠。
旧 native/path/work 报告只核对绑定，没有重跑，没有新成本或收益数字。
本次最终 `build/paper/report.json` SHA-256：
`0312828065a85389fef055ac4c3514866ba8544a29c280206fb3f705d9fc8ea2`。

## 2026-10-07：inner loop 与整行接受同步

[Inner scan](constant-joint-inner-scan.md)已把 BODY producer 接到实际短路 loop，并
从原 outer prefix 打开 inner prefix；整行接受导出全 column 的观察保持和下一
outer prefix。14 endpoints 独立审计通过，原 BODY／model／nested-header／compiler
及 native/path/work 绑定核对通过，没有新增数组 fixture、提取或运行矩阵。

Case-study、evaluation 和 evidence map 同步真实执行端点、fixed-entry header
责任与源／guard 状态区分。实际 outer loop、完整模型、factory／whole-program
编译和新 native 接受继续标记 pending。Offline 重建仍为 11 页；无未解析引用
或 overfull box。渲染检查修改后的第 7、9、10 页，段落和红色 pending 无截断。
最终 `build/paper/report.json` SHA-256：
`2adbee8ae42aa94e1b3938543dded5f946397221e7b32968278eb1b7150435ff`。

## 2026-10-07：outer scan 与完整双缓存源同步

[Outer 消费者](constant-joint-outer-scan.md)已从原 source prefix 许可真实逐 row
检查，整段接受生产所有 rows／columns preservation，实际填入旧 two-cache
transport，保留原／缓存源的出口 temps 与 final memory。独立 empty outer guard、
zero-header transport 和 first-row refusal 分别有实际执行端点。14 endpoints
（2 language、12 domain）／565 依赖／1,069 源摘要审计及先前 validators 通过，
kernel 闭合、完整 compiler 保持 42 assumptions；旧 native/path/work 仅核对绑定。

Case-study／evaluation／evidence map 同步这一能力和输入责任；canonical model、
实际 capture/numeric producers、原 AST factory／candidate／whole-program compiler
与新 native 接受继续标记 pending。没有新增数组 fixture、提取或计时。
Offline 重建仍为 11 页，无未解析引用或 overfull box。渲染检查第 7–10 页，
新增段落、pending、evaluation 和后继页均无截断／重叠。
最终 `build/paper/report.json` SHA-256：
`fb1b7aaff10a9ff41c352fb7129f338afab99209966d04732b854b5d4d6d2911`。

## 2026-10-07：完整三层 canonical model 同步

[Canonical model 消费者](nested-constant-model.md)已将合法的双缓存源接到旧
affine AST，并消费 checked package 取得真实 Loop 内存执行。12 domain
endpoints／557 依赖／1,071 源摘要审计通过；kernel 闭合，旧 compiler 保持
42 assumptions。原 outer／inner／BODY／constant model／nested-header／loaded-offset
validators 及既有 native/path/work 绑定核对通过，没有新运行矩阵或计时。

重新 fetch/read narrative `271f6fc`，main 正文一致。责任文档修正旧 outer 待办，
计划继续分开 proof-first 功能链、紧凑条件／成本／接受域和作者负担验收。
Case-study／evaluation／evidence map 同步当前模型接口；实际输入 producers、
原 AST factory／候选／host／提取和本例 native 接受继续标记 pending。
Offline 稿件仍为 11 页；修复新增段落的排版溢出后，无未解析引用或 overfull。
渲染检查最终第 7–10 页，新增段落、pending 与后继内容均无截断／重叠。
最终 `build/paper/report.json` SHA-256：
`69156b7c1310551ee214cec60d3b24f61918e99148ccdf2c22879f847b7f7f53`。
