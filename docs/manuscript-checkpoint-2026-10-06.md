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
