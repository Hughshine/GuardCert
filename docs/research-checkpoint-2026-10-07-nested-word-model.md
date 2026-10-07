# Checkpoint：same-word 条件的实际模型与检查出口

2026-10-07，接续 main `2c55aa5`。完整目标保持 active；本轮是实际 producer 的
证明交付，尚未改变 extracted compiler，也没有新 native／性能结果。

## 交付

- [语言控制分类](../prototype/interface/ClightWordObservationControl.v)从 actual
  structured `exec_stmt` 取得完整 Mint32 constant-word store chain；支持有限 loop
  执行，不声称终止或 pointer-binding 保持。
- [源到模型](../prototype/interface/ClightNestedConstantWordModel.v)消费旧 checked
  site、原 source numeric/preparation receipts 与 BODY bool checker，证明缓存比较
  接受时 raw headers 等于存入 word；每次 literal subloop 保持 observations，再
  复用旧 nested transport／canonical bridge。没有新增语义 callback。
- [实际 residual check](../prototype/interface/ClightNestedConstantWordCheck.v)是
  两个私有缓存比较与结果 temp。执行、same memory、结果和 actual check-exit
  ports frame 已证明；接受生产固定 model anchor、原 final memory／公开出口及
  numeric 前提。
- [fixtures](../prototype/interface/ClightNestedConstantWordExample.v)证明一个真实
  仿射索引常量写实例通过旧 source/model package 和新 BODY checker；另覆盖完整
  三层语法、缓存接受／拒绝、真实 check 执行和 root refusal 不读未定义 child。

具体接口、三方责任与 remaining installation 见 [nested-word-model](nested-word-model.md)。
Kernel 未修改；候选及 whole-program host 的证明仍是独立环节。

## 验证

`audit_nested_word.py` 编译／独立查询／只读 validate 均通过：22 endpoints、508
required dependencies，所有端点只用独立 memory／Clight 基线的 6 项 assumptions，
kernel 闭合、零新增 global axiom。报告 SHA-256：
`ce5c202de41b517fc4b9e51b81b239754a5278758dadef995255c731695677ae`。

旧 `audit_word_observation.py --validate`、source-only reproduction readonly validate
和 `make nested-frontend-validate nested-frontend-coverage-validate` 均通过。
这些是旧证据的保持核对，没有重新跑完整 native matrix 或重复全部源码构建。
新 audit script 的 Python 编译与 Git whitespace check 通过。

实际 manuscript 的 case study／evaluation、README 与 evidence map 已同步。
Offline Tectonic 构建通过，15 页；已渲染检查第 9／13 页，无 overfull／未解析引用。
最终 `build/paper/report.json` SHA-256：
`69377f24a4e93e9023b13e20b27911f983e10f92f748bdc5660610acd29f21fc`。

## 下一项

将这份 producer 接到 physical guard／multi adapter／typed factory，尽量保留旧
scan 作为新条件不成立时的路径，复用候选与安装证明。然后验证 header/data overlap
的新接受路径、不同 word 的扫描／原源回退及完整程序上下文；分别计数 residual
比较和完整 guard 的工作，并测完整运行成本。Broader affine/source classes、动态
布局及同例作者工作比较继续推进，不以本阶段局部证明替代完整目标。
