# 完整 nested loaded guard：条件捕获、空域和 cached/original 分派

2026-10-08。本阶段关闭 [双轴 scan](word-store-nested-scan.md) 的捕获/gates
输入缺口，生成实际 guard，并证明完整两层 cached/original rewrite。它尚未
消费 polyhedral candidate、生成本族 data factory 或安装新的 loaded compiler。

## 优化实现者如何消费这个服务

实现者给实际源 shape、checked store body、两份 header 表达式的 pointer/delta、
cache names、private scan names、stable/live/public scope 和 rename。静态事实
包括 body checker 的结果、scope/freshness、资源唯一性、source/iterator 与
保护 temps 的分离。自动 source factory 仍应生产这些事实；源码使用者不应
提供 semantic callback。

`word_store_nested_guard_execution` 只请求原 loaded nest 的正常执行作为动态
证明前提，产出：

- 实际 conditional capture 执行、捕获参数 `upper` 与 `option child`；
- 原 source 在捕获入口的执行、公开 source exit 的运输；
- root header receipt；child 为 `Some` 时的 receipt 和原 outer-test 成功事实，
  为 `None` 时的原 outer-test 失败事实；
- 完整 guard 的实际执行、相同 memory、live/public frame 和准确 flag；
- 接受后从 actual guard exit 执行 cached nest，保留原 final memory/public exit。

没有入口 READY、row-zero、nonnegative、数组可用性或 cached execution 的
动态假定。检查许可来自原 source，不来自待建立的缓存模型。

`word_store_nested_rewrite_execution` 对如下实际 AST 证明正常执行与公开出口：

```text
conditional capture; entry gates; joint short-circuit scan
if private_flag then cached nest else original loaded AST
```

这是 hoisting 两份 loaded bounds 的一个完整局部 rewrite。任意 public scope
由调用方/site 指定。它还没有建立本族 whole-program simulation；整程序
安装仍需语言 progress/boundary/placement 和资源声明证据。

## 条件读取与分派

捕获首先读 `*H + delta`。只有原 `i < upper` 为真才读 `*K + child_delta`。
这与原 child 的首次读取边界一致；column reset 不修改 child pointer。
然后 guard 依次检查 row-zero、root 非负和 root 正值。

| 入口情况 | 后续检查/行为 |
| --- | --- |
| row 非零或 root 负值 | flag 拒绝；不运行 scan；完整 rewrite 运行原 AST |
| row 为零、root 为零 | flag 接受；不读 child cache、不运行 scan；cached 外层不进入 body |
| row 为零、root 正值、child 负值 | 捕获过 child；flag 拒绝；原 AST fallback |
| row 为零、root 正值、child 非负 | 联合双 cursor scan；接受保持两份 header，拒绝停止两轴 |

Row 非零时 capture 仍遵循原 outer comparison，可能读取 child；这是原 source
已经许可的读取。它随后被 row-zero gate 拒绝，不因优化器对输入形状的要求
改变原读取的安全边界。

空域路径不要求 child READY。语言证明用 root receipt 建立原外层 false test，
由 quiet execution determinacy 得到其实际出口；cached 外层也只读 row/cache，
不求值 child 或 body。最后统一运输到 guard 的真实出口。

## 接候选时必须保持的状态区别

接受不意味着所有潜在的缓存参数都有值：outer 空域接受可以留下 child cache
未定义。因此下一 source/model adapter 不能在每个接受入口都运行一个无条件
读取 child 的 numeric/layout setup。它应在空域直接执行已证明的 cached 空
源，或提供同样跳过缺失参数的准备代码；活跃接受才消费完整 child receipt。
这一 obligation 属于 domain/语言实例的 dependent-condition 服务，不要求
generic kernel 认识 Clight header 或数组。

既有 `check_multi_tensor_region_source` 递归提出并独立检查 source nest，故两轴
cached source 可以沿现有数据入口研究接线。接线必须另证明 cache/维度/scalar
bindings 从实际 guard exit 到 setup/model 的运输，再接真实候选/公开恢复。
已安装的 temp-bound driver 不能代替本族的 original loaded-source progress、
selected placement、declarations、Csem→Asm 和实际 native 验收。

## 已检查的真实内存行为

在同一 allocation 中，`H=K=1,B=5,A` undefined 的源执行 `A=B+3;B=A+3`。
完整 capture 和 guard 接受；完整 rewrite 得到 `A=8,B=11`，保持原 iterator
出口。`K` 与 `B=2` alias 而 `H=1` 不变时，`A=B-2;B=A-2` 改写 child header
为 -2；完整 guard 拒绝，完整 rewrite 保留原一个点执行后的 memory 和出口。

空域例只有 root pointer 与 row 有值，root word 为零；child pointer/cache
和两个数组 temps 均未定义。实际 capture 跳过 child，guard flag 为 1，并保持
这些 temps 为 `None`；完整 rewrite 正常退出且公开状态与原空循环一致。
这是 Rocq 内核检查的 `exec_stmt` 推导，不是新增 C interpreter 或 Asm 运行。

两模块独立审计查询 20 端点：3 闭合、最多 6 项旧 globals、1,142 项实际可达
绑定，零新增公理；逐项核对前一 1,138 项绑定的冻结 report，没有重跑历史
递归审计或读取其他工作的未提交 column/component 文件。报告为
`build/multi-word-nested-guard/proof-v1/report.json`，SHA-256：
`0ddcd3c5ac86c0a5f29bbadb7539a49f2598a557cc34aacbd70251b08ebeb56e`。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/compile_word_store_nested_guard_sources.py --attempt completed
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_word_store_nested_guard.py --validate
```

## 下一验收与三方责任

Framework kernel 保持局部证书组合。语言服务提供 conditional reads、gates、
实际 scan、memory/private/public frame、source/cached 执行运输与 host 安装。
Domain 接原 prefix/coverage/header 保持、source/model 与候选对应；factory/site
提供静态资源、scope、原 source progress 和 placement 的数据生产。公共边界
仍是 region guarantee 与具体 context requirement 的匹配，不新增 contract algebra。

下一项接同族 source/model/candidate 与 data factory，然后复用已连接的 marked
C／真实 Pluto／prepared codegen／selected backend 路径，验收本族完整 C→Asm
接受、回退、多 site 和 context。一般 affine domains、更多 source 覆盖和
coordinate-only scalar 仍属完整目标；本阶段不作新的 compiler 或成本结论。
已闭合 temp-bound slice 的紧凑条件、接受域、代码尺寸、runtime work、完整成本
及 OLO 功能/可用性比较继续独立推进，不等待全部 source 扩展。
