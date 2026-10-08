# 原 loaded source 许可的完整检查与 cached 分派

本后继把 [store-sequence prefix](word-store-sequence-prefix.md) 接成一条
loaded axis 的完整 Clight guard。入口捕获、拒绝 gate、短路 cursor loop、
全接受后的 cached source 和实际检查出口，现在属于同一条执行证明。
它是多维 loaded 多数组优化器的前置服务；不是新的完整 polyhedral compiler
或新增 Csem→Asm／native 验收。既有 temp-bound 多数组 C 流水线保留其范围。

## 实际插入的代码

原 source 形如下面的 Clight loop，body 是 AST checker 接受的 assignment list：

```c
for (; i < *h + delta; ++i) {
    A[f(i)] = rhs1;
    B[g(i)] = rhs2;
    /* 可以有更多实际 stores */
}
```

生成的 guard 是固定 AST，运行时决定循环次数，不按入口数据展开语法：

```c
cache = *h + delta;
if (i == 0) {
    if (cache >= 0) {
        flag = 1;
        bound = cache;
        cursor = 0;
        for (; cursor < bound; ++cursor) {
            flag = stores_do_not_overlap_header(cursor);
            if (!flag) break;
        }
    } else flag = 0;
} else flag = 0;

if (flag) {
    for (; i < cache; ++i) original_body;
} else {
    original_loaded_loop;
}
```

以上是语义等价的示意；实际 AST 先复制 bound，再初始化 flag/cursor。
`stores_do_not_overlap_header` 是既有 word 地址 decision tree，不读取 RHS，
不执行源 stores。静态名称／scope／body 事实由语言与 domain 实例提供，
完整 loaded family 的 data-only factory 尚待连接。本库定理中的 SOURCE
是语义证明所消费的实际 source execution，不是要求 C 用户传入的 callback。

## 检查为何安全，接受后为何可换 bound

1. **许可捕获。** 完成的原 loaded loop 总会求值第一次 header，即使第一次
   测试已为 false。已有 capture 服务据此执行同一个 `*h + delta`，得到 private
   cache 和 captured source receipt。入口不另外假设 READY、数组可用、起始
   iterator 为 0 或未来 header 保持。
2. **gate 在数组检查之前。** iterator 不为 0、cached signed bound 为负时
   拒绝并跳过扫描。Count 为 0 时扫描不进入 body；未定义的 A/B temps 不妨碍
   原零次循环和 guard 的执行。
3. **按原源 prefix 许可每个点。** 当前 prefix 取得实际原 body 的 assignment
   sequence receipts；后续 store 的 RHS 可以依赖前一 store 的初始化。回运的是
   permission，而不是 RHS 的值。地址检查只要求相关地址 temps 与当前 cursor
   一致，不要求全 temp environment 一致。
4. **接受当前点后才推进。** 所有实际 store 与 captured header word 分离时，
   它们保持该 header；原源下次测试才能使用同一 bound，许可下一 body。首个
   拒绝点使扫描立即 break，不再建立／使用后面的原源读取许可。
5. **全接受产出 cached 执行。** 所有 cached indices 的点检查接受，证明原
   loaded loop 与 cached loop 有相同实际执行结果；cached execution 是结论，
   不是许可 guard 的前提。
6. **接真实出口。** Guard 不改变 memory，只写私有 cache、cursor、bound、
   flag。利用 checked scope 与 temp frame，把 cached source 运输到实际 guard
   exit。拒绝时同样把完整原 source 运输到该出口。分派保持原 final memory、
   公开 temps 和正常控制出口；不声称所有私有 temps 相等。

Index 运算仍是 CompCert modular int32。该服务证明的是 header stability
和检查安全，未把 affine model 的 no-overflow 条件消掉。Point scan 针对同一
完整、对齐的 Mint32 word，不外推到任意 byte/chunk overlap 或 volatile。

## 提供的接口与责任

| 层 | 本次服务 | 仍需提供或连接 |
| --- | --- | --- |
| Generic framework | 既有局部 guarded-correctness 组合接口，kernel 未改 | 不包含具体 pointer、loop 或 source extractor |
| Clight instance | `word_store_sequence_runtime_check` 的地址-temp 运输；capture/gate、readonly cursor loop、source/cached 在实际出口的执行运输 | typed 私有资源、合法 placement、progress/boundary、host 安装及 backend 接线 |
| Loop/domain | 原源 prefix 到实际 point domain；接受后 header 保持、coverage、cached 结论 | 完整 nested 多 header、模型、candidate correctness、公开恢复及 data factory |
| 支持族的源码用户 | 最终给 marked C 和普通 policy 数据 | 本次不冒充已安装的自动 loaded family |

主要入口：

- `word_store_loaded_scan_cached_exit`：prepared entry 的完整扫描；接受时从实际
  scan exit 执行 cached source，匹配原 final memory 和 live temps。
- `word_store_loaded_guard_execution`：从原 loaded source 执行，生产捕获状态、
  ready relation、完整 guard 执行及接受出口的 cached receipt。拒绝不要求
  row-zero／非负／未来数组许可。
- `word_store_loaded_rewrite_execution`：完整 `guard; if flag then cached else
  original` 的实际正常执行及公开 frame。它示范 conditional bound hoisting；
  后续 scheduling adapter 可消费同一 cached receipt，不能据此宣称已安装调度。

## 真实内存案例与验证

`ClightWordStoreSequenceScanExample.v` 复用实际 12-byte allocation：

- H=1、A 未定义、B=5，body 为 `A=B+3; B=A+3`。原 loop 执行一次，结果
  H=1／A=8／B=11、i=1；完整 guard 接受，cached source 可在真实出口运行，
  完整 rewrite 得到同一结果。
- B 与 H 别名、H=2，body 为 `A=B-2; B=A-2`。第一次 source body 将 H
  改为 −2，下一原测试停止，i=1。完整 guard 拒绝第二条 store/header overlap，
  fallback rewrite 保留这份原结果。没有假定 cached count=2 的第二次原迭代
  已执行或可供许可。
- H=0，A/B temps 均未定义。原 loop 零次执行；完整 guard 接受，cached loop
  从实际出口也零次执行。只许可原 header，未提前要求数组 pointer。

使用固定 CompCert 3.18／Rocq 9.2 工具链，保留成功对象和全部失败日志。
独立 audit 重新查询本次端点、绑定其实际可达 closure，并只读核对上一
store-sequence report 的 1,100 个 bindings；没有重跑全部历史 transitive audits。
四模块共 **35 端点、7 闭合、最多 6 项既有 globals、1,114 项绑定**，所有
globals 均在旧 42-global compiler allowed set 内，无新增公理。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/compile_word_store_scan_sources.py --attempt verification
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_word_store_scan.py
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_word_store_scan.py --validate
```

报告：[`proof-v1/report.json`](../build/multi-word-scan/proof-v1/report.json)。
SHA256：

```text
4f470b4c502a3a672fdefc89722eb8dfaaea0aacd8715f951caa6092397ecfb9
```

本次未新增 native、编译器 endpoint、runtime cost 或 compact-condition 证据。

## 下一项验收

沿同一原源许可链组合完整 loaded nest 的多 header／条件读取，建立全接受的
cached/model 对应；再消费已证明多数组 candidate、公开出口恢复、data factory、
selected host 和真实 scheduler/codegen，做同族 C→Asm 接受／回退／context
验收。最难的位置仍是条件读取的许可与值保持、检查入口／实际出口的状态连接。

2026-10-08 再次 fetch 的 narrative 仍为 `12419c1`，与 main 正文一致。
最小 kernel 止于局部证书；host guarantee/requirement 的 clause 化仍是要由
实例检验的开放设计，不因此新增 kernel API。已闭合 temp-bound slice 的
紧凑条件、接受域、code size／runtime work／完整成本与 OLO 比较继续推进，
不等待所有 source grammar 扩展；本阶段不将完整 active goal 标记完成。
