# 双 loaded axis 的原源许可、联合 header 检查与实际 cached 出口

2026-10-08。该阶段接在 [单轴完整 guard](word-store-sequence-scan.md)之后，
将任意 checked assignment list 的原源许可推进到两层 loaded loop。它是
language/domain 库的证明连接；完整条件捕获和该族编译器安装仍待接线。

## 输入、生成代码和输出

源片段的实际 Clight shape 是：

```c
for (; i < *H + delta; ++i) {
  j = 0;
  for (; j < *K + child_delta; ++j) {
    STORE_1;
    /* ... */
    STORE_N;
  }
}
```

`body` 是 checker 接受的任意长度完整 word-store 序列。各 store 的地址
index 使用受限 word-expression 语法；RHS 仍在原执行的真实中间内存求值。
两份 header 的 pointer/cache temps 属于 stable 集；两条源 iterator 不在该集。
`H` 与 `K` 的 pointer temps 可以指向同一内存 word，不要求二者不 alias。

本阶段入口已经捕获两份 header，证明了 cache/read receipts、非负 count、
外层 iterator 为零，并有原 loaded nest 的正常完成执行。原执行是用于
语言定理的证明前提；不是一个要求 C 用户提供的 callback，也不是已交付
的自动 factory。Private cursors、limits 和 flag 与 caller-live temps 分离。
Rename/scope 的静态事实仍由实例化方证明，下一 factory 应从 AST/资源池生产。

`word_store_nested_scan_code` 生成固定语法的双 cursor loop：先设外层 limit、
flag、cursor；每一行设置内层 limit/cursor，然后对每个 store 与两份捕获
header 的地址做 readonly 比较。AST 大小不按动态 count 展开。内层首次拒绝
停止内层，并让外层停止；检查保持原 memory 和全部 caller-live temps。

`word_store_nested_scan_cached_exit` 提供：

```
原 loaded nest 执行 + 捕获 receipts/gates + 静态资源/scope 事实
  -> 实际 Clight scan 执行、memory/live frame、准确 flag
  -> 若 flag 接受：从实际 scan exit 执行 cached nest，
                 与原 nest 相同 final memory、相关 live 出口。
```

缓存嵌套循环的执行不在检查的许可前提中。该输出可交给后续 source/model
与候选对应服务；这里尚未执行优化候选或安装新的 loaded compiler。

## 最难的连接：许可不能来自待证明的缓存模型

原 nest 的 outer prefix 记录已接受行之后的实际源状态与剩余执行。打开
当前行时取得实际 inner prefix。它只许可当前原 body 的 store receipts；
后续 store 的许可来自前一 store 之后的内存。已有服务只把权限回运到 scan
入口，不把后续 RHS 值前移。

当前点接受同时保持两份 header observations，才可以推进 inner prefix。
当前行全部接受，才可以推进 outer prefix。因而下一原 header test 和下一
body 的许可逐步获得；拒绝后不会使用后续行/点的假定许可。全部接受后再
证明原 loaded nest 与 cached nest 的执行对应，最后用 temp frame 运输到
实际扫描出口。

此组合还暴露了一个可复用接口问题：inner prefix 的 ready/observations
锚定在实际 outer entry，而旧 header law 要求覆盖所有 ready 状态。
`ClightAnchoredExpressionPrefix` 将 law 限定在当前真实 entry，借助加强的
ready predicate 复用原 receipt/advance 服务。这属于 prefix 库，不增加
kernel 对 Clight、header 或 polyhedral semantics 的知识。

## 三方责任

| 提供者 | 本阶段承担的责任 |
| --- | --- |
| Generic kernel | 消费局部 condition/conditional-correctness 证书并组合；本次定义不变 |
| Clight language library | 真实读取/store receipts、permission transport、word 地址计算、pointer comparison、安全执行、双短路 loop、private/live frame、actual-exit transport |
| Domain/optimizer library | 将原 nested prefix 接到 joint preservation 与 coverage；导出原源到 cached-source 对应；后续仍需 affine/no-wrap 模型和 checked candidate 对应 |
| Factory/site 与 language host | 后续生产静态资源/scope、region guarantee 和 placement evidence，消费既有 progress/boundary/installation 定理 |

公开边界是具体 site 的 context 可观察内容。Region guarantee 与 context
requirement 仍分开；本阶段没有新增通用 contract algebra。

## 真实内存例子

接受例在一个 12-byte allocation 中放 `H=K=1`、`B=5`，`A` 初始 undefined。
两条 store 是 `A=B+3; B=A+3`。实际嵌套源执行一个点，得到 `A=8,B=11`，
两个公开 iterator 都为 1。两份 header pointer temps 指向同一个 word。
检查接受，并从其实际出口执行 cached nest，得到相同 memory/live 出口。

拒绝例让 `H=1`，`K` 与 `B` 同为 offset 8 的 word，初值为 2，执行
`A=B-2; B=A-2`。第二条 store 将内层 header 改为 -2，外层 header 保持 1。
原源在第一个点之后重新读取内层 header，退出 inner loop；随后退出 outer
loop。联合检查在第一个点拒绝，不假定 `(i=0,j=1)` 已执行。仅检查 root
header 会遗漏此问题。这里证明的是原 source 和实际 readonly scan 的
`exec_stmt`，还不是完整 fallback dispatch 或新增 native 运行。

## 仍须完成的连接

1. 从原 source 生产 conditional capture 和 gates：outer 不活跃时不能读取
   未定义 child header；当前 theorem 要求两份 ready，尚未覆盖这种入口。
2. 接完整 cached/original dispatch、同族 affine model/candidate、公开恢复。
3. 同族 data factory 自动生产 resources/scope/progress/placement，并接已安装
   的 marked C → 真实 Pluto/prepared codegen → selected CompCert backend 路径。
4. 验收该 loaded family 的实际 C/Asm 接受、回退、多 site 和 context。

Word 地址检查的安全性不等于 affine/no-wrap 模型成立。Header-write separation
是足够条件，可能拒绝写回相同值的情形。运行工作仍按实际访问点/条数增长，
固定 AST 不代表 constant-time guard；没有新增性能或收益证据。已闭合
temp-bound slice 的 compact condition、接受域、代码尺寸、完整成本及 OLO
功能/可用性比较继续属于 active goal，不等本族全部扩展才开始。

## 证据与复核

六个新模块已使用固定的 CompCert 3.18／Rocq 9.2 工具链编译。独立审计
重新查询 50 个端点：9 闭合、最多 6 项既有 globals、1,138 项实际可达绑定。
所有 globals 位于旧 42-global compiler 基线内，无新增公理。审计逐一核对
前一 [1,114 项绑定的冻结 report](../build/multi-word-scan/proof-v1/report.json)，
没有重跑历史递归审计，也没有读取外部未提交 column/component 工作。

本阶段 [report](../build/multi-word-nested/proof-v1/report.json) SHA-256 为
`27d4447c320d7b5caac717a11c24883944458940725ef433875ba1e48cd426ae`。
所有失败编译日志保存在 `build/multi-word-nested/source-build/`；成功的源文件、
proof objects、helpers 和 report 保持不改。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/compile_word_store_nested_sources.py --attempt completed
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_word_store_nested.py --validate
```

该复核检查依赖与端点 assumptions；Clight fixture 的含义仍是内核检查过的
执行推导，不能代替新的 C/Asm 运行、收益、条件成本或完整程序安装证据。
