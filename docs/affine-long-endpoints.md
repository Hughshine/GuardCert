# 仿射循环端点：数学前提与实际 capture 的责任

本阶段为原语料中的常量上界和外层变量端点准备证明依赖。三个模块共 252 行，
[审计](affine-long-endpoints.json)查询十个端点，其中六个 closed，其余最多使用
六项既有 globals；没有新增公理。三次成功和八次失败的源快照、日志均保留。
这些是局部服务，当前 source-tree factory 和 native compiler 尚未消费它们。

## 为什么最终 word 检查不够

令实际 I64 temp `x = 2^62`，端点表达式为 `4*x`。数学值为 `2^64`，实际
CompCert 机器值为零，所以检查 `0 <= endpoint <= 98` 可以接受。这样的接受
不能推出数学端点也在 `[0,98]`。新模块中的两个 Rocq fixtures 分别证明最终
机器检查接受，以及基于数学区间的表示检查拒绝这个例子。

要解释一个端点的数学值，证明链需要分别建立：

```text
原表达式经 checked decoder 得到 affine row
实际 controls 的 words 对应 mathematical valuation
实际求值得到 Int64.repr(row · valuation)
已有输入区间事实 → 数学端点区间 → 最终值在 I64 signed 范围内
实际 read-only capture 接受 → 数学范围与精确 I32 cache
```

其中最后一行使用真正的 Clight check/capture 执行。区间传播是对数学数据的
可计算证明服务；它本身不是新发射的 Clight runtime guard。输入处于各区间的
事实仍需由优化实例根据实际源、已认证的循环域或安全的前置检查建立。

## 服务交接

| 交付者／服务 | Requires | 已证明的结果 | 本阶段没有交付的工作 |
| --- | --- | --- | --- |
| 数学 domain 库：`AffineIntegerIntervals` | 输入值逐项属于给定区间 | 支持正负系数的 affine 区间包围实际数学值；维度缺失时拒绝 | 从任意源程序自动产生输入区间事实 |
| Clight 库：`GuardMemoryAffineLongEndpoint` | checked affine decode、实际 controls word 关系 | 实际表达式类型和 modular execution；加入最终 nonwrap 后得到 signed/math 对应 | 任意表达式、loads 或语言的安全求值 |
| 同一 Clight 库的 capture | 上述证据、I32 check limits | 实际 `E0`／`Out_normal` 执行保持 memory；接受后数学范围与精确 cache | 自动分配 fresh temps 或全程序安装 |
| Capture frame | cache/flag 不属于公开 controls | 原 controls word 关系保持 | 任意 context 的全部 live-out 保持 |
| `GuardMemoryAffineLongEndpointRange` | 输入区间事实与区间表示检查成功 | 建立最终 nonwrap，接到实际 capture theorem | 紧凑 OLO 入口条件算法、新的 native 源族 |

这里的 nonwrap 是**最终数学端点在 signed I64 内**。实际执行对应针对 CompCert
语义，未新增每个中间运算都不溢出的定理，也不是 LLVM poison 或一般 C 标准
undefined behavior 的证明。具体 source/model 桥还要生产其所需的 controls 范围
及机器表示证据。最小 kernel 与现有语言 host 法则保持。

## 两个语料缺口怎样使用这些服务

原 `nodep` 使用 `i < 100`、`j < 4`；现有
`GuardMemoryDoubleSourceTreeDecode.propose_double_tree_bound` 只提出 global header
或 header 减常量，因而缺少 literal endpoint。常量 affine row 如 `([],100)`
无需输入区间即可通过新的表示检查。后续仍要把这个端点接到源循环有限执行、
Loop 域、候选、公开 counter exit 与实际 factory。

原 `dsyrk` 的内层循环从 `k=j` 开始。现有 tree initializer 只表示 I32 常量
cast；新的 affine decoder 可表示外层 temp `j`，区间服务可使用外层循环已经
建立的 `j` 范围。后续需要证明这些事实在实际到达的 child entry 成立，并处理
body frame、参数编码、退出 counter 和 host 安装，不能把接口的区间前提留给
C 使用者作为任意 callback。

它们仍是未完成的功能缺口；本 checkpoint 没有增加这两个原例的 native 安装
或支持计数。每个源族扩展须沿同一 compiler 链交付，而非等待最后一次全局接线。

## 验证与后续

成功证明及其对象已冻结。当前审计绑定 221 个 reachable sources、10,703 个文件，
包括既有 compiler 基线及全部本阶段编译 attempts。可验证保存的绑定：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_affine_long_endpoints.py --validate
```

下一步先扩展实际 source grammar 和 model 桥，消费这些已证明服务，然后接
factory／当前程序 Csem→Asm 和原例运行。Alias、loaded header 读取许可及稳定性
仍复用或扩展各自服务；纯 temp/literal endpoint 不替代它们。这个阶段没有完成
紧凑入口条件推导、guard 成本或完整 PolCert／CGO17 验收，长期 goal 保持 active。
