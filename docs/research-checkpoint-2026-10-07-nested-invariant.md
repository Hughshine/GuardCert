# Narrative 复核与入口值 guard 的阶段验收

本轮有具体进展，完整 polyhedral goal 保持 active。重新 fetch 并检查所有远端
heads 后，narrative reference 仍为 `271f6fc941910456da43a76e9f0eed38e8a5e200`；
main 中 `docs/topdown/paper-narrative.md` 与远端正文一致。

最新 narrative 的验收继续约束实现：最小 kernel 止于 local guarded correctness；
语言提供 installation；domain/优化方提供前提与实际模型对应；先闭合已声明 scope
的证明链，再分别改进 guard 成本、接受域和作者负担，不以 verified 标签解释 OLO
功能缺口。当前改动是上层 condition service，不扩展 kernel。

[入口参数的同值条件](nested-invariant-word.md)已从 typed actual-store effect 接到
真实 source/model、physical guard、data-only factory 和新的 Csem→Asm entry；
候选 validator、compact exit 和语言 host 复用。定义性从原 prepared/domain receipt
生产，没有新 caller callback。原 literal lowering 保留；unsupported／不同值
路径使用原 scan。Stored value 的 modular wrap 与控制／地址条件分别处理。

独立 35 端点／591 依赖审计和提取通过；compiler 的 42 项既有 assumptions 保持，
kernel 闭合。新的两类 C／20 inputs 在六种 modes 下有 120 assembly calls，三个
Clight modes 的 60 calls 有显式接受／回退核对。完整数组、headers、公开 counters
和上下文 effects 一致，包括 `INT_MIN+INT_MIN+1` 的 word-one alias 接受。
无新增未修改汇编 probes、成本测量或最新入口的 fresh source-tree reproduction。
具体报告 digests、限制和命令见上述文档；旧 helpers、Makefile 和阶段证据保持。
新入口 proof/native 与前一 compact proof/native/large/cost 的 digest validation 均通过。
实际 manuscript 离线编译为 19 页，无 unresolved refs/cites 或 overfull boxes；
已渲染并检查新 case-study/evaluation 页面。
稿件 builder 核对源码锚点和排版，不重新执行研究实验。

下一步保持三个不同层次的任务：

1. 在同例比较新 guard 的完整工作／运行成本、接受域和代码大小，以及实例作者
   数据、库证明和 site-specific 证明；当前“无新语义 callback”不是定量 author
   burden 结论。实现后的 GDB 路径证据和 latest-entry source-only rebuild 单列。
2. 对仍改变 header 的 BODY 和多数组 alias 继续 compact footprint 条件。已有
   source-observed affine envelope 是可复用前例；raw pointer-base ordering 不能
   自动使用，必须有实际比较 primitive 的 definedness 与 source/placement receipt。
3. 更广 affine source、参数化域变换、动态布局／delinearization 与完整 BT 功能
   仍沿完整目标推进。不能把 invariant uniform store 子集称作 OLO 的完整覆盖。

对应 manuscript 更新记录真实检查/模型/host 责任与以上报告，保留性能和一般
projection 待办；本阶段不是终稿贡献或完整目标完成。
