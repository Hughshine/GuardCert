# OLO 与当前 tensor 实例的同问题核对

参照 [Optimistic Loop Optimization，CGO2017，Figures1–2和§§5–7](https://pollylabs.org/publications/grosser-2017-Optimistic-Loop-Optimization.pdf)，
本轮重新读取作者 PDF。它将模型所需的逐位置假设概括／简化为入口参数条件，
并讨论机器溢出检查和按实际访问域安排预加载。这些要求仍是本项目的功能与
可用性验收依据；当前已证明的 tensor 子集不能替代完整论文场景。

后继[loaded tensor 首点服务](tensor-header-point.md)已连接条件式capture与实际
动态`i*ld`首点，并证明原store许可的检查、接受后的两header保持及alias拒绝路径。
40端点独立审计通过；它尚未关闭完整source-prefix／cached模型／candidate／安装
链。本页的loaded＋动态layout缺口仍保留，不能把首点证明称为完整loop版本化。

后继[实际坐标次序扩展](tensor-coordinate-order.md)已在原proof report下接入
`[j,i,k]` 数据提案并保留 `[i,j,k]` 源；[另一轮完整成本](tensor-coordinate-cost.md)
记录大stride输入的交换收益和小输入负结果，使用单独的stride<2048 profile。
后继[literal-bound接入](tensor-literal-bound.md)又完成实际第三层`<5>`的private
准备、原源／检查后状态运输和expression-progress安装，八配置1,152汇编／432
Clight调用通过。它仍未关闭loaded／cross-tensor／nonrectangular缺口，也没有原
BT／Polly对跑或其他framework作者工时测量。后面的历史“下一项”保留本页创建时
的判定；最新功能计划是loaded-bound／+1与动态layout的实际组合。

| 相同问题／验收维度 | 当前 tensor 的实际处理 | 当前缺口或区别 |
| --- | --- | --- |
| 动态逻辑布局与物理地址 | 真实 `((i*ld)+j)*5+k`，动态 stride，source/model/Horner 与 pointer correspondence | 一个 tensor和单 leaf；native第一个extent选源bound，不支持任意未读取的dimension参数 |
| 域内坐标条件到入口条件 | 全部 affine reads/writes 的 box extrema，受 profile约束的安全机器编码 | Rectangular boxes，不是任意Presburger投影；cap／profile可能保守拒绝 |
| 实际机器算术 | Volume乘法前做除法界检查；affine lowering证明每个中间值安全；RMW值按word语义处理 | 没有通用的硬件overflow-flag实例；不支持的static arithmetic拒绝 |
| 只在合法路径读参数 | Source-derived read许可；empty outer先拒绝，不读取后续参数 | 最新第三层可为literal，其他bounds仍是temps；OLO motivating source 的两个loaded bounds须由现有loaded服务与tensor组合 |
| Array／header稳定性 | 本例一个tensor、temp／literal bounds；条件覆盖后连接既有依赖 checker | 不能拿这个guard证明跨tensor alias或loaded-header稳定性 |
| 版本化、退出与程序上下文 | 原AST fallback；actual candidate／iterator恢复；kernel局部证书，语言host和Csem→Asm | 当前finite structured host范围，不能自动推出任意exit／divergence contract |
| Runtime work与实际收益 | [同例成本](tensor-region-cost.md)及[另一坐标次序成本](tensor-coordinate-cost.md)记录prefix判断、bytes和完整调用 | 前者无净收益；后者一项声明输入有收益；新literal入口未测成本，不是原BT或Polly的性能对照 |
| 自动化与作者工作 | 数据factory和候选checker生产local/site证据；[责任清单](tensor-proof-ownership.md)可核对 | 没有其他框架同例作者工时／证明工作测量，不声称这种优势已验证 |

这份 C 例子以int32 RMW实现实际读写，保留动态 stride、三个loop和公开counter。
最初temp-bound实例没有保留Figure1的两个`grid` loads、对应的`+1`和第三层
literal bound。新入口已恢复第三层literal；两个loaded bounds／+1仍未与动态
layout实际组合，因此不能称为那个motivating excerpt的完整覆盖。先前的
[loaded-header适配](olo-figure2-coverage.md)有自己的固定布局证明和运行证据，
两者还需要实际组合，不能相加后声称完整动态BT已完成。

以下是本页创建时的后继判断，其坐标次序／literal项现已由上述阶段关闭。

本轮结果确定了后续工作的两个方向。性能方面先用现有parametric coordinate
checker接入另一种实际地址／遍历次序，验证原先按列访问、交换后按行访问的
源；无需为一种新schedule重证语言host。功能方面继续literal-bound transport、
loaded-bound与动态布局组合、更多body／跨tensor alias和affine domains。
新增前提仍需分别交付安全读取、accepts⇒模型义务和实际状态运输。

最小 kernel、三方证明归属和四条逻辑链保持。OLO comparison的最终验收同时
看功能、自动条件处理、成本和人工工作；本报告没有把证明或测试数量当作
这些维度的完成证据。
