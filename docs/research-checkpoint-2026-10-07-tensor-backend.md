# 2026-10-07：narrative 澄清吸收与动态 tensor 候选连接

本轮是具体 progress，完整目标继续 active。

重新 fetch `topdown/research-positioning` 后，远端为
`271f6fc941910456da43a76e9f0eed38e8a5e200`，其
`docs/topdown/paper-narrative.md` 与 main 相同。读完正文、澄清 commits 和
context-lifting 设计说明；当前没有发现额外的远端正文变化。以下落实其要求，
不以再次复制 narrative 代替实现。

## 澄清怎样影响当前目标

| Narrative 要求 | 本阶段决策 | 后续可验收交付 |
| --- | --- | --- |
| 最小 kernel 止于 local correctness | 动态布局、检查编码和候选 lowering 留在语言／domain 库；kernel 未变 | 只有实际 obligation 无法表达时才提出 API 改动 |
| 三方责任与四条逻辑链分开 | 明列 C_guard 的 D 与 C_derive 尚缺源义务；checker 生产 C_opt，不新增候选语义 callback | source/model、entry transport、region guarantee 和 site placement 的真实 producer |
| 全程序安装不是局部执行的自动结论 | 本轮只证明 checked candidate execution，保留 actual source/progress/public exits 未完成 | 具体 local rule／typed factory 由现有 Clight host 消费，新的 Csem→Asm entry |
| 先闭合约定范围的证明链 | 先接这个三层、变量布局、真实 RMW 源子集；不先扩张通用 contract algebra | 完整 C 输入、合法运行时布局、接受／回退、public continuation 和重复 rewrite |
| OLO 是功能与 usability 验收参考 | Volume 已紧凑，但不据此声称完整 condition synthesis 或完整 BT | 同例分别报告 coverage、condition algorithm、未闭合证明或语义差别；成本、接受、bytes、作者负担独立列报 |
| 与实现同步 manuscript | 新 candidate checker／backend 的已证与待证边界写入实际论文和 evidence map | 每个后继里程碑更新相应正文，实验数字仅在实验完成后加入 |

这些任务属于已有长期目标，不把局部阶段的提交当作完成整个目标。

## 本轮真实交付

[动态 tensor backend](dynamic-tensor-backend.md) 保留 vector affine coordinates、
runtime dimension temps 和现有 read／RMW／int32 RHS，产生真实 Clight 指令／
循环执行及完整 memory 对应。Private scratch 不覆盖 layout、pointer、dimension
或声明的 live temps。入口 observer、标准 readonly guard 和 registry nonalias
连接；原 affine／tiling checker 成功直接交付候选实际执行证据。

独立审计：66 端点（33 旧＋33 新）、238 本地依赖、30 闭合、零新增 globals；
候选端点继承原 checker 最多 14 项基线。七项提取运行验收通过，含三维 RMW
identity／tiling 接受和结构性拒绝。没有新的 C 输入编译、生成 statements 的
动态执行、完整程序安装或成本实验。详见服务文档中的报告绑定。

## 紧接着做什么

1. **真实 source adapter**：识别 Horner 形式的变量布局地址，证明其 modular
   word 求值与 vector address 相同。保持原 AST 作为 fallback key；不要只接受
   我们新 lowerer 自己生成的 source AST。
2. **源许可的入口事实**：从首次实际活动路径生产维度／RHS definedness 和
   pointer 绑定，空轴不提前读取内部参数。Loaded headers 另需真实 capture 与
   stability／entry frame；成功 proof-facing observation 不能替代这些证据。
3. **完整 C_derive**：运行时条件覆盖全部活动坐标，例如 `columns<=ld`，并导出
   原 C 到 Loop 模型的执行。单 tensor injectivity 不替代跨 array 或 header
   分离；成功 Mem operation 仍是权限来源。
4. **local 到 global**：恢复原源 public iterator exits，连接 checked entry、
   typed private pool、source progress 和 site placement，交给已有语言 host，
   提取新 Csem→Asm compiler。正常完成定理不能单独覆盖可能发散的 fallback。
5. **功能验收之后的同例比较**：不同合法 ld、padding、overflow／range 拒绝、
   未初始化空轴、RMW dependence、loaded alias、重复 sites 和上下文。随后量化
   条件成本／接受域／代码与编译成本、完整运行，以及三方可复用证明和实例作者
   仍须提供的数据／证明。新增更广能力不能无限推迟这个比较。

最难的下一项是原源活动路径、真实地址和模型坐标的对应，以及这些事实运输到
实际检查后入口。它不是再加一张 abstract record，也不是修改 if 的定义。
