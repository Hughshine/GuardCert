# Checkpoint：原 Horner tensor 源到候选与公开出口

日期：2026-10-07。后继于 `24b3e35` 的 dynamic tensor backend；完整目标 active。
重新 fetch 后，narrative 远端仍为 `271f6fc`，main 正文 diff 相同。澄清继续约束
本轮：最小 kernel 止于局部正确性；实例必须生产 source/model、读取安全、入口
运输和公开出口的真实证据；全程序 installation 属于语言 host 与具体 site。

## 本轮改变

六个新 Rocq 模块复用现有指令、候选 checker、lowerer 和语言循环基础设施：

1. `GuardMemoryTensorHorner` 保留真实 `((i*ld)+j)*5+k` 地址 AST，证明与 mixed-radix
   数学下标的 modular word／pointer 对应；实际地址求值反推各 operand 的 Vint。
2. `GuardMemoryTensorSource` 提供 executable affine-coordinate／Sassign descriptor
   checker；从真实 RHS/load/store 解码旧 memory instruction，所有声明 reads
   必须实际使用。成功 source execution 反推 pointer／stride／已用参数定义性。
3. `GuardMemoryTensorSourceRegion` 的数学 interval box 覆盖全部活动坐标和每个
   read/write，且真实原 nested Clight execution 生产 Loop SOURCE 与精确公开出口。
4. `ClightTensorSourceCandidates` 消费原 `exec_stmt`，内部生产模型，再连接原
   affine／tiling checker 的实际 candidate execution。附加实际 temp restoration
   后，全 memory 相同、指定 public live temps 与原 execution 的出口一致。
5. `ClightTensorSourceGuard` 的标准 readonly certificate 用原 finite silent normal
   completion 作为 D。Root／各 bound 先检查，全部接受后 first leaf 提供 stride
   许可，再运行真实 volume guard。它交付布局，不把数学 coordinate box 视为机器检查。
6. 独立手写 Horner AST 示例验证原 Sassign 识别、错误 metadata 拒绝、坐标反例，
   以及未初始化 stride／RHS 参数下空 outer 的实际短路拒绝。

没有新 source/model 语义 callback；但当前接口仍显式消费 source structure、
count/scalar bindings、profile、BOX 和源 execution 的证明前提。Region factory
尚未把这些义务自动包装成可交给 C frontend 的完整 guarded rewrite。

## 三方责任与验收位置

| Narrative 要求 | 本轮具体产物 | 尚未闭合的位置 |
| --- | --- | --- |
| Kernel 只消费证书 | 复用 readonly condition；kernel 文件保持 | 不增添通用 assumption extractor／WP 或 contract algebra |
| 语言提供真实语义服务 | Horner word、pointer/load/store 反推，short-circuit guard，count-temp restoration | literal-bound transport 连接、private temp declaration、progress／placement |
| Domain/site 提供实际推导 | affine-coordinate metadata、box soundness、真实 source→model→candidate；公开 exits | 实际 region data factory，覆盖全部条件的机器编码 |
| C_opt 与 C_derive 分开 | checker/lowering 复用；原源 producer 与数学覆盖单独证明 | 完整入口充分条件到实际安全检查的连接 |
| C_guard 的 D 有真实来源 | 源完成许可每层 bound，再许可 address/RHS operands | 当前只提交 layout condition；不能替代 coordinate condition |
| C_host 是语言安装义务 | 新局部证明具有 full-memory／public-temp 输出，可供既有 host 消费 | 没有新 Csem→Asm entry 或完整输入安装 |
| Proof-first，随后 OLO usability | 本轮推进约定子集的源/候选证明，不用接口字段充当证据 | 子集完整闭合后同例验收成本、接受域、bytes、运行和作者负担；不等待全部扩展 |

具体 API 与例子见 [原 tensor 源说明](tensor-original-source.md)。当前源是 positive
rectangular **temp-bound** nest 的单 leaf operation、一个 tensor；真正循环 literal
`<5`、多 statement body、loaded dynamic dimensions/stability 和完整原 BT 仍有
独立接入义务。空 outer 目前安全回退，正域才进入模型和 restoration 证明。

## 可复核证据

独立 proof report：`build/tensor-original-source/proof/report.json`。
SHA256 `2ff5cae0461440cc9d5c76c5872db90a2736f4c4d2b72ea8d5ea1f6ca8839c94`。
15 个入口模块／291 个本地依赖；111 端点＝旧 66＋新 45，53 闭合。
源／guard／restoration 的语义端点最多继承 6 项 CompCert globals；4 个新增
mapped／tiled candidate 端点继承原 checker baseline，最多 14 项。无新增 global
axiom，kernel 闭合。描述器与数学 box 的关键端点闭合。打印显示中的任何意外
额外 assumption 都会拒绝报告，不以忽略名字解决审计失败。

独立 extraction report：`build/tensor-original-source/extracted/report.json`。
SHA256 `e916cdfb9986399466d056d0670e39433ea2962d977e00c311f774f1d2d7568a`。
12 项实际 OCaml 执行：正确 Horner 源识别；changed RHS／wrong rank／unknown
coordinate／unused read 拒绝；box／负系数接受；宽 columns／负 coordinate 拒绝；
从源 descriptor 所得 instruction 的 mapped／tiled candidate 接受；zero tile 拒绝。
该运行只执行 syntax checker、数学条件、candidate checker 和 lowerer，**没有
执行生成 Clight、实际机器坐标 guard 或完整 C/assembly 程序**。

旧动态布局 proof（33）、旧 backend proof/extraction（66／7 cases）和已安装
invariant compiler proof/native 报告均重新 validate，绑定及原证据保持。旧 C/native
calls 不能计为新动态 tensor 源的运行证据。原 Makefile、既有复现／fetch helper 和
外来未跟踪文件保持。

## 下一项

1. 为这份 BOX 充分条件构造实际安全的机器检查，明确 extrema 运算的溢出界、
   short-circuit 许可和 scalar profile；不得直接把数学 Z boolean 当作 Clight code。
2. 连接 literal-bound transport 和保留原 AST 的 region checker/factory，自动生产
   shape／freshness／used-parameter 和局部证书；公开出口使用本轮已证 restoration。
3. 交付 private resource、progress 和合法 placement，安装经 kernel 组合的 guarded
   replacement 到语言 host／Csem→Asm；提取并运行完整 C 接受、拒绝和上下文。
4. 在同一个闭合实例上继续紧凑条件／成本与三方作者工作比较，随后扩展域与 BT。

不将本轮局部执行桥、可执行 descriptor 或新增模块数量视为完整目标完成。
