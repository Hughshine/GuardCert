# Narrative 复核：责任、困难证明与原案例验收

本次重新 fetch 后，可见 narrative 分支仍为
`8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9`。
[paper-narrative.md](topdown/paper-narrative.md) 和
[context-lifting.md](topdown/context-lifting.md) 与 main 正文一致。
这里吸收已推送的澄清，不声称看到另一个较新提交；实施结果另由
[witness-policy 记录](double-witness-policy.md)和
[固定摘要](double-witness-policy.json)支撑。

## 接口与三方责任

| 提供者 | 交付内容 | 当前实现边界 |
| --- | --- | --- |
| 最小 framework kernel | 消费 check、分支行为与入口关系证书，证明局部 guarded refinement／preservation | `GuardInterface.guardify_refinement`／`guardify_preservation`；两个方向分别证明 |
| 语言／IR 实例 | 实际 check/choice 执行、读取许可、private frame、公开出口、progress 与合法上下文安装 | Clight 语言服务、scoped selected host 和 CompCert backend |
| 优化／domain 实现者 | 实际 source/model 对应、充分前提及入口推导、候选 checker、实际 lowering 接线 | 当前 typed-double factories 与实例化的 PolCert validators／codegen |

支持族的 C 使用者给标注源码和策略数据，不逐 site 提交语义 callback。
新增语言或 source/transformation family 的作者需要提供适用证明。
`C_opt`、`C_derive`、`C_guard`、`C_host` 是证据分工；不是四份必需手填的
用户 record。`C_host` 的 choice 定律与完整程序安装也是两项责任。
通用 context record 消费 host 的 lifting 字段，本身不会证明上下文闭包。

本次扩大相邻交换见证搜索，修改的是不受信任 producer。既有 compiler
定理已量化任意有限 choices；每项尝试仍由 factory 验证。这是复用已有
边界的具体结果，没有新增 kernel、context algebra 或语义公理。

## 条件库分类及契约

沿 narrative 的五类组织已有服务；下表是能力映射，不是新公共 API。
各服务的源族和语义限制继续以链接文档为准。

| 家族 | 已有服务／范围 | 安全调用前提与接受事实的区别 |
| --- | --- | --- |
| 算术与表示 | `memory_long_range_capture`、`memory_long_accepted_int_exact`；I64 bound 到 private I32 | 实际 header load 的许可先成立；接受再给出非负范围和精确转换 |
| 范围与 footprint | `double_reduction_entry_bounds_check_ready`；actual typed layout／affine accesses | 静态声明／layout 与运行时 count 一起推出全部 reached points；单次值可读不证明整个 footprint |
| 内存分离 | [源观察支持的 affine 分离](source-observed-affine-separation.md) | 原 prefix 许可 base 观察；包络 coverage 与机器比较建立充分分离；本次 double-global 路线沿用静态 block 分离 |
| 值与观察保持 | [zero-RMW 路线](zero-loaded-word-installation.md) | 原首点许可 scalar 读取；接受后建立特定 `Mint32` 观察保持，允许部分 header alias；不推广至 F64 或任意 chunks |
| 控制与条件观察 | [依赖 header captures](affine-header-snapshots.md)、range tree 与 readonly short-circuit 库 | earlier branch 决定后续读取是否有许可；空域／拒绝不得偷读未来 child／RHS |

每个可组合服务应说明：安全调用需要什么、读取哪些观察、写哪些 private
状态、是否保持 public temps/memory/events、接受推出什么、拒绝如何运输
fallback。Readonly 指所声明的公共观察；cache/cursor/flag 的私有写入必须
由入口／出口关系覆盖。Refusal 不推出前提为假。

Separation 和 value-preserving writes 可以提供同一稳定性义务的替代充分
条件，但两者都不能替代读取许可。生成扫描不是已经交付的可调用 C runtime
library；若以后改成调用，需要把实际 call/state 契约接到 compiler proof。
库整理和封装不替代紧凑条件推导、接受域或检查成本验收。

## 最难的证明应怎样验收

| 连接 | 证据来源／责任 | 不足以替代它的结果 |
| --- | --- | --- |
| 原 Clight → source Loop | Domain factory 组合实际指令／控制执行定律；static metadata、runtime/capture/transport、原执行 receipts 分别提供适用前提 | Polyhedral validator 接受；一份带未 discharge 前提的 source theorem |
| 局部义务 A ← 入口条件 B | Domain 的 bounds、footprint、header stability 和物理地址证明覆盖全部 reached points | 只检查 first point；只有数学范围而没有机器表示／权限桥 |
| 安全检查与接受充分性 | 语言执行证明、安全调用许可、domain 的 `accepts⇒B` 和 private entry transport | 只证明 Boolean soundness；用未来 cached-source execution 许可当前读取 |
| Source Loop → 实际 candidate → Clight | 固定实际捕获参数的最终候选 checker、candidate progress 和实际 lowering／公开出口证明 | Raw codegen 的 backward theorem；存在某组参数的模型执行；只验中间 schedule |
| 局部片段 → 当前完整程序 | 实际 site 的 scope、资源、placement、source progress；语言 host 再接 Csem→Asm | 只有有限退出关系；沿用旧程序的 site 证据；只运行 native digest |

原源执行是证明的语义起点，不是在优化前运行原片段。`decode` 表示从具体
执行恢复模型执行，不能把单向 theorem 描述成独立双向等价。Repeated
rewrites 要消费当前 intermediate program 的证据，有限序列再组合；无限
运行的搜索不是 compiler output。

## 实施顺序的落实

先运行当前 actual compiler 的全部 62 原案例，再处理暴露的 blocker。
已完成的一次对照发现默认见证漏掉坐标 1／3；新策略已把 `matmul-seq`、
`matmul-seq3`、`tce` 接到现有整程序证明并运行。此次不是停在诊断或新增
模型 probe，也没有缩减 sequential 验收目标。

后续按实际缺口推进：

1. 接通 double 的真实 tiling producer、固定参数的最终生成 Loop progress、
   actual Clight lowering 和 selected Csem→Asm；已有 word tiling 或
   DoubleAssignmentTilingValidator 的实例化不算该路线已安装。
2. 定位 `dct` 的 initialized route 和 `polynomial` 的实际 skew candidate
   拒绝，分别处理逐 site 见证、源 body 和 coordinate/domain 表示；更长的
   swap 列表不能声称支持一般 affine change。
3. 对 scheduler 前回退的 44 原案例逐步定位 actual static checker，扩展
   multiple bounds、statement sequences、非零／inclusive starts 等真实源
   结构。每个扩展同时交付安装证明和接受／回退／context 证据。
4. 保留 tiling／ISS／diamond／two-level／unroll-jam／SIMD 的顺序配置、原
   BT、LLVM／SPEC 和较大输入的验收；Unavailable/frontend 项不删出清单。
   条件尺寸、运行工作、接受域与完整调用成本分别测量。

Novelty 仍需与已有系统在相同义务上比较；局部组合定理、端点数和 native
调用次数本身不能证明贡献。完整 goal 保持 active。
