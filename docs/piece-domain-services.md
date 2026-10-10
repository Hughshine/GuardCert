# 分片域与坐标：已经证明的服务和剩余执行桥

本阶段落实 [narrative](topdown/paper-narrative.md) 的 domain 责任，不扩展最小
kernel 或 language／host laws。它补的是实际多面体 codegen 的表示缺口：一个
源语句可能展开成多个不同深度的候选 pieces。完整候选能否安装仍需动作、参数、
次序和真实执行证明；域证书不能单独授权 rewrite。

## 用户／optimizer 提供什么

[piece_coordinates](../theories/PolCertPieceCoordinates.v) 是纯数据：实际 candidate
domain、candidate→source 的仿射 `embed`、source→candidate 的仿射 `project`。
每个候选 piece 的宽度由 `project` 的输出数确定，所以同一家族可以包含不同深度。
这里的 source 坐标是已检查 phase 的完整 tiled model 坐标，含 parameters、tile
axes 和原始 point axes。它不要求原调度与新调度的 timestamps 相等。

Optimizer 还提供一个有限覆盖树：`CoverPiece id`、`CoverEmpty` 或
`CoverSplit row yes no`。树、映射和候选均不受信任。一个 native search 可以产生
提案，失败或预算耗尽时拒绝；不能把 search 的返回值当作数学事实。

这不是普通 C 使用者的新证明接口。C 使用者仍提交标注源码和 phase 配置；域
实例的实现者接入数据提案及已证明 checker，语言实例接入机器执行和 host。

## Checker 提供什么

| 服务 | 接受时的结论 |
| --- | --- |
| `piece_map_width` | 每一仿射行的 coefficient 宽度正确 |
| `piece_pullback_poly` | 拉回后的约束在输入点成立 iff 原约束在映射点成立 |
| `piece_equal_maps` | 两个仿射映射在该点的输出完全相等；输出数不同则为空域 |
| `check_piece_coordinates` | 候选点映入有效 source domain，且 project(embed(candidate)) 恢复候选点 |
| `piece_image_domain` | 用 project 拉回 candidate domain，并要求 embed(project(source))=source |
| `check_cover` | 每个 source domain 点至少落入一个实际 image domain |
| `check_disjoint_family` | 不同静态 pieces 的 image domains 互斥 |
| `check_piece_family` | 上述义务同时成立，每个有效 source instance 恰好对应一个候选 instance |

所有点是任意整数向量，不是对常量大小循环逐点枚举。覆盖树的否分支使用
`neg_constraint` 的整数补集，包含严格不等式需要的减一 slack；leaf inclusion
和 emptiness 使用既有 VPL 证书检查。仿射约束由已证明的纯函数构造，不用
rational projection 代替整数逆映射。

`family_exactly_one` 要求实际 source index 的长度正确；结论同时给出唯一
piece id 和唯一 candidate index。`family_instance_valid` 排除额外候选点。
单个 piece 的两个 inverse 方向分别由 candidate-domain check 和 image-domain
定义建立。互斥不仅是每个 piece 内部的条件，也涉及不同静态 pieces。

## 如何接到真实执行

拟接线保留 phase 的完整 tiled model，而不是仅返回 generated Loop 和 tiling
witness。随后使用两个不同的证明步骤：

1. 将实际 candidate pieces 按 `embed` 重定时到共同 tiled schedule；域／坐标
   证书，加参数前缀与动作检查，构造已有 `memory_point_isomorphism` 所需证据。
2. 将重定时的七片模型与实际提取的七片模型交给既有依赖 validator，证明实际
   candidate 次序。这一步允许 schedule 改变，不能省略依赖与可交换性。

这避免把两语句 source 与七片 candidate 塞进等长 positional attachment，也
避免用 timestamp 相等去证明优化的重排。随后还要接 source Loop→checked
phase model、candidate model→actual Loop，以及 host 所需的独立 progress。
现有 safe machine lowering、private/public frame、公开出口及 current-program
Csem→Asm 安装继续复用。

本阶段 **尚未建立这些动作／参数／次序／Loop 桥**。新的 native 检查是诊断，
现有 compiler 的最终 checker 保持安装权限；整体 fusion2 仍未安装。真实提案
结果与失败要分别记录，不能把完整输出匹配当作该变换已支持。

## 验证与责任边界

[审计摘要](piece-family.json)绑定五个模块、443 行、13 个查询端点：四个 closed，
最多八项既有 globals，无新增。十二次编译尝试含七次失败和五次成功，失败
snapshots／logs 保留。依赖和来源共绑定 11,194 项。代码行数包含连接及既有
模块实例化，不作为作者负担减少的测量。

这些服务消费已建立的参数 facts；不产生 runtime guard，不证明新 Clight 算术
或读取安全，不提供 OLO 的 compact entry 推导。`C_opt` 的完整执行证据、
`B⇒A`、safe `G accepts⇒B`、entry transport 和 host 安装保持各自责任。
完整顺序 PolCert／CGO17 验收及性能比较继续开放。

## 原 fusion2 的实际提案检查

[结果摘要](piece-family-results.json)绑定 15,886 项来源，包括现有完整 compiler
的诊断后继、原源码三配置 replay、真实 source／candidate domain 与映射 receipts、
覆盖树和负例。输入 hash 与前序一致，保留 double 数组和原计算；三个完整输出
匹配。新模型数据来自实际 extractor 与 imported tiled phase，不是手写目标。

| 实际提案 | 源 instructions | Pieces／深度 | 检查 |
| --- | --- | --- | --- |
| Untiled whole candidate | 2 | 6：1,1,2,2,1,1 | 六坐标检查、两 parent families 通过 |
| Tiled whole candidate | 2 | 7：3,3,4,4,3,3,3 | 七坐标检查、两 parent families 通过 |

例如 tiled 第一片在 `(p,u,v,q)` 上执行 A，参数表达式为 `(-q,q)`。
`embed` 产生共同 model 的 `(p,u,v,-q,q)`；`project` 从 `(p,u,v,x,y)`
取 `(p,u,v,-x)`。其 image 额外要求 `x+y=0`，与实际候选的 `q=0` 域共同
限制到原单点。Checker 验证这些公式，而不是假定边界 peeling 语义。其他片
包含完整二维点、行尾和末端边界；四个 parent families 的 union／disjointness
均经提取的 checker 检查。当前实例的 `p=100` 来自精确 literal facts。

[负例](piece-mutations.json)用同一提取的 checker 复查四个实际 families：正确
见证均通过；更改 project、移动 embed、漏掉一片、重复一片共16项拒绝。移动
embed 检查的是完整 family：单片映入另一个合法 source 点可能仍满足 inclusion
和 candidate inverse，却改变覆盖／互斥。第一次负例预期错误保留，不能据此称
单片 checker 失效。首次 standalone 执行缺 CompCert configuration 的失败及
初次 native build 来源变化的拒绝也保留，均排除出有效结果。

最终 selected Clight 与前序相同：untiled 四个 for／最大深度二／八个 if；tiled
八个 for／最大深度四／16个 if，仍是两个单独 tiled nests。这里的 if 包含控制
条件，不是 OLO entry guard 数。域检查通过并未授权安装整体 fusion，也没有
增加全程序 theorem、动态条件推导或成本结果。
