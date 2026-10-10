# 逐语句坐标平移：完整 fusion1 已安装并执行


本页保留point-origin checkpoint当时的结果。后续[共同坐标与stencil整段融合](double-tree-common.md)已关闭本页stencil拒绝；tricky3、general piece correspondence和OLO条件工作仍未完成。

原 `fusion1` 的两个 marked 兄弟循环现在被同一个 guarded replacement 替换。
候选有一个循环，第二个 assignment 在 counter 至少为 3 时执行，并使用
counter 减一后的原坐标。原 `0.33` IEEE 运算树和数组声明保留；接受分支
结束后恢复两个原 source counters，拒绝分支包含两个原循环。

另外两例的完整 marked region 尚未优化成功。此次没有实际 tiling、速度收益、
完整 corpus 覆盖增量或 OLO compact-condition 完成的结论。

## 原来为什么被拒绝

已证明结果相等的 compilation-only trace 区分了实际阶段：

| 原完整候选 | 旧路径实际拒绝位置 | 本次处理 |
| --- | --- | --- |
| fusion1 | 最终 adapted Loop 检查，未进入 machine lowering | 合并 peeled prefix，增加逐语句坐标平移证明和检查；完整候选已接受、lower、安装 |
| multi-stmt-stencil-seq | affine dependence validation，未进入 tiling import | 完整候选仍拒绝；发现送给外部调度器的源顺序编码反例 |
| tricky3 | 最终 adapted Loop 检查，未进入 machine lowering | 完整候选仍拒绝；原四个 assignments 在生成候选中有十九个静态 copies |

现有 tiling attachment 是 positional 的。新
`double_tiling_attachment_cardinality` 证明它接受时 source、candidate、witness
列表长度必须相同。fusion1 的原提案有三个候选 copies、两个源语句，至少
违反该接口的必要条件。tricky3 同样需要更一般的 piece correspondence；
不能将新坐标平移服务称为 domain-partition checker。

stencil 的 exported source schedule 出现了具体顺序倒置。在 `N=16` 时，
第二段的 index 2 被编码为 timestamp `(1,2,1,0,0,0)`，第三段的 index 3 为
`(1,1,3,1,0,0)`。后者排在前者之前，而原 C 完成第二段后才进入第三段。
这要求检查 source-tree 的共同 schedule 坐标，不能仅修补候选点坐标。
后续修复 exporter/producer 的顺序信息，仍由实际 source 的 verified validator
裁决提案；此次没有绕过依赖验证。

## 一个完整流程

以下是保留原 bodies 的说明性伪代码：

```text
source:
  for i = 1 .. N-3: A_body(i)
  for j = 2 .. N-4: Out_body(j)

candidate:
  for k = 1 .. N-3:
    A_body(k)
    if 3 <= k: Out_body(k-1)
```

外部 scheduling 和 prepared codegen 提出带前导段的真实 Loop。不受信任的
coalescer 提出上面的单循环形状；每个 assignment 的点坐标 shift 是 `[0,-1]`。
最终检查器核对实际候选的 domains、typed instructions、tiling representation
和 dependences，不能因为 proposer 声称合并正确就接受。

`double_point_shift_execution` 证明逐语句常数平移保留 parameter prefix、时间戳
和实际 IEEE/Mem execution。Domain constraint 的 bound 与 affine expression 的
bias 使用相反的修正符号。服务处理一个指定坐标上的逐语句常数平移；当前
检查器用于 swaps 后的第一个点坐标。它不是任意 affine isomorphism。

Guard 复用前序 source-licensed capture、private cache、signed profile 和
footprint 推导。新 factory 消费 shifted final checker，再进行实际机器 lowering、
public-exit restoration 和 fallback。已有 language host 接入当前程序；
`compile_selected_shifted_double_tree_program_correct` 给出同一原 Csyntax 输入到
Asm 的 backward simulation。没有源 C 用户提供的动态 model callback。

## 责任和难点

| Certificate | 本实例的生产者与责任 |
| --- | --- |
| `C_opt` | 多面体实例：逐语句坐标对应、实际候选 domain/dependence 验证；coalescing 与 shift 表是 untrusted data |
| `C_derive` | Domain 库与 checked factory：profile/footprint、cache encoding、源/模型对应和候选机器范围 |
| `C_guard` | Clight 库：首次原 comparison 许可读取、安全截断前检查、条件 capture、短路和 private/public frame |
| `C_host` | 已有语言 host：source progress、scope、private allocation、placement、current-program lifting 和 CompCert backend |

最小 kernel 和 host laws 保持。点平移属于具体优化实例的表示服务，不能
归为 kernel 自动发现 assumptions，也不能替代 safe guard encoding。

下一项困难是 shared schedule coordinates 和 source-to-many candidate pieces 的
完整覆盖/互斥/执行对应。需要实际接入 source ordering、partition certificate
及 coordinate witnesses，保持原 Clight 到最后实际 lowering 的证明链。
OLO 的 compact entry-condition derivation、条件简化/复用和成本单独推进。

## 验证和范围

九个新 Rocq modules 共 859 行，查询 26 个 endpoints，13 个 closed；最大
42 项原 globals，无新增 global assumptions。Audit 追踪 565 个 reachable
sources、绑定 10,405 文件，并保留 16 次 module 编译尝试。证明摘要为
[double-tree-shifted.json](double-tree-shifted.json)。新的 complete compiler
实际消费这些服务，已提取并构建 native compiler。

三份原冻结 C 分别运行 unmarked、requested untiled、requested tiled、错误
shift、收紧 profile 五种配置，15/15 完整输出匹配同源 GCC references。
Unmarked 和错误 shift 都零安装。Fusion1 在两个普通 marked 配置安装一个
完整 fused region；stencil/tricky3 分别安装四/两个内部 regions，不能计作
完整 marked-tree 成功。Requested tiled 的 fusion 仍是同一个未分块形状。

收紧 profile 的 fusion1 仍安装完整 guard：upper cap 为 4，原固定 `N=4096`。
根据 emitted checks 和原输入可以推出拒绝并走 fallback；输出匹配。没有新增
实际机器 guard-branch 插桩/观察，且常量输入可能被 backend 折叠，不据此报告
动态 guard 成本。没有新的 timing 或全部 sequential configurations 验收。
Native 摘要和报告 hashes 见
[double-tree-shifted-native.json](double-tree-shifted-native.json)。

成功源码、objects、helpers、输入和 reports 已冻结。失败 proof/build/audit
的源码与日志另存；旧子循环-only 报告保持，不回写为整段成功。
