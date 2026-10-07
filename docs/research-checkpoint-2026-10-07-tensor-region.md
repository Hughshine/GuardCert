# Checkpoint：真实 tensor source 到完整 guarded compiler

2026-10-07，后继于 `b41b00f`。重新 fetch／读完 narrative `271f6fc`，main 正文
一致；[澄清核对](narrative-implementation-check-2026-10-07.md)已将三方责任、
四条逻辑链、局部／安装边界和 proof-first／usability 顺序纳入工作计划。
完整多面体目标继续 active。

## 已交付什么

六个新 Rocq 模块：

1. `ClightLoopAdministrative` 证明行政 skip 的完成执行等价和 quiet／writes
   证书运输；保留 loop header／increment、labels／switches。
2. `ClightTensorRegionPackage` 从实际 AST 和 metadata 数据构造 dependent package，
   自动核对 shape、namespace、实际参数使用与 box guard compilation。
3. `ClightReadonlyPreservationKernel` 将 readonly local rule 接到实际 kernel
   `guardify_preservation`，并连接语言 choice realization／projected contract。
4. `ClightTensorRegionPreservation` 消费 full guard 和既有 mapped／tiled checker，
   从原实际执行取得同一最终 memory 和公开 iterator 出口，保留原 fallback。
5. `ClightTensorRegionCompiler` 核对 private pool／共享 Boolean／实际 table，
   复用原源 progress、scope 与语言 continuation host，组合到 Csem→Asm。
6. `ClightTensorRegionExample` 验证普通／前端 skip-wrapped 源接受，错误 reset、
   未许可 dimension、重复／未用 scalar 和空 profile 拒绝，核对原源 progress。

新 native proposer 只提出三个 axis 的 Horner RMW 数据和 schedule／tile sizes。
Factory 重新核对所有提案。实际 C initially 全回退的原因已定位为前端 leaf
sequence 包装，并由上述语言定理修复；原 kernel 和 tensor source／box modules
保持。完整源码／接口说明见 [tensor region compiler](tensor-region-compiler.md)。

## 证明和实际执行分开验收

Proof report：`build/tensor-region-factory/proof/report.json`。
SHA256 `640d768bbbe74f456e04c7bfbbf848f994fbcaa6c4018c31ecc82a32feb4e4e3`。
26 entry modules／368 dependencies；181端点＝旧142＋新39，89闭合。
新语言运输继承原六项 Clight baseline；compiler 的42 globals来自原独立查询的
CompCert／checker baseline union。Kernel 闭合，零新增 global axioms。

Native report：`build/tensor-region-factory/native/report.json`。
SHA256 `0a3fb6525463765c330321beafe1c636a3ba0257666e7ca27c48929e9926887d`。
Compiler stamp 绑定实际入口、proof sources／objects、提取配置、native policy 和
binary。实际新编译，不把旧 compiler 的输出当作本轮证据。

六配置 disabled、identity、interchange、2×3 tile、wrong-reindex、zero-tile，
每配置36次调用，共216 assembly calls。三个函数分别含一个 region、连续两个
region、带前后 memory effects／goto skip 的 region。每次核对1,024个完整数组
words、最终公开 counters、首个 region 的出口和外围 markers；与 GCC -fwrapv
reference 及独立 word model 一致。

实际 Clight table 安装：identity／interchange／tile 各在三个函数安装1／2／1
sites；两个非法提案全部静态拒绝。动态矩阵覆盖 positive layout、RMW 值 wrap、
两个 signed32 极值、坐标不在 layout、profile 外、非零 root、空外／中／内层及
goto 跳过。数组模型包含源地址合法但 guard 保守拒绝的输入。

三个已安装配置另执行108次插桩 Clight calls。每配置观察12 fast／35 refusal
dispatches；重复 sites 带来多个 dispatch，goto skip 不执行检查。该插桩由 GCC
运行打印 Clight，明确不是未修改汇编的路径探针。本轮没有新增 GDB probe。

| 配置 | 单 region bytes | 双 region bytes | context bytes |
| --- | ---: | ---: | ---: |
| Source | 218 | 345 | 317 |
| Identity | 622 | 1,137 | 707 |
| Interchange | 624 | 1,154 | 708 |
| 2×3 tile | 870 | 1,627 | 952 |

Code size 是 linked function 的观测，不是 guard-only 成本或净收益。

## 责任与剩余验收

Kernel 消费 local certificates；语言库负责机器 checks、skip 运输、readonly frame、
shared choice、private allocation 与安装；domain 负责源／模型／candidate 对应、
坐标义务和公开出口。Site/proposer 只提交数据和实际片段，成功后由 checker
生产证据。使用者没有新增 SOURCE、BOX、bindings 或候选出口语义 callback。

当前 class 是 positive rectangular temp-bound nests、单 Horner RMW leaf、一个
tensor。Literal-bound transport、更广 body／affine domain、跨 tensor alias、
loaded-bound stability 与完整 BT 仍待推进。此子集的端到端链现在闭合，下一项
按 narrative 立即做同例成本／接受域／作者负担比较；不等所有扩展完成。
仍无新入口的完整计时、check-work 分解或 source-only rebuild 结果。

独立复现：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_region.mk native
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_region.mk validate
```

原 tensor backend／source／box 和 nested-invariant 的 validate 全部通过，原 reports
的摘要保持。论文 evaluation 与 evidence map 随本阶段更新，不声称完整 OLO
能力、最优 guard 或性能收益。
