# Checkpoint：安全机器坐标条件生产候选输入

日期：2026-10-07。后继于 `f7aa6ce`，完整目标 active。
重新 fetch 并读过 narrative `271f6fc`；与 main 正文一致。最小 kernel 止于
local guarded correctness；语言 host 与具体 site 负责全程序安装。Proof-first
顺序和 OLO 的功能／usability 要求继续作为验收，不把局部桥当作目标完成。

## 完成什么

五个新 Rocq 模块：

1. `GuardMemoryTensorBoxExpressions` 从 affine 坐标生成 axis／scalar extrema，
   覆盖负系数、零系数及每个 read/write，证明符号条件与数学 BOX 相等。
2. `ClightTensorBoxGuard` 连接既有 signed32 affine compiler，实际 profile checks
   接受后执行安全条件算术，交付真实 decision_run／标准 readonly certificate。
3. `ClightTensorCompleteGuard` 在原 source-derived layout 前缀之后连接 profile
   与坐标条件。原有限正常完成许可读取；接受生产 INITIAL／bounds／dimension
   view／layout／BOX。数学 singleton MAX_SIGNED+1 不变成实际溢出加法。
4. `ClightTensorCompleteCandidates` 从真实原执行和真实 full guard acceptance
   生产 pointer／count／scalar bindings、range、BOX、Loop SOURCE，再消费原
   affine／tiling checker，生成候选实际执行和 public iterator restoration。
   调用者不再提交这些独立语义前提；静态 metadata 证书仍需 factory 生产。
5. `ClightTensorBoxExample` 验证 safe compilation、unknown dimension／溢出式
   静态拒绝、负系数，以及实际 coordinate guard 接受、宽坐标／超 profile 拒绝。
   完整 guard 在 n=0、后续 temps 未定义时安全拒绝也已证明。

参数 profile 由 runtime checks 证实，不是用户语义 callback。静态 lowerer
拒绝可能越 signed32 的 extrema 算术；runtime profile 外保守拒绝。
本例生成 code 随 access/coordinate 数量增长，无域内 scan；实际运行成本和
代码 bytes 尚未测量。Context 重复 n／ld 检查仍未简化。

## 责任和剩余难点

| 链／责任 | 具体已证部分 | 未闭合部分 |
| --- | --- | --- |
| Kernel | 消费 readonly condition；既有最小定义保持 | 新 local preservation factory 尚未交付 |
| C_derive，domain | affine extrema→全部活动坐标 BOX；source/entry views 对应 | 非矩形 projection、多 tensor footprints 不在当前实现 |
| C_guard，语言/domain | 真实 layout/profile/坐标短路检查；原 source-defined D；纯检查保持入口 | 新 frontend 安装尚未发生 |
| C_opt，domain 使用语言服务 | 实际 source→旧 model/checker→实际候选，全 memory 和 public temp 出口一致 | 更多源／多 statement recognizer 尚待扩展 |
| C_host，语言与 site | 本轮无新整程序定理 | AST data factory、literal-bound transport、source progress、private allocation、合法 placement／Csem→Asm |
| 功能与 usability | 生成紧凑 affine entry condition，支持真实读写 source | 同例完整接受／回退、guard cost、bytes、机器运行和作者责任比较 |

当前范围仍是 positive rectangular temp-bound nests、单 Horner-address leaf、
一个 tensor。无新的整程序 compiler、C/native 运行、性能结果或完整 BT 覆盖。
Normal-completion D 不代替程序 reachable-state progress/divergence。旧 native
结果保持其原 source class，不能充当本轮 tensor 运行证据。

## 可复核证据

Proof：`build/tensor-coordinate-guard/proof/report.json`。
SHA256 `deeb2b67bd7dbbe87459ead7d2c62f2c5f5863af27e2c8815f14b09f193852ec`。
20 entry modules／306 required dependencies；142 端点＝此前 111＋新 31，
69 闭合。新语义端点最多继承 6 个 CompCert globals，两个 candidate execution
端点继承原 VPL/PolCert checker baseline，最多 14 项；零新增 global axioms，
kernel 闭合。Extrema 编码与 signed/profile correspondence 的关键端点闭合。

Extraction：`build/tensor-coordinate-guard/extracted/report.json`。
SHA256 `9df367b1b737cbed002f25ded637e063c2a80e128c6c128bcf4202ee5bdbfe2a`。
13 项实际执行：原坐标／负系数编译成功，中间溢出／unknown dimension／profile
arity 静态拒绝；正坐标／负系数接受，宽 columns／components／profile 外 stride／
负 coordinate 拒绝；alpha 的 signed32 两个极值接受。实际运行 synthesizer、
Clight lowerer 和数学 flag；生成机器 guard 的执行对应由 Rocq fixture 定理
提供，该 executable 不执行 Clight 或完整 C。

## 下一项验收顺序

1. 为实际原 AST 交付 region descriptor checker/factory，自动生产 source shape、
   freshness、used-parameter 和 protected-name 静态证书；消费现有 full condition
   和 source/candidate execution bridge，包装 kernel local certificate。
2. 连接现有 literal-bound transport，证明 source progress 与可用私有资源，
   再通过 language host 安装到 Csem→Asm；scope 失败或条件失败保留原 AST。
3. 提取完整编译器，实际 C 接受／回退／多 site 和上下文运行验收；区分真实
   候选执行与原程序 fallback，核对 full memory 和公开退出值。
4. 对同一闭合子集开展 OLO 对照，分开接受域、生成 code、runtime work 和人工
   工作，再扩展 source/domain、跨 tensor alias 和原 BT。
