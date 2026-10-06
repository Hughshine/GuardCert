# 2026-10-06：源观察与符号化 pointer 片段

后继 main `cd8c228`。本轮从“`p+k` 可访问不蕴含原始 p 可以比较”的语义缺口继续，实现保留源 load prefix 的观察证据、实际包络条件、全部 footprint 对应，以及消费原候选证书的 checked fragment lowering。完整研究目标仍活动；此阶段尚未安装新完整 compiler 或提取／运行新路径。

## 实际证据链

| 交付 | 已证明的边界 |
| --- | --- |
| [SourceObservation](../prototype/interface/ClightSourceObservation.v) | 普通 int32 源读取的实际完成执行提供 valid-pointer receipt；静态 coverage/freshness checker；保护 frame；保留前缀、在其后安装条件 body 的正常 region contract |
| [PrivateScanShortcut](../prototype/interface/ClightPrivateScanShortcut.v) | 在许可观察的域中，readonly sufficient condition 接受执行同一候选，拒绝进入原 private scan；两条路径消费 kernel 保持定理，不重证 candidate C_opt |
| [AffinePointerEnvelope](../prototype/interface/ClightAffinePointerEnvelope.v) | 实际 signed pointer-equality test、两方向包络比较的精确 Boolean 解释及全点 soundness、同 base 的 modular 四字节单元分离。编码和正／负算术例子均编译通过 |
| [ParamPointerEnvelope](../prototype/interface/ClightParamPointerEnvelope.v) | header 对实际 counts／parameters 的机器表示；全部访问对条件生成；通过原 footprint member 定理覆盖所有真实 cells；接受建立原 P |
| [ObservedPointerPreservation](../prototype/interface/ClightObservedPointerPreservation.v) | 从真实 source prefix 得到附加观察域，把 source/candidate/condition 接到原有限 private-region 宿主；不对无 prefix 源假设 base-valid |
| [ObservedPointerCandidate](../prototype/interface/ClightObservedPointerCandidate.v) | 从原 checked lowering 的成功结果取得绑定实际 AST 的 rule witness；检查 observations，输出前缀＋新快捷条件＋原 candidate/scan。调用者仍证明其 candidate check 的证书性质 |

三方责任和使用步骤见 [接口说明](source-observed-affine-separation.md)。语言无关 kernel 没有修改；domain 包络与真实语言原语分开。原 candidate checker、源／模型对应、private names 和 scan 继续复用。依赖库及端点数量不构成 proof-burden 或性能测量。

## 审计与兼容性

`make interface-pointer-envelope-proof` 已通过：17 个公开端点、474 项实际 user 依赖、835 份源码摘要。新端点没有 CompCert 35 项基线之外的全局假设；conditional candidate certificate 是显式输入，实际使用原 PolCert/VPL checker 的完整 compiler 仍继承其原有七项假设。这不是从完整优化证明中去掉了这些假设。

当前审计 report：`build/interface-pointer-envelope/report.json`，SHA-256 `c6358bbbc79ec96de84594c66889a43535e2e876c4884481aad5b017ad0d42a9`。脚本 SHA-256 为 `1181cf49931e046226997a379f3f27dce2b7fa3fdcc3a4cc22faa56aa7d08439`；报告绑定 actual sources/.vo、审计端点和固定 Rocq 工具链。改变 proof sources 后应重新运行审计。这次逐项编译新增／变更模块和必要依赖，没有声称重建整个 CompCert。

已有产物绑定核对均继续通过：主接口 415 端点／864 摘要、25 配置／40 报告与 40 份原 C／Clight 摘要保持；named 40＋8 配置；参数化 readonly 29 端点／134 配置／十个探针；private-scan 38 端点／15 配置／四个探针／三个上下文配置。此处核对的是已有报告、脚本、源码与实际 compiler/binary 的绑定，本轮没有重跑这些 native 配置或将它们用作新快捷路径的执行证据。

三个评审分支再次 fetch 后保持 `f793629`／`9673381`／`3e9f008`，无新增意见。现有意见的验收继续体现在观察安全、B 对所有 A 的覆盖、实际模型对应和三方证明责任；详细归档见 [评审整理](review-synthesis-2026-10-05.md)。

## 下一项仍必须完成

新片段 lowering 已产出实际 Clight AST，但还没有 normalized C frontend 的 prefix matcher、完整 mapped／tiling／schedule proposer 路线或新 Csem→Asm 入口。下一项应完成这组连接和提取，然后以 actual binary／assembly 验证同 base 且包络分离时跳过扫描，不同 base／重叠时仍扫描，缺观察／覆盖破坏时静态拒绝，以及 prefix 值、数组输出与外围 context 保持。数学例子的非空接受域不能替代这一验收。

当前 pointer source 仍是原稳定寄存器 counts 下的受限矩形／参数化访问模型；一般非盒状 affine 域、多个依赖 preload、复杂 effect、成本和作者负担对照继续留在 [完整计划](current-work-plan.md)。本阶段的 library 证明不将它们标为完成。
