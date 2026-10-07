# 原嵌套源 capture／numeric 输入生产：阶段交付

2026-10-07。完整 goal active；本阶段不声称已安装 OLO Figure 2 优化。
接口、输入前提、输出锚点及三方责任见
[nested-constant-numeric.md](nested-constant-numeric.md)。

实际改动：语言从原源活动路径生产 first leaf；domain 消费 checked 参数使用
结果，取得 header caches 及 BODY 参数的整数定义性。实际 ordered capture 和
两个 positive-count gate 接到旧 numeric probe，接受后生产完整 math domain 和
outer scan 的逐点 DOMAIN／SOURCE_WORDS。原源完成是安全域的输入；缓存源完成
和未来观察稳定性都不是检查许可的前提。整段检查保持入口 memory 和公开 temps。

具体 checked package 的 store value 使用额外 BODY 参数。Package 接受、公开
result scratch 拒绝、numeric 接受／超 profile 拒绝已证明。空外层／内层的实际
Clight gate 在 BODY 参数、output pointer 和 source counters 未定义时仍正常拒绝。
它们不等于新完整程序运行。

## 验证记录

- 24 endpoints：6 language／11 domain／7 fixture；565 required dependencies，
  1,076 源摘要。新端点最多使用六项既有 CompCert globals；kernel 闭合、无新增
  global axiom，旧完整 compiler 保持 42 项 assumptions。
- 新 proof／validate 通过；父 model、outer、inner、BODY joint、constant model、
  nested-header 报告的源／对象绑定全部保持。
- Loaded-offset 完整 compiler proof／native／path／guard-work **绑定核对**通过：
  708 汇编调用、236 Clight 调用和 21 机器探针仍是其原报告，未重跑新矩阵。
- LNCS working draft 同步 case-study、evaluation 和 evidence map；离线构建
  12 页，无 overfull 或 undefined 引用。渲染检查第 7、8、10、11 页通过。

Proof report：`build/nested-constant-numeric/proof/report.json` SHA-256
`0574bda833e58435b2d8000f9c70284d0bec95bfb2320acd0c8cf9dbf29bead8`。
Paper report：`build/paper/report.json` SHA-256
`da251cc98d47b0445b3ec78cc440d2e2137e265e743ecd3300f335f609fc5c96`。
没有新 compiler、extraction、native、timing 或 empty-build bootstrap 结果。

## 剩余连接

1. 将 produced DOMAIN／SOURCE_WORDS、实际 observer receipts、helper 初始化和
   namespace／scope 绑定到现有 outer physical scan。事实锚定 captured entry，
   后继实际入口的 frame／private mapping 仍须组装。
2. 用 data-only 原 AST site checker 生产完整 guard certificate；接 cross-entry
   candidate、typed pool、原 fallback 和语言 host，取得新 Csem→Asm 入口。
3. 提取并运行 Figure 2 适配原 C 的接受／拒绝／empty／overflow／alias 路径。
   功能闭合后，同源同候选验收 compact conditions、检查成本／有用接受域及
   实例作者工作；不把 endpoint 数当作这些指标。

本轮重新 fetch narrative，远端仍是 `271f6fc`。最小 kernel／核上库／语言
安装边界、三方归属与四个逻辑环节、proof-first 及并行实际稿件要求继续有效。
