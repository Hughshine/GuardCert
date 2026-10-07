# 阶段记录：空构建复现与 constant-word language guarantee

日期：2026-10-07。接续 main `3bd0ef4`；本阶段入口提交 `beea7d4`，修复提交
`1d3acc0cb8a38341ba105ba321e745e9b3a0704b`。完整目标保持 active。

## 从空项目产物重建

[复现入口与命令](nested-frontend-reproduction.md)导出固定 commit 的 1,853 个
源码文件，初始无 build／vendor／编译对象，恢复 checksum-pinned CompCert 与
固定 Git blobs／patches 的 PolCert。复用已安装工具链，不宣称重装 opam packages。

第一棵空树暴露 audit query 的未编译 baseline checker 依赖。补齐两个根模块并
预检查后，从修复 commit 重新导出第二棵空树；没有把修补树称为完整复现。
第二棵树 `/tmp/guard-clean-nested-20261007-r2` 的完整 pipeline 通过：

- 目标 CompCert proof 与 585 GuardCert／PolCert dependencies 编译完成。
- Standalone audit 绑定 884 source digests／767 objects，直接查询 20 个端点；
  compiler 为同一 42-global 集合，kernel 闭合，零新增 global axiom。
- 原提取脚本生产实际 compiler，调用相同 `compile_ncs_frontend_regions`。
- 新树重跑 48＋714＋238＋27＝1,027 successful full assembly calls，另两次
  错误无 guard 变体的真 dependence counterexamples。
- 16＋357＋238＝611 Clight calls 与 6＋10＝16 selected-store GDB probes 单列。
  全数组、headers、public exits 与 context markers 按原模型／reference 对照。
- 14 个 pipeline 步骤全部返回 0，最后只读验证新树 proof／outputs／probes 绑定。

Reproduction report SHA：
`e7e7b1422f84825f7731c72f59551e835d5e62d3940e553a923eaa92587d4afa`。
Standalone proof SHA：
`65e5a4492b762aa629da81628ba2ea9d857c641f3ee168402418678fae6f4284`。
新 compiler SHA：`dbe2035ef71cff5ca1030eeb536b965db273a19b2cec2268f61791ad58a66a79`。
这些新报告不覆盖历史报告。不同 compiler digest 不构成失败：本阶段建立源码
可重建性及证明／行为复现，不声明 bit-for-bit identity、source class 扩展或收益。

## 紧凑条件的实际语言基础

[CompCertWordObservation.v](../prototype/interface/CompCertWordObservation.v)证明
成功 `Mint32` stores 写入原观察已有的 word 时，固定 cell 的观察保持，允许
写到同 cell。成功 load／store 的 alignment 排除不同 cell 的部分重叠；不能
推广到任意 chunk／byte store。不同 word 的同 cell store 另有改变观察的定理。

Actual Clight BODY 的 Boolean checker 支持 typed dereference constant-word
assignment、skip／set／sequence／if。Checker soundness 生产 statement
classification；实际 `exec_stmt`、cast、`assign_loc` 和 `Mem.storev_store` 生产
真实 store chain，再生产 observation guarantee。Field lvalues 被拒绝以排除
bitfields；没有用未验证的 source/model callback 或用户的“所有 stores 是常量”
断言代替这条执行对应。详见 [语言库与下一使用者](constant-word-observation.md)。

7 个端点审计通过；checker soundness 闭合，memory 端点使用 4 项已有 assumptions，
actual execution／最终 BODY guarantee 使用查询到的 6 项 memory／Clight 基线。
零新增 global axiom，kernel 未改。Word-observation report SHA：
`c41d8275f74d0a74673d31eab25628a4d0a480ee5c114f65d9d5206e2d99139b`。

这是 fixed-address memory guarantee，不保证 temp／pointer bindings、source progress
或检查读许可。它也不证明任意 constant-store BODY 可重排。候选正确性、入口
到模型的推导及语言安装仍消费各自证据；当前 compiler 没有启用新 shortcut。

## 文档、论文与下一项

已同步 current plan、责任说明、narrative 实现核对，以及 actual manuscript 的
case study／evaluation／README／evidence map。离线 Tectonic 编译 14 页并核对
变更页；paper report SHA 为
`c0d0ff47db2260cfdb9523d240b9ef0ee2928bda63685d49f9131426a3a14544`。
Paper build 不重跑研究实验。

下一项将 word BODY guarantee 接入实际 guarded producer：用已许可 capture 的
缓存比较生产 header-word 条件，完成 prefix／model anchor／actual entry 运输，
复用 protected frames、候选与 host。运行 header/data alias 的新 fast 输入及
不同 word 的回退，比较逐点 scan work 和完整成本。Source／domain 扩展、完整
BT 动态布局／delinearization、接受域、成本和作者工作量仍按主计划验收。
