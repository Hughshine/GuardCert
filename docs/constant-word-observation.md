# Value-preserving stores：紧凑条件的语言基础

2026-10-07。[CompCertWordObservation.v](../prototype/interface/CompCertWordObservation.v)
证明了固定内存观察的保持，并提供 actual Clight BODY 的静态 checker。
这是下一项紧凑条件工作的语言库基础；当前 compiler 尚未使用它跳过扫描。

后继 [实际循环／缓存模型与检查出口](nested-word-model.md)现已消费此保证，
生产相同 word 条件的真实 Clight 检查及接受后的 canonical source/model execution。
它补齐旧文下述 prefix／模型及出口 frame 的局部义务；factory／compiler 安装和
运行测量仍待完成。本文保留最初 7 端点语言阶段的证据边界。

## 已证明的条件

如果 `Mem.load Mint32` 在某 cell 取得 word `w`，后续每次成功的 `Mem.store Mint32`
都写入同一个 `Vint w`，该观察在任意有限次这些 stores 后仍然是 `Vint w`。
Store 可以写到观察 cell 本身；不要求它们 non-alias。

证明分两种情况：同 cell 由 `Mem.load_store_same` 取得相同 word；不同 cell
由成功 load／store 提供的四字节 alignment 排除部分重叠，再使用
`Mem.load_store_other`。这不是任意 chunk／字节写入的性质。另一个端点证明
同 cell 存入不同 word 会改变该观察，不能省掉“原观察等于存入 word”的前提。

## 从实际语法生产证据

`check_constant_word_statement w body` 是 compile-time Boolean checker。支持
skip、temp set、sequence、if，以及 signed32／无 attrs 的 typed dereference
assignment，其 RHS 必须是同样 typed 的 literal word `w`。Unsupported syntax
返回 false；特别是一般 field lvalue 被拒绝，因为 int-typed field 可能是 bitfield，
其写入并不等于完整 `Mint32` word store。

已证明的链为：

```text
actual BODY 的 static checker accepts
             ⇒ constant_word_statement w BODY
actual Clight BODY execution
             ⇒ constant_word_stores w before_memory after_memory
入口固定 cell 的 load 为 Vint w
             ⇒ 出口同 cell 的 load 仍为 Vint w
```

执行 theorem 消费实际 `exec_stmt`，从 typed lvalue、constant 求值、cast 和
`assign_loc` 推出实际 `Mem.store` chain；没有要求使用者额外断言模型中“所有
writes 都是常量”。Temp set 不改内存，但可以改 bindings，因此此库只保证
**固定 block／offset** 上的 memory observation。Bound pointer／controls 的 frame、
source progress、guard 读许可及 source/model 对应仍分别由既有 site／语言／domain
证明承担。该保证不是整个 loop 的正确性证书。

## 下一项真实使用者

对现有 `nested_write` 的两层 loaded headers 与 BODY `a[index]=1`，考虑两
headers 初始都为 1、并与 A 数据重叠的输入：这项语言性质可以保持 header values，
提供不同于 non-alias 的充分条件。计划从已许可 capture 的两个缓存比较生产
该入口条件，并复用既有 protected-temp frame 与候选／host 证明。

实际 guard producer 仍须完成：有序读许可、cached values 与原 observations 的
对应、loop-prefix induction、model anchor 和实际 checked-entry 运输。全部接通
后才能启用新的 constant-time shortcut；不把本库的语义引理说成已安装优化。
其他 BODY 保留原扫描或保守拒绝，不要求该条件最弱或接受集合相同。

## 验证

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_word_observation.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_word_observation.py --validate
```

7 个查询端点通过，static checker soundness 闭合；其他端点只使用查询到的
CompCert memory／Clight fragment 基线，基线并集为 6 项既有 assumptions，零新增
global axiom。不能将这些 language theorems 全部称为“无公理”，也不能将其与
完整 compiler 的 42-global 基线混为一项。

`build/word-observation/report.json` SHA-256：
`c41d8275f74d0a74673d31eab25628a4d0a480ee5c114f65d9d5206e2d99139b`。
报告绑定 sources、objects、helpers、实际查询和编译 logs。没有新 runtime shortcut、
native acceptance／cost 或 guard work 测量；kernel 不变。
