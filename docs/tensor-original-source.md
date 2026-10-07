# 原 tensor 源：Horner 地址、读取许可和公开出口

日期：2026-10-07。[动态 candidate backend](dynamic-tensor-backend.md)的后继。
本轮把真实原 Clight 执行连接到候选执行，并证明一份 source-derived readonly
layout guard；完整坐标条件的机器编码和新整程序安装仍待完成。

## 处理的源与条件

当前源是正矩形、temp bound 的 counted-loop nest，leaf 是一条 int32 数组
赋值，可有多次读取及旧 value-expression grammar 的 RHS。示例对应：

```c
for (; i < n; ++i)
  for (j = 0; j < columns; ++j)
    for (k = 0; k < components; ++k)
      a[((i * ld) + j) * 5 + k] = a[((i * ld) + j) * 5 + k] + alpha;
```

布局是 `[temp(n);temp(ld);constant(5)]`，循环计数是 `[n;columns;components]`，
另有 scalar 参数 `[ld;alpha]`。地址乘数 5 已在实际 AST 中；循环条件里的
literal `<5` 尚须连接既有 constant-bound transport adapter，不能把它算成本轮
已识别的完整 C 输入。当前只连接一个 tensor、一条 leaf operation；没有通用
多 statement body recognizer。

源地址保持 Horner AST，候选 encoder 使用 suffix-volume sum。新证明在实际
Clight int32 modular 求值及 pointer semantics 下连接二者，不假设每个 Horner
中间结果没有 wrap。逻辑坐标合法性和布局 span 界保证最终地址对应；成功源
load/store 提供实际内存权限。Volume/nonalias 事实本身不授予权限。

两个前提必须分开：`n*ld*5` 满足布局检查，并不保证 `columns<=ld` 或
`components<=5`。`tensor_source_operation_box` 对全部 writes/reads 的仿射坐标
做数学整数区间检查，覆盖所有活动点。例如 `[3;2;5]`／布局 `[3;31;5]` 接受，
`[3;32;5]` 拒绝，尽管布局乘积仍安全。负系数也按实际区间 extrema 处理。
**这个 box checker 目前是 Rocq/提取 OCaml 的数学计算，尚未生成 Clight guard。**

## 使用者给什么，库交付什么

| 输入／义务 | 库交付的证据 | 当前接入状态 |
| --- | --- | --- |
| 维度来源、坐标 affine descriptors、原 Sassign AST、RHS metadata | `describe_tensor_source_access` 与 `check_tensor_source_operation` 检查编码、实际 AST 相等和所有声明 reads 都被 RHS 使用 | 可执行数据 checker；不接受 source/model 语义 callback |
| 原 nest 的实际 AST、shape/freshness、参数名称和使用位置 | 从第一次实际执行到的 leaf 反推出 pointer、tail dimensions 和已用 scalar 的 Vint 定义性，并运输回入口 | 通用 producer 已证明；region/site 的数据 factory 还未生产全部结构证书 |
| 原 silent normal execution、正 signed 计数、实际 bindings、数学坐标 box、布局接受 | `tensor_source_region_decode` 生产真实 Loop 模型执行和精确源退出状态 | 消费原 `exec_stmt`，不再消费假设的 Loop SOURCE 执行 |
| 不受信任的 candidate／schedule witness 或正 tile sizes、参数 profile、scratch pool、public live set | 原 verified checker + lowering 生产候选实际执行；完整 memory 等于原 execution 的结果 | affine／tiling 执行连接已证明 |
| 与原计数对应的实际 bound temps、candidate frame | `memory_recursive_restore` 恢复公开 iterators；restored candidate 与原 exit 在 public live set 上一致 | source/candidate 出口证明已连接；程序中的私有名字分配还需 host/site 安装 |

检查器拒绝未知 coordinate temp、rank 不符、改变 RHS 的原 AST，以及声明但
实际未使用的 read。最后一种限制服务于从成功源 RHS 反推各读取许可的证明。
选片段、提出优化和参数范围仍由实例负责。当前 candidate 定理显式保留源结构、
入口 bindings、profile 和 BOX 义务，尚不是一个交给 C frontend 的完整 factory。

## 源定义性怎样支持 guard

`tensor_source_layout_condition` 是现有 `readonly_condition` 的实例，其 D 为
**原片段存在 silent normal completion**，不是要求调用者预先提交全部维度 Vint。
实际 decision tree 按顺序运行：

```text
original root iterator == 0
  -> each source bound is positive and <= count cap
  -> actual readonly tensor volume guard
```

每一层后续读取由前一层接受和真实源执行许可。若外层为空，guard 在外层
计数处返回 false，不读取 `ld`、`alpha` 或后续 bounds。示例实际 Clight
`decision_run` 证明在这些 temps 没有 bindings 时仍能安全拒绝。

若所有 bound checks 接受，源确实执行到 first leaf；真实 Horner lvalue 的
求值反推 stride 被读取为 Vint，真实 RHS 则反推使用的 scalar 为 Vint。第一维
若未出现在 Horner 地址里，静态 metadata 要求它来自原 bound；其他维度必须
由实际地址读取许可。接受交付 positive bound ranges、相同 observed dimensions
和 layout flag。它**还没有交付数学 BOX**，所以不是完整优化 guard。

D 的有限正常完成限制仍需语言 host 的 progress/divergence 处理。不能凭本轮
guard totality 定理声称任意 reachable program state 的整程序 preservation。

## Narrative 的三方责任与四条链

Framework 的最小 kernel 保持：这里只复用 readonly condition 和已有组合定律。
Clight 库提供真实求值反推、地址/load/store 对应、短路安全和 temp restoration。
Domain/site 提供坐标描述、布局、nest 结构及使用关系，消费区间和原 checker。

`C_opt` 的 source 端现在从实际原 execution 生产模型，候选执行包含公开出口
恢复；`C_derive` 已有覆盖全部活动点的数学 box 充分条件；`C_guard` 已有
source-derived layout condition，但 box 的机器编码未交付；新 `C_host` 的实际
factory／placement／资源／progress 安装未发生。四条链不是四份用户手填 record。

## 验收

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_source.mk proof
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_source.mk prototype
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_source.mk validate
```

证明与提取报告分别位于 `build/tensor-original-source/proof/report.json` 和
`build/tensor-original-source/extracted/report.json`。详细 hash／端点／运行记录见
[checkpoint](research-checkpoint-2026-10-07-tensor-source.md)。提取运行只执行源
descriptor、数学 box checker、原候选 checker 和 lowerer；不执行生成的 Clight，
没有新增 Csem→Asm entry、完整 C/native calls、machine probes 或性能结论。

下一项是在这份已接源/候选的接口上生成并证明安全的机器坐标条件，随后连接
literal-bound transport、原 AST factory、语言 host 与完整程序。该约定子集闭合后，
继续同例比较 guard work、接受域、code size、完整运行及三方作者负担。完整目标 active。
