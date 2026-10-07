# Tensor 坐标条件：从 affine box 到真实只读 guard

日期：2026-10-07。[原 Horner tensor 源](tensor-original-source.md)的后继。
完整目标 active。这一步生成安全的 Clight 坐标检查，并把其接受事实接到原源／
候选执行证明；新完整程序安装尚未完成。

## 使用过程与支持的条件

沿用同一真实原 AST：

```c
for (; i < n; ++i)
  for (j = 0; j < columns; ++j)
    for (k = 0; k < components; ++k)
      a[((i * ld) + j) * 5 + k] = a[((i * ld) + j) * 5 + k] + alpha;
```

用户提出源坐标、读写描述、布局 `[n;ld;5]`、候选 schedule 或 tile sizes，
以及用于安全生成条件的参数 profile。当前源是正矩形、temp-bound nest、一个
tensor 和一条 leaf operation；此处的 `<components` 已连接，literal `<5` 的
frontend transport 仍待连接。RHS 沿用已有 int32 value grammar，word wrap 是
实际语义的一部分；并非要求所有程序算术均不 overflow。

条件库支持每个 read/write 的多维 affine 坐标：常数整数系数、常数偏移、循环
axes 和 loop-invariant scalar。Axis 取 `[0,count)`，scalar 是单点。维度来自
常量或有名 temp。它为每项生成区间最小／最大值，再检查
`0 <= minimum && maximum < dimension`。负系数选择相反端点；零系数不生成
无用运算。所有 accesses 的条件合取。因此它覆盖整个活动矩形，无逐点 scan。
这是 box 充分条件，不是一般 Presburger projection 或 weakest precondition。

本例的坐标条件等价于相应正域上的 `columns<=ld && components<=5`；布局
volume 条件还检查正维度与 pointer span。`n=3, columns=2, components=5, ld=31`
通过坐标检查；`columns=32` 或 `components=6` 被拒绝，即使 volume 本身合法。

`compile_tensor_box_guard` 把生成的数学条件交给既有 signed32 affine expression
lowerer。用户 profile 是 **runtime 要检查的范围**，不是 caller 保证。
只有所有实际参数通过 profile gate，才执行 extrema 算术。Lowerer 静态证明
每个生成运算的 signed32 范围；未知 temp、错误 arity、无效 profile 或可能溢出的
中间式返回 `None`。Factory 后续应在 `None` 时保持原程序；当前实例仍需接该 factory。
Runtime 超出 profile 则返回 false，保留原源路径的语义安装由后续 host 完成。

例子的 context 为 `[n;columns;components;ld;alpha;n;ld]`；重复参数当前会重复
检查，尚未消除。Count profile 分别是 `[1,33)`、`[1,33)`、`[1,6)`，stride
是 `[1,1000)`，alpha 覆盖整个 signed32 域。数学 singleton 的上界可能是
`MAX_SIGNED+1`，但生成器直接取 singleton 的值，不把这个上界编码成机器加法。
Profile 编码使用 `upper-1`，支持 full-signed alpha；提取 fixture 验证两个极值。
`ld=1001` 是合法坐标却超出本例 profile 的保守拒绝，不能算算法不支持该布局。

## 从实际 guard 接受到候选执行

组合的真实 decision tree 按顺序运行：

```text
root iterator == 0
  -> positive source bounds <= count cap
  -> readonly tensor volume check
  -> actual parameter profile checks
  -> safely lowered affine coordinate comparisons
```

前缀使用原源 silent normal completion 许可后续读取。所有 bounds 接受时，
原源执行到 first leaf；实际 Horner 地址和 RHS 反推出 pointer、stride 和已用
scalars 的类型／定义性，并运输回入口。若 outer 为空，前缀在缺 stride、alpha
的入口安全拒绝，不提前运行 profile 或坐标式。新 proof 复用该许可，不给 D
偷偷添加“所有 temps 先已定义”的条件。

| 使用者输入／库前提 | 库生产什么 | 责任归属 |
| --- | --- | --- |
| Affine 坐标与 layout descriptors | 全活动矩形的 extrema 条件及数学 box 对应 | Domain 条件库：`tensor_box_entry_value` |
| Temp 名称、静态 profile | 安全 signed32 condition 编译、profile 短路、readonly certificate | Clight 库：`tensor_box_checked_exact/condition` |
| 原 nest／operation，shape、freshness、参数使用与保护的静态证据 | 原源许可的完整 condition；接受推出 INITIAL、正 bound ranges、维度观察、layout 和 BOX | Language/domain 组合：`tensor_complete_guard_sound` |
| 真实原执行、完整 guard 接受、原 candidate checker 成功与 frame 名称配置 | 实际 mapped／tiled candidate 加 iterator restoration；完整 final memory 相同、live temps 与原出口一致 | Domain 使用原 checker；Clight 库实现实际执行／frame |

新的 `tensor_complete_tiled_execution` 和 `tensor_complete_mapped_execution` 内部
生产 count/scalar bindings、pointer view、profile、BOX 和 Loop SOURCE；调用者
不再另外提交这些语义证明。仍需提供源结构和 temp 保护等静态证明，实际源
execution 和实际 guard acceptance 是执行正确性定理的前提。它们尚未被一个
data-only region factory 包装为 kernel 的 preservation certificate。

Framework 最小 kernel 未改变。四条逻辑链的位置是：`C_derive` 由 affine extrema
和 layout 服务生产入口充分条件；`C_guard` 编码该条件并证明实际短路安全；
`C_opt` 连接真实原源、旧 verified candidate checker、实际候选和公开退出；
新 `C_host` 仍需 region factory、progress、private resources 与安装。
三方责任不能误读成四份使用者手填 record。

## 验证边界与下一项

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_box.mk proof
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_box.mk prototype
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_box.mk validate
```

142 端点包含此前 111 与新 31；实际 coordinate guard 的接受／拒绝和 empty
full-guard refusal 以 Clight `decision_run` 证明，不是以数学 bool 代替执行。
提取程序实际运行条件合成、Clight expression lowering 和数学条件 flag；它
**不执行生成的 Clight 或完整 C/assembly**。完整报告见
[checkpoint](research-checkpoint-2026-10-07-tensor-box.md)。

后续先让 region data checker/factory 从实际输入 AST 生产结构证书，再连接
literal-bound transport、kernel 的 local certificate、source progress、私有声明
和语言 host／Csem→Asm。D 当前是存在 finite silent normal completion；本轮
totality 不能替代全 reachable states 的 progress/divergence 证明。单 tensor
layout 非别名也不代替 header stability、跨 tensor 分离或实际内存权限。

按 narrative，约定子集闭合后在同例验收接受域、guard 工作、code bytes、完整
运行和三方作者负担；保留 scan／refusal 的情况单列。Profile 范围可改进，重复
probes 可用既有简化服务消除；这两项不要求改 candidate 正确性或最小 kernel。
