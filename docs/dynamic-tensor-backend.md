# 动态 tensor 候选：verified checker 到实际 Clight lowering

日期：2026-10-07。本文面向需要接入一种带运行时条件的循环变换的实现者。
这是 [动态布局服务](dynamic-tensor-layout.md) 的后继：现在已有实际 candidate
backend 和 affine／tiling checker 的连接，尚未安装新的完整 C 编译入口。

## 现在能做什么

继续使用三维 RMW 目标：

```c
for (i = 0; i < n; ++i)
  for (j = 0; j < columns; ++j)
    for (k = 0; k < 5; ++k)
      a[(i * ld + j) * 5 + k] += alpha;
```

逻辑指令保存坐标 `[i;j;k]`，布局描述器保存 `[temp(n);temp(ld);constant(5)]`。
循环计数参数是 `[n;columns;5]`，另有 scalar 参数 `[ld;alpha]`；两者没有混同。
新的 backend 保留运行时 `ld`，把向量访问、真实内存读取、modular RHS 和实际
Mint32 写入一起降为 Clight。源／候选的数学 Loop IR 沿用原指令及 dependence
接口。这里展示的 C 地址仍是后续 source adapter 要识别的源问题；它不是
提取实验的输入。

候选可以由不受信任的搜索产生。`check_tensor_mapped` 调用既有 affine candidate
checker；`check_tensor_tiled` 调用既有 quotient-witness tiling checker，返回
`Some statement` 或 `None`。只有成功的代码生成与候选验证共同产生接受。
编译期拒绝不等于运行时 fallback，后者还需 selector／语言 host 安装。

## 调用者提交什么

| 输入 | 作用 | 本库提供的证明 |
| --- | --- | --- |
| `tensor_dimension_source` 列表 | 维度来自 int32 常数或入口 temp | 常数按实际 `Int.signed (Int.repr z)` 解码；temp 需要实际 Vint。成功 observation 导出 signed 范围、typed pure 求值；保护这些 temps 后布局不变 |
| logical array、实际 pointer temp | 指令的逻辑身份及目标 pointer 表达式 | 成功 registry lookup 与实际 pointer 绑定产生同一个 modular 地址；未知 array／坐标 rank 不符拒绝 |
| instruction 列表 | affine 坐标向量、reads、RHS、write | 真实 `Mem.load/store` 与旧 instruction semantics 对应，支持已有 Add/Sub/Mul/Param/Constant 的 int32 RHS。裸 LoadedValue 仍受旧 integer-result gate 限制 |
| 参数 layout、范围、private counter pool、live temps | 候选循环编码和公开 temp frame | scratch 不能覆盖 layout、pointer、维度或声明的 live temps；完整生成循环保留这些 bindings |
| candidate／reindex witness 或正 tile sizes | 优化提案 | 成功的既有 verified checker 产生条件候选证书，无 source/candidate 正确性 callback |
| 实际源模型执行与范围事实 | 将当前原源执行接到 Loop IR | 接受后候选具有实际 silent normal Clight 执行，结果为相同完整 memory；源代码到该模型的 producer 尚未提供 |

`tensor_observe_dimensions` 是证明中的 partial lookup，不是生成到程序里的
运行时查询。真实 guard 使用维度的 Clight 表达式。它的标准 D 目前要求这些
维度已经有 Vint bindings；本次没有证明原源能安全地提前读取全部维度。

## 一条成功证明怎样连接

`tensor_checked_candidate_execution` 将以下实际输入组合：

```text
原 Loop 模型执行、参数范围、实际 memory registry 与 pointer 绑定
       + 成功维度 observation
       + 实际 volume guard 接受
       + verified candidate certificate
       + 成功 Clight lowering
       => 候选实际执行、同一完整 memory、受保护 temp frame
```

`check_tensor_mapped_execution` 和 `check_tensor_tiled_execution` 从对应 checker
的成功返回直接取得 candidate certificate。Volume 接受生产 signed 下标范围和
本 tensor 内的物理 nonalias，供原依赖验证使用。它不授予内存权限，不生产跨
array 分离，也不生产 `columns<=ld` 或所有活动坐标的合法性。

这个区别影响正确性：即使 `columns>ld`，原 C 的多个坐标也可能落在同一合法
物理地址上；当前 tensor registry 会拒绝那些越出逻辑维度的坐标。后续必须
证明运行时入口条件覆盖实际源的全部活动坐标，不能把模型无法执行当作原 C
不需处理。原源 Horner 地址 `((i*ld)+j)*5+k` 与生成的 suffix-volume 地址也有
不同 AST，需要实际 word／地址对应证明。

## 三方责任与四条证书链

[Narrative](topdown/paper-narrative.md) 的最小 kernel 保持不变。

| 责任归属 | 本次已经交付 | 仍需交付 |
| --- | --- | --- |
| framework／可复用库 | 复用 readonly condition、现有 guarded composition；无新 kernel 能力 | 本次还没有新的 local rule 交给安装 host |
| Clight 语言库 | dimension expression 求值、实际指令／循环执行、protected temp frame、readonly guard；复用原语言 host | 实际源地址规范化、source-derived 读取许可和公开出口的 producer 连接 |
| domain／优化／site | vector 指令 lowering；原 affine／tiling checker 与物理布局连接；成功候选的实际执行定理 | 原源到模型、完整坐标覆盖、loaded header 稳定性；actual source key、progress、freshness、合法 placement |

`C_guard` 已在明确的 D 上交付；`C_derive` 提供 volume 到 span／nonalias 的部分，
尚缺实际源义务的完整入口推导；`C_opt` 现在连接经验证候选和实际生成执行，
但 source 端仍为 Loop 模型；`C_host` 复用接口，本次尚未实例化新安装。这四项
是逻辑环节，不是要求每个使用者另填四份证明 record。

## 验收与证据边界

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_backend.mk proof
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_backend.mk prototype
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_backend.mk validate
```

Proof report `build/dynamic-tensor-backend/proof/report.json`：
`2b0fe57f9a8e31a21845acbac3c82a10251c7a651819d52d4c3da472a3098d1f`。
九模块、238 个本地依赖；66 端点包含旧 33 项和新 33 项，30 项闭合。
语言端点只使用既有 CompCert 基线；两个 candidate 执行端点继承原
VPL／PolCert checker 基线，最多 14 个 globals。无新增 global axiom，kernel 闭合。
不能将这份基线描述成全体端点只依赖六个 CompCert globals。

独立 extraction report `build/dynamic-tensor-backend/extracted/report.json`：
`50f6f7994dfcca6af19ffbb9e3892ff43e13bcc3b9ec96467e22b41a661503c5`。
原 checker 和新 lowerer 实际提取执行，七个 cases 通过：三维 vector RMW 的
identity 与 2×3 tiling 分别产生 27／51 个 statement nodes；零 tile、layout
scratch 冲突、错误 scalar arity 拒绝；运行时布局 observation 的数学 volume
check 接受，46341² 拒绝。Nodes 是 AST 节点数，不是汇编 bytes 或运行成本。

Harness 没有执行生成的 Clight statements，没有读取上述 C 输入，也没有新
C→assembly compiler、native program calls、machine branch probes 或收益测量。
实际执行对应来自上述 Rocq 定理，提取实验只确认 checker／lowerer 可运行。
旧完整 compiler 和成本报告保持各自配置范围。

## 下一项验收

沿 [本轮 checkpoint](research-checkpoint-2026-10-07-tensor-backend.md) 接实际源。
先对约定三层源子集闭合 source／condition／candidate／host 证明，再在同例
评估 compact conditions、接受域、guard work、code growth、完整运行和作者负担。
其中 volume check 已是按 rank 检查；这不表示整份条件合成或成本验收已经完成。
完整 BT 和更广 source classes 仍有各自待办。
