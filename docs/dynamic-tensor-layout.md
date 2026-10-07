# 动态多维布局：条件编码、真实访问与依赖服务

日期：2026-10-07。此阶段交付局部库，不新增完整 C 编译入口。

后继 [动态 tensor backend](dynamic-tensor-backend.md)已连接 vector 指令／真实
RMW、原 affine／tiling checker 和实际 candidate lowering，另有七项提取运行。
本文保留原 33 端点服务阶段的证据范围；真实原源接入及新完整 compiler 仍待完成。

## 要覆盖的源问题

考虑有 padding 的布局，`ld` 为运行时行宽：

```c
for (i = 0; i < n; ++i)
  for (j = 0; j < columns; ++j)
    for (k = 0; k < 5; ++k)
      a[(i * ld + j) * 5 + k] += alpha;
```

候选可以改变循环顺序，但首先要证明真实地址与逻辑 cell 对应、相关读写的依赖
得到保持。将地址直接表示成一条静态仿射式，无法保留 `i*ld` 的参数乘法；把
`ld` 枚举成少量常数则限制布局规模。新服务保留逻辑坐标 `[i;j;k]`，在语言视图
中使用入口维度 `[n;ld;5]` 映射到实际地址。`columns<=ld` 和各坐标的范围仍需
由实例证明，不能从布局检查自动得到。

已有 [runtime-stride compiler](clight-runtime-stride-case.md) 已经在二维固定数组
纯写模板上保留变量 stride，并证明完整 Csem→Asm。另
[loaded-stride compiler](clight-loaded-stride-case.md) 在小 extent 上枚举布局。
本阶段补的是通用坐标向量到 CompCert buffer 的连接；上述 C 代码是后继接入
目标，不是本轮已安装的优化，也不代表完整 BT 已经支持。

## 提供的接口与证明

| 服务 | 使用者提交 | 库实际证明 |
| --- | --- | --- |
| `tensor_index` | 入口维度与逻辑坐标向量 | 成功则所有维度正、flat offset 在 volume 内；同布局相同 offset 的坐标向量相同；维数不匹配或越界返回 None |
| `tensor_pointer_locations` | 一个逻辑 array、实际 block/base 与入口维度 | volume 的 byte span 不超过 `Ptrofs.modulus` 时，不同逻辑 cell 的 Mint32 byte 区间分离；包括非零和 modular base |
| `tensor_index_expression` | typed pure 维度／坐标表达式及其实际 word 求值 | 生成 row-major 地址的 int32 modular 求值等于数学 flat offset 的 `Int.repr`；布局接受后最终下标在 signed 范围内 |
| `tensor_pointer_lvalue_evaluation`／`inverse` | 上述值对应、布局接受及实际 pointer 绑定或 lvalue 执行 | 真实 Clight 地址恰为 `Ptrofs.add base (repr (4*offset))`；inverse 从实际执行取得 pointer/base 和 Full field |
| load／store 服务 | 原 memory 上的真实 `Mem.load/store` receipt、实际 RHS 求值 | 真实 Clight load 或 Sassign 执行；完整 memory 对应，store 保持 temps。访问末端界来自成功的 Mem operation |
| `tensor_instruction_reorder` | 两次真实指令执行与原依赖接口中的 WW／WR／RW 独立性 | 交换后有真实执行并得到相同完整 memory；复用 `GuardMemoryInstr`，支持其已有读写及 modular computation 语义 |
| `tensor_volume_guard_condition` | 每个维度表达式为 pure signed32，且在当前入口有实际求值 | 标准 `readonly_condition`：检查可用、每个到达测试安全、全部接受执行蕴含布局性质，检查状态等于原入口 |

这里的 registry 是证明中的语言视图，不是生成的 block-ID 查询。单个 tensor 内
的 nonalias 不证明不同 array/base 之间分离，也不证明 loaded header 不被 body
改写。布局尺寸和 pointer 绑定本身不授予 load/store 权限。

## 检查如何安全编码前提

语义性质为各维度严格正且

```text
volume = d0 * ... * dr-1
volume <= min(Int.max_signed, Ptrofs.modulus / 4).
```

数学 `tensor_layout_flag` 直接使用 Z 乘积；实际 guard 使用不同的编码。
从 accumulator=1 开始，每一维先检查 `d>0`，再检查
`accumulator <= cap/d`。只有通过后，后续表达式才计算该乘积。
`tensor_volume_check_spec` 证明正 accumulator 下的完整数学等价；实际 Clight
求值证明另外排除除零、signed division trap 和检查中的回绕。并非假设检查
接受后再证明检查安全。

当前 lowering 为 readonly decision tree。每维两个短路测试，检查数只随 rank
增长；累计表达式在后续节点重新求值，表达式文本／算术工作最坏为 rank 的平方。
没有 private accumulator、缓存去重或计时证据；“没有域遍历”不等于常数机器成本。

公共 condition 的 D 要求全部维度都有 typed pure word 求值。这仍是使用者要
从原源生产的入口证据。本库另证明首维非正时直接安全拒绝，后续维度无需有值；
fixture 的首维为零，后两维确实未初始化。这个独立定理没有自动放宽上述 condition
record 的 D，也没有生产一般多层条件读取的 source certificate。

## 三方责任与四条逻辑链

最小 kernel 没有修改。`readonly_condition` 和 guarded composition 直接复用。

语言库负责实际 int32 算术／比较／除法、pointer lvalue、load/store 和 readonly
tree 安全；domain 部分负责 mixed-radix 单射、坐标／布局性质及与既有依赖契约
的连接。优化／site 作者继续负责原 AST、维度读取许可与稳定性、坐标覆盖、
source/model 对应、具体候选、公开出口及合法 placement。相同服务以后能供多条
规则调用，但本轮没有量化作者负担收益。

四条逻辑链的当前状态是：`C_guard` 已在明确的 D 上完整交付；`C_derive` 已提供
volume 到 span、signed index 和物理 nonalias 的局部部分；`C_opt` 已复用独立
指令交换定律，但未生产新 source/candidate 的完整证书；`C_host` 未新增调用。
不能把这些分项称为新完整 optimizer。

## 验收与下一步

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/dynamic_tensor.mk proof
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/dynamic_tensor.mk validate
```

独立报告为 `build/dynamic-tensor/proof/report.json`。五模块、160 个本地依赖与
CompCert 源／对象摘要绑定；33 个端点中 13 个闭合，其余最多六项原 CompCert
假设，零新增 global axiom，kernel 闭合。真实 guard 定理覆盖 stride=17／31、
signed 最大 volume、46341² 和 signed 最大值乘二的拒绝、未初始化后续维度；
另检查越界、缺失坐标和零维度拒绝。

没有新 extraction／native／whole-program entry、运行性能、完整 BT 或任意 rank
frontend 的成果。下一步先使 vector affine accesses 和真实 reads/RHS 消费这些
服务，再从原源生成运行时维度的 receipt、稳定性和范围；随后接候选 lowering、
公开出口、selector 和语言 host，以完整 C 接受／回退作验收。
