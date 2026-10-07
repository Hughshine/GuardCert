# Tensor 实例：使用者的数据与各层证明工作

本文面向想接入一条 guarded loop rewrite 的实现者。依据当前
[tensor compiler](tensor-region-compiler.md)，区分已有领域内的一次使用、扩展
source grammar／优化领域，以及首次实现语言 host。没有记录作者工时，也没有
把源码行数或 endpoint 数当作证明负担减少的测量。

## 已支持 source family 的一次使用

用户选择真实片段，提出一个数据描述器和候选。描述器有九个字段：dimensions、
scalars、pointer、logical array、write coordinates、read coordinates、value、
cap 和 profile。Candidate 是 Loop AST／reindex witness 或两整数 tile sizes。
当前 OCaml 例子有75行，包含 source pattern、profile 和若干候选模式；这是
一个不受信任策略示例的物理行数，不是一般优化策略的最少工作量。

对这个已支持 family，不要求每个候选／位置手写 SOURCE、BOX、bindings、
candidate-exit 或上下文 simulation 证明。数据 checker 核对实际 AST 和 metadata，
full guard producer 取得源路径许可及模型输入，候选 checker 核对域／依赖，
语言 host 核对位置、private pool 和 progress。任何环节失败都保持原源。
搜索如何找到有价值的候选和 profile 仍由优化策略决定；正确性 checker 不证明
候选有收益。

一个使用过程是：提出 dimensions `[n,ld,5]` 和坐标 `[i,j,k]`，提出 `[ld,alpha]`
及其 profile，再提出交换前两条 loop 的 AST 和 swap witness。Factory 绑定
Horner 地址／真实 RMW RHS，guard 从当前入口检查所需充分事实，checker 生产
候选执行证据，kernel 给出 guarded preservation，host 安装并继续编译。
错 witness 无须用户补一个“条件下也许正确”的证明来强行通过；本 checker
会静态拒绝它。更一般的条件正确性接口仍允许其他 domain 提供自己的证明。

## 增加一个 source family 的工作

新 source grammar／内存效果不能只给描述器添字段。领域实现需要证明实际源
和模型的对应、入口条件对模型义务的覆盖、真实候选及 public exit 的对应。
新的前提表达式还需要已有 safe condition compiler 支持，或交付新的有证书
原语／编码算法。Loaded bounds、多个 tensors、nonrectangular domains 和 literal
loop bounds 的对应是具体工作，不能从当前九个数据字段自动获得。

本轮新增模块按责任归属列在下面。共享于该 family 的 factory／compiler 是
一次开发成本；现有 native matrices 中换 schedule 或 source site 没有再增加
对应的语义 callback。

| 工作 | 新模块 | 查询端点 | 物理源码行数 |
| --- | --- | ---: | ---: |
| 可复用 Clight 服务 | `ClightLoopAdministrative`、`ClightReadonlyPreservationKernel` | 10 | 197 |
| Tensor 数据 factory／局部规则 | `ClightTensorRegionPackage`、`ClightTensorRegionPreservation` | 14 | 319 |
| Compiler 组合接线 | `ClightTensorRegionCompiler` | 5 | 151 |
| 接受／拒绝 fixtures | `ClightTensorRegionExample` | 10 | 78 |

审计保留此前142个 tensor queries，再加入这39个端点。实际证明消费既有的
source／guard／candidate对应、语言guard／region host、CompCert pipeline 和
PolCert candidate checker。142包含fixtures，不表示新compiler直接调用了
142个定理；这两个数也不是全部库大小、同等独立定理或作者工时。

`ClightLoopAdministrative` 承担前端 skip 包装到模型 AST 的执行运输。
Readonly adapter 实际消费 kernel certificate 并解释 guarded choice。
Tensor factory 的静态证书和 domain producer 的实际执行覆盖共同关闭本实例的
`C_derive / C_guard / C_opt`；compiler glue 再消费既有安装定理。
Kernel 定义保持。完整程序连接仍以 source scope／progress／freshness 为前提，
并由程序安装 checker 和语言定理生产／消费相应证据。

## 首次实现语言 host 的工作

语言实现者须解释 check、执行、观察和 choice，证明机器原语安全、实际状态
运输、private resources、effects、控制出口和进展协议，再证明该 host 的程序
安装定理。原表达式／logical condition 是只读，不意味着机器 scratch、flags
或私有临时状态可以忽略；它们必须处于有证书的状态关系内。

本轮没有重新实现这些 Clight 安装定理，也没有引入任意语言都能自动安装的
contract algebra。若一个新优化被已有 host 拒绝，应先确认缺少的 guarantee／
context requirement，再增加有具体使用者的语言服务。

## 可复核与比较边界

`scripts/audit_tensor_proof_ownership.py` 绑定完整 proof report，记录各模块实际
queries／源码摘要、数据字段和 native policy，并检查本轮使用的关键 producer
与 kernel／host 接线。它是责任和复用清单，语义正确性由独立 Rocq 审计提供。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_tensor_proof_ownership.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_tensor_proof_ownership.py --validate
```

尚未进行其他 verified framework 的同例作者工时实验。因此当前可证明的结论
是哪些证据已由库／checker 自动生产，哪些扩展还需要新证明；不能声称已测得
相对其他框架的作者负担优势。OLO 的功能／算法比较和本实例成本另列。

后继的[坐标次序实例](tensor-coordinate-order.md)已经换用 `[j,i,k]` 数据提案，
并在实际两种源／单次／连续／goto上下文中复用本 proof report。它没有新增
Rocq definition 或 semantic callback；这是一项可核对的接口使用结果，仍不是
其他框架同例作者工时的比较。

报告 `build/tensor-region-factory/ownership/report.json` 的 SHA256 为
`18d37a4d81d17f4ef46569baddd66401d1e937a50cb3d50aca3f5509c103fe2a`。
