# 阶段记录：公共 private-scan pointer compiler

2026-10-06。实现基于 main `26e38f18ee1b09c5fd428276945dfd5f6fb052dd`。活动完整目标继续，研究定位遵循 `topdown/research-positioning` 的 `f7936299fa6272fbf50db6b94a1bd0333808ea09`；本阶段结束前重新 fetch，三个评审 refs 与上一读取相同，没有新增评审内容。
## 结果和原缺口

前一阶段只完成实际 scan 的完成执行 facts、原入口前提稳定和 exact wrapper；本阶段完成公开 host、真正的检查安全解释、guard certificate、分支状态运输、kernel 保持的消费与真实 compiler 安装。没有修改语言无关 kernel，也没有调用旧统一 compiler 入口。

实际入口是 [compile_preserving_pointer_scan](../prototype/interface/ClightParamPointerCompiler.v)，最终定理 `compile_preserving_pointer_scan_correct` 给出 Csem→Asm backward simulation。C frontend、私有名字／scope、独立 source progress、region traversal 和 CompCert 后端继续复用；实际 guard 和候选数据分别由新 pass 构造及既有 domain checker 核对。

## 三方责任与源码

| 责任 | 新实现／复用 |
| --- | --- |
| 框架 | 既有 `guard_certificate`、`preservation_certificate` 和 `guardify_preservation`。本阶段新增实例，不以新增接口字段代替优化正确性 |
| 语言实例 | [Safety](../prototype/interface/ClightPrivateScanSafety.v)：到达表达式／测试、实际子执行后状态与有限 loop 续行；[Host](../prototype/interface/ClightPrivateScanHost.v)：实际初始化／checked state、双向 dispatch、安全到可用；[Preservation](../prototype/interface/ClightPrivateScanPreservation.v)：normal public observation、source/candidate transport、kernel 与小步 contract |
| 优化／domain library | [Certificate](../prototype/interface/ClightParamPointerCertificate.v)：原入口 D/P、所有完成检查 frame／sound；[Preservation](../prototype/interface/ClightParamPointerPreservation.v)：旧真实 candidate 证书的接入和名字核对；[Candidates](../prototype/interface/ClightParamPointerCandidates.v)：mapped、tiling、schedule generation 后重新核对；[Compiler](../prototype/interface/ClightParamPointerCompiler.v)：真实 source/target 表、完整程序端点 |

优化方提供实际 source package、候选与条件性 source→candidate 保持；P 的依赖和 protected-frame 稳定属于 domain。语言 adapter 处理私有检查写入、分派／fallback 和公开观察。kernel 不读取指针、bounds 或 overflow 语义。

`check_safe` 是归纳操作判断，要求实际 `eval_expr` 和 Boolean 测试可定义，并覆盖每个实际子执行后的安全续行。已有 bounded scan 的执行见证和确定性可构造这个判断；由独立语言定理推出检查可用。没有把 `check_safe` 定义成存在一个完成路径。局部 exact 定律覆盖任意完成 branch trace/outcome；正常 region 安装实例的观察范围另外限定为 E0/Out_normal，最终 compiler 定理方向仍是 backward simulation。

D 不预含 nonalias 或 header 接受。source 的正常执行提供 runtime domain，接受建立 P(original)；header／参数／pointer binding 的依赖由 protected ports 覆盖。检查只写声明的私有 temps，保持 memory；其结果和实际 cursor 被保留到 checked state。

## 实际能力与拒绝

source 使用稳定寄存器 bounds 的矩形嵌套循环，多个真实 pointer、参数化仿射地址、独立 RHS scalar、多读取和多语句。提案包含 mapped Loop/index-map、tiling 或 affine schedule；生成的真实 Loop 必须重新核对。selector 从已有 axis/parameter cap profiles 搜索；参数非负和有限访问窗口等实际检查仍保守限制接受域，超出时回退。

原有独立模型中的 `param_copy2` 在本机选出 `[58,16]` 的 count caps；当前 fixture 的 disjoint 输入可接受 interchange。链式依赖的 `param_chain2` 对 interchange／tiling 缩小到 `[1,16]`，fission 缩小到 `[58,1]`，而不是因运行时不别名就接受任意重排。维度不足时可选择实际内层 region，报告区分 whole source 与 inner region。

这一 package 不是 readonly 的 `j<U(i,parameters)` source；没有把两种实现组合宣称成一般 affine pointer polyhedron。本阶段复用既有 B⇒A footprint／机器域对应，未新增一般符号化投影算法。

## 验证

固定 CompCert v3.18 / Rocq 9.2.0 工具链。`audit_interface_private_check.py` 编译所需依赖并 Print Assumptions：**38 个端点（17 language、21 domain）、465 个实际依赖、812 份源摘要**。language 端点不超出 CompCert 基线；domain 候选检查另外继承 `CoqAddOn.posPr/zPr` 和 `PedraQBackend.add/isEmpty/pr/t/top` 七项既有假设，无新增全局公理。本次没有重编所有历史主接口或执行 coqchk。

提取编译器 `build/compcert-private-scan/ccomp` 已实际构建。原有 [完整 pointer fixture](../examples/native_memory_address_parameters.c) 和 [独立模型](../scripts/native_memory_address_parameters.py)不变；15 个配置分别运行同一组 637 次调用，共 9555 次配置调用，完整 buffers 和公开 counters 与 GCC `-O0 -fwrapv` 及模型一致。覆盖 identity/interchange/fission/tiling、实际 alias、地址参数范围、空／null／未初始化操作数、invalid schedule、oracle resource/fault 和缺失／损坏提案。配置重复不是 9555 组独立输入。

四个 x86-64/GDB 硬件观察点探针，在 direct mapped 和实际 generated schedule 两种 interchange 提案下确认：

| 入口 | 实际写入顺序／值 | 含义 |
| --- | --- | --- |
| disjoint，n=2,m=3,u=3,v=7 | p[51]=-10958，然后 p[36]=-10443 | 实际候选 interchange 顺序 |
| p=q，n=3,m=2,u=v=0 | p[33]=-6096，然后 p[48]=-6401 | 真实 alias 冲突回退为源顺序 |

另有 [上下文 fixture](../examples/native_interface_private_scan_context.c) 与 [独立模型／runner](../scripts/native_interface_private_scan_context.py)：222 组输入，三个配置共 666 次调用。switch/goto/return、外围 continue/break、连续两个 region、全局 effects、alias 和空／未初始化／null 输入通过完整汇编执行对照；interchange／tiling 各插入六处实际 dispatch，资源拒绝配置零处。

`validate_interface_private_scan.py --runtime-order --context` 核对源、提取、compiler、报告、Clight/assembly/output 以及 GDB 输入／结果的绑定。已有 main 415 端点／40 报告、named 和 parametric 134 配置证据的绑定仍通过；本次未重新运行这些旧原生配置，也没有把旧 compiler 算作新 pointer pass。

| 产物 | SHA-256 |
| --- | --- |
| proof report | `03c5f02fc0166ea98f0e593d342391d6ac07a31c101e5c24dcee27afaf40898f` |
| compiler | `eb6b34657b41b9ab11595a04072ab9ee8802a267e1fa7a6870ac4703047925a8` |
| native report | `a16e04b6c9f777a84ced506a124766ea52eea166eb8bfc6a354cf6621c18695f` |
| GDB report | `c05c93696d32e8a3b150d2a4e0cd6816b27768c5bb13b3cea42eb1447bb92eee` |
| context report | `aa498d687495b5107e2d2c9d1950699f5d9240a1445ba98cd727fb605278f67c` |
| validation | `531f09e1933d0738eb77d9e2a5d2cfcf89963d67378ee86f8e4400059a664696` |

## 复现和下一项

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-private-scan-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-private-scan-runtime-order
```

最后一项依赖 x86-64/GDB/ptrace；所有测试都不是性能测量。代码、文档和 push 以本阶段提交为准，产物保存在忽略的 build 目录，摘要绑定上述当前文件。

下一项推进 P3 的受限符号化条件／足迹推导。拟先在已接受 header／同 base 的入口推导仿射 offset 的区间分离，命中时跳过扫描，否则保留既有扫描；这仍须证明实际访问覆盖、机器求值和指针观察的定义性，当前只是计划。明确允许观察、B⇒A 覆盖、机器安全和拒绝策略，并由实际候选消费。一般深度 affine pointer 域、多个依赖 preload、任意无限 pointer fallback、性能与同例证明负担比较仍未完成。详见 [当前计划](current-work-plan.md) 和 [责任矩阵](framework-responsibilities.md)。不以这一阶段关闭活动完整目标。
