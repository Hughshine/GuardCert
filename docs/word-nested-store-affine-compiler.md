# 双 loaded store-list：候选分派、region guarantee 与整程序定理

2026-10-08。本阶段将 [数据入口](word-nested-store-data-factory.md) 连接到既有
完整多数组 affine/tiling candidate checker，导出 projected region guarantee，
并消费既有 expression-progress selected host 接 Csem→Asm。

这是新族的证明连接。其实际 C metadata frontend、提取后的 compiler driver、
真实 Pluto/prepared codegen 安装与 native 验收仍待连接；旧 temp-bound 多数组
流水线的运行证据不能替代它。

## 暴露的数据接口

`check_word_nested_store_affine_region public typed_pool describe describe_cached
propose source` 消费实际 Clight source 与三种普通数据提案：

- `describe` 提出 loaded source 的两个 iterator、header pointer/offset 和 body；
- `describe_cached` 看到已分配缓存的实际 AST，提出 access/value、dimension、
  profile 和 cap metadata；
- `propose` 看到 checked model 的 instruction list，提出候选 Loop 数据。

源/body/static/model checker 和完整候选 checker 独立检验这些提案。源码
使用者不提交 execution、simulation、NonAlias 或 READY 证明。无法识别、
资源不足、模型不匹配或候选验证不通过，返回静态 refusal。语言 host 再检查
placement、原 source progress、scope、private declarations 和合法出口。

这个入口属于 domain/compiler 库。最终支持族的使用体验仍应是 marked C
和 phase/tile options；本阶段没有完成该族的自动 C 描述者。

## 实际运行时代码

候选 checker 返回的是完整 versioned Clight statement，包含 numeric/layout/
box/profile 准备、实际 alias scan、候选执行、公开 iterator 恢复和 cached
fallback。外层代码为：

```text
完整 source-licensed header guard
if header_flag then
    if root_cache > 0 then
        完整 checked cached-model candidate version
    else
        cached source
else
    原 loaded source
```

这里有两层动态 refusal。Header 检查拒绝时执行原 loaded AST；header 接受、
内层 model/setup/alias 检查拒绝时，执行已证明与原源对应的 cached AST。
接受模型条件时才运行实际候选；私有 scan temps 不属于公开退出状态。

外层空域有独立路径。完整 header guard 可在 child pointer、child cache 和
数组未定义时接受。因而候选准备不能无条件读取所有模型参数。新增 positive
root test 使空域直接执行不进入 body 的 cached outer loop，绕开整个内层版本。
这不是把参数定义性作为 caller 假定，也不是在空域运行一次候选 checker。
候选 checker 在编译时运行；本段讨论的是它生成的准备代码。

## 从局部执行到 host

`nwsp_guard_execution` 从实际原 source 的正常执行生产 conditional capture、
完整 guard 执行、memory/public frame、flag 值和接受后的 cached execution。
cached execution 已位于**实际 header-guard 出口**，而非另造的入口状态。

`nwspp_affine_execution` 消费这个 receipt 和完整候选 checker 的接受结果。
活跃接受将 cached execution 交给既有多数组 candidate 定理；空域跳过其
准备；header refusal 则用 scope/frame 将原 source 运输到实际 guard 出口。
三条路径保持原 final memory 和请求的 public temps。

`nwspp_affine_contract` 导出既有
`PrivateRegion.projected_region_contract public source target`：公开 temps
关系、memory equivalence、silent execution 与正常有限退出。它不是原始
Clight 全状态相等，也不承诺任意控制退出或任意发散 region。

`checked_word_nested_store_affine_regions_sound` 为有限 accepted table 逐项
提供这个 guarantee。新的
`compile_selected_word_nested_store_affine_regions` 依次执行 SimplExpr、
SimplLocals、selected source 收集、typed pool、checked table、既有 expression
host 安装和 CompCert tail；其 correctness endpoint 是 Csem→Asm backward
simulation。数据提案者与选择策略被量化，不在语义可信边界内。

安装仍由语言 host 检查 occurrence selection、source progress、scope、fresh
declarations 和 label/exit 约束。特别是使用原 loaded source 的 progress，
不是其 cached AST 的 progress。局部正常执行定理与 whole-program theorem
通过这个明确的 host 连接；前者本身不提供任意 contextual closure。

## 三方证明责任

| 环节 | 本族中由谁提供 |
| --- | --- |
| 局部 certificate/guarded-choice 组合 | framework kernel；本阶段未改 |
| capture、地址/word 安全、条件读取、frame 和实际出口运输 | Clight language 服务；factory 实例化静态证据 |
| header 稳定性、原源→cached→model→candidate 对应 | domain 服务与已验证的模型/候选 checker |
| checked candidate 的 affine/tiling 条件正确性 | 既有 polyhedral checker；候选算法只提案 |
| region guarantee | domain producer 接局部执行与 projected contract |
| context requirement、progress、scope、资源和整程序安装 | 既有 Clight expression host；site 检查消费具体 guarantee |
| 真实模型描述、调度/codegen 和标注源码体验 | ordinary compiler producer；本族 native 接线仍待实现 |

没有新增 kernel API 或 host contract，也没有将 narrative 的 guarantee/
requirement clause algebra 开放讨论实现成新接口。已 fetch 并核对 narrative
`12419c1e1e3da450bf378742a2fb4e204e51e060`；两份 topdown 正文均与 main 相同。
其中实际 optimizer 集成和 OLO 可用性仍是任务约束。

## 验证范围与下一项

独立审计查询三个模块的 14 个端点：6 个闭合，局部候选端点使用 14 项旧
globals，整程序端点使用既有 42-global baseline，无新增公理，绑定 1,380
个可达文件。报告见 `build/multi-word-nested-affine/proof-v1/report.json`；编译与失败
尝试日志见该 stage 的 `source-build`。成功 proof objects 和前阶段输入保持
冻结，审计核对前阶段 1,280 个绑定，不重跑历史实验。

Rocq fixture 证明任意 candidate 在外层空域不可达，child pointer/cache 和两
数组 temps 仍为 `None`。普通数据 checker 接受两个 loaded axes 的二维物理
layout、两数组和两条有意 flow-dependent stores，拒绝错误 read metadata。
这些是 checker/`exec_stmt` 证据；没有新的 native C、Asm 或成本数据。

下一项直接连接本族 marked C 的实际 AST、自动数据描述、两轴真实 Pluto/
prepared codegen、提取的已证明 compiler 入口和 native 接受/两层 fallback/
空域/重复 region/continuation 验收。需要处理真实 C normalization 的 reset、
wrapper 与 loaded-header 表达式，不能把第三条虚拟 axis 或手写目标当作
两轴 optimizer 安装。紧凑条件、安全/充分性/运输、接受域与完整成本、一般
参数化 affine source 和 OLO 对照继续验收；本阶段不标记 active goal 完成。
