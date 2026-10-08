# 多 assignment 的数据入口、完整 setup 与 typed scan 资源

日期：2026-10-08。

本阶段生产 generic temp-bound 源 package 和 scan allocation，不依赖前一
两数组 demo 的固定 identifiers。实际源 AST、plain metadata、typed pool
仍是输入；证明字段是 checker 的输出。完整 setup 接受时，package 可以导出
实际源的 Loop 模型。新的 scan AST 已接 typed private frame，但尚未完成泛化
scan 的安全执行／coverage、候选接线和该族整程序安装。

## 数据接口与使用者责任

`multi_tensor_assignment_data` 描述一条实际 assignment：write pointer 与 affine
coordinates、read pointer／coordinates 列表、value expression。
`multi_tensor_region_description` 提供 dimensions、scalars、assignment 描述列表、
cap 与 profile。这里没有源语义证明或 simulation callback。循环 iterator／bound
names 从实际 AST 提出，再独立核对，既不由 demo 常量决定，也不从入口值生成 AST。

`check_multi_tensor_region_source source description` 是本阶段的 source factory。
成功返回 `multi_tensor_region_package source`，包含：

- 实际原源到 normalized nest 的语法对应与既有语义运输；
- 每条 assignment 的独立 RHS／read-use／coordinate 编码检查，以及完整叶子列表；
- 非空 body、nested reset／loop shape、iterator／bound freshness、参数唯一性；
- iterator 与真实 body pointers／dimensions／scalars 的分离；
- scalar-use 和 dimension-read coverage；
- signed cap、所有实际访问的 checked box lowering；
- 对原源执行的 `structured_progress_supported` 证据。

Assignment 数量与标识符是参数，source/model endpoint 不限于 demo 的两条语句。
源 family 仍是现有 nested temp-bound frontend loops 和 checked affine/Horner
assignment grammar；这不等于一般 parametric affine domain 或 loaded 源已安装。

`allocate_multi_tensor_scan source live pool rank` 为两个 rank 维 cursor 和一个
flag 选择资源。它跳过非 int32 声明与源／caller 已用名字，再检查完整长度、
唯一性、freshness 和在 typed pool 中的成员关系。不足或重复会拒绝。
`multi_tensor_scan_candidate_pool` 从剩余 pool 中排除 scan 资源，供已有 candidate
scratch checker 消费。最终 language host 仍须验证整个声明 pool 与 concrete site。

## 一处真正的识别缺口

复用旧 single-operation `tensor_propose_nest` 的初版 checker 编译通过，却在
真实两-assignment 输入上返回 `None`。原因是它将任何恰好两条语句的 body
当作 reset＋child；第二条 assignment 被误提为 child leaf，最后的 shape gate
正确拒绝整个源。这是安全的静态 refusal，没有错误 target。

后继 `multi_tensor_propose_nest` 核对第二条确实是 structured loop、第一条确实
是其 iterator 的 reset，才递归提出 nested child。普通两条 assignments 是完整
leaf，任意其他 statement-list 长度也不因数量被固定拒绝。独立 source equality、
shape 与 body checks 仍负责接受证书；不信任 proposer 自己的判断。

已成功的初版 `ClightMultiTensorDataPackage.v` 保留其 record／语言运输定律，
其旧 `check_multi_tensor_region_description` 不用作新的生产入口。生产路径采用
`ClightMultiTensorRegionFactory.check_multi_tensor_region_source`。
失败编译／计算日志保留在 `build/multi-tensor-data-factory-work/`。

## 动态条件和真实源模型

`multi_tensor_package_setup_guard package` 复用前一完整 setup 编码器，静态生成
numeric／layout／profile／box tree。`multi_tensor_package_setup_run` 用实际原源
执行许可其观察；`multi_tensor_package_setup_accept` 从接受取得动态 setup。
最后 `multi_tensor_package_source_model` 得到实际原源与 entry-indexed Loop
模型的执行对应、相同最终 memory，以及 source iterator exit。

这三个端点从 package 中消费静态证据，没有 entry numeric／layout／box callback，
源模型也不要求 NonAlias。实际 read 使用自己那条 assignment 的中间 memory，
保留同点两次 store 的依赖。Candidate 仍需足够的 separation／dependence 证据；
该要求尚未由这里的泛化 alias scan 生产。

`multi_tensor_allocated_pair_guard` 用 allocator 选出的 names 初始化 flag 并构造
原 pair-scan AST。`multi_tensor_allocated_pair_guard_frame` 对它的实际执行保持
源与 caller 的全部 temps；它不从 frame 推出该 scan 总会安全完成或接受 coverage。
资源分配与地址观察许可是两个不同责任。

## 已验证的行为与边界

九个闭合计算 witness 运行实际 checker／allocator：

- identifiers 改为 41–50 的三层两数组源接受；body 中的行政 skip 也接受；
- pointer metadata 错误、少一条 assignment、unused scalar 拒绝；
- 实际 typed pool 跳过源 iterator、caller `301` 和 pointer-typed slot，分配
  `501`–`507`；pool 不足和重复 slot 拒绝；
- 整个 region 外包 skip 的 raw shape 未通过现有 progress 分类器，静态拒绝。

最后一项是明确的 progress/frontend 限制，不能因为 normalization 等价就隐去
原源的 progress 责任。上述是 Rocq 中的 checker／allocator 计算，不是新编译器
或生成 Clight／Asm 的 native 运行证据。

Framework kernel 与 host 定义保持；语言提供 normalization、progress、typed
resources、写集／frame；domain producer 提供 source metadata checking、所有
访问 coverage、setup 推导与实际源模型。Source 用户仍给标注 C 和 phase／tile
选项，未来描述器是 untrusted frontend 实现，不是要求用户手填证明。

## 下一验收

将相同 package 和 allocation 接泛化 runtime alias scan：从真实源模型生产
每个实际访问的 permission，证明 runtime coverage 和接受充分性，并运输到实际
guard exit。随后接已有 checked candidate／restore，生产 projected guarantee，
消费 selected host 的 progress／placement 和 typed declaration 安装，得到同族
Csem→Asm 与 native/context 证据。当前 source 名称和资源服务已参数化；前一
完整两数组 statement 的固定名实例不能据此称作泛化 guard 或新族安装完成。

Loaded 两次 store 的 header 保持／原源 prefix、真实跨迭代依赖、一般 affine
domains、紧凑安全条件及 OLO 的完整成本／接受域／作者负担仍在 active goal 中。

## 复现

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/compile_multi_tensor_data_factory_sources.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_multi_tensor_data_factory.py --validate
```

独立报告：`build/multi-tensor-data-factory/proof/report.json`。
只编译新模块，保留成功的 source／objects 和旧 parent closure；不运行 `coqchk`。

七模块 audit 查询 32 端点：26 闭合，其余最多 6 项既有 globals。121 项直接
绑定加已验证 parent closure 保持旧 42-global compiler baseline，零新增公理。
报告 SHA-256：
`3dd7dbf82727c8f1f6aa6ececb4a01a59dd8734ce97d94b7682ba36734346576`。
