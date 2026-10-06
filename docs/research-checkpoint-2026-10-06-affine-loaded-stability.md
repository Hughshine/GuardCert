# 独立 bound pointer：按源顺序取得检查许可

2026-10-06。本阶段基于 `c821517`，沿 topdown
`7d94d810685a691efbf07df734f5fad8abfb4724` 的叙事继续实现。
**这是新增证明服务；独立 bound pointer 的完整优化／编译器安装尚未完成。**
当前可运行的 loaded compiler 仍以 [此前阶段](research-checkpoint-2026-10-06-affine-loaded-compiler.md)
为准。完整 goal 保持 active。

## 为什么必须按源顺序

目标源片段可以是：

```c
n = *bound;                    /* retained source snapshot */
for (; i < *bound; ++i) {
  k = i + 1;
  for (j = 0; j < k; ++j)
    p[32 + 64*i + j] = q[4096 + 64*i + j] + a;
}
```

`bound` 不必等于 body 中任意一个 pointer。它可以是另一个 allocation，
也可以指入 `p` 的某个单元。正确性的前提是全部实际源 writes 保持这次
bound 观察；只判断 `bound != p` 没有覆盖偏移写入。

把初始 `n` 对应的所有假想 writes 一次比较完也有安全问题：某一 store
可以改小 `*bound`，使源提前结束；后续假想行的地址不一定具有可支持
指针比较的访问权限。CompCert 的不同-block pointer ordering 也不能当作
总函数使用。因此本阶段选择实际 pointer equality，并从源到达证据取得
当前行的权限。每行 guard 成功后才推进源执行的 ghost witness。

```text
原入口 snapshot／接受范围 + 剩余实际 loaded-loop 执行
          |
   实际活动 header -> 当前整行真实执行
          |
   当前所有 stores -> write receipts -> 权限运输回原 guard entry
          |
   只读地址相等检查：有定义、完成、接受蕴含 byte separation
          |
   接受：该行保持 bound load -> 剩余执行推进到下一行
   拒绝：停止，不检查后续行
```

当前内层 bound 在执行 inner loop 前计算完成。即便当前行最后写中 outer
bound，当前整行仍来自真实源执行；这可以支持当前行全部比较，但不自动
支持下一行。Guard 不执行图中的 stores 或 ghost source steps。

## 已实现的证明与责任

| 层 | 本阶段源码／证明 | 仍由实例交付 |
| --- | --- | --- |
| 最小 kernel | 未修改，仍组合条件证书与条件性源／候选保持 | 不提取 optimizer assumptions，不证明 Clight 安全或程序安装 |
| 核上的框架库 | 复用 [ReadonlyPrefixScan](../prototype/interface/ReadonlyPrefixScan.v)，证明有依赖前缀检查的组合；该端点 closed under global context | 每个活动分类器及正结果续行证书；足够 fuel 的覆盖 |
| Clight 权限／比较 | [ClightStorePermissions](../prototype/interface/ClightStorePermissions.v) 证明真实 store 及 counted points 的权限反向运输；[ClightWordAddressSeparation](../prototype/interface/ClightWordAddressSeparation.v) 证明 typed word-pointer equality 安全、完成、接受蕴含物理 byte separation | 当前地址表达式的实际求值、Writable write receipt 和已定义 bound load |
| Clight 源推进／扫描 | [ClightLoadedRowPrefix](../prototype/interface/ClightLoadedRowPrefix.v) 从实际活动源取得 row receipt、接受保持后续行；[ClightLoadedRowScan](../prototype/interface/ClightLoadedRowScan.v) 消费旧 prefix library；[ClightReadonlyExpressionScan](../prototype/interface/ClightReadonlyExpressionScan.v) 提供运行时 signed-expression bound 下的检查代码、覆盖与证书 | 真正 row decode、参数 frame、point 权限和 row probe 条件；这些是证明参数 |
| 数组／多面体 domain | [GuardMemoryWriteReceipts](../adapters/compcert-memory/GuardMemoryWriteReceipts.v) 将真实物理 stores／当前完整 row 变成每项 write receipt；[external transport](../adapters/compcert-memory/GuardMemoryLoadedExternalTransport.v) 扩展 protected frame，独立 bound pointer 不要求属于 body pointer 列表 | 本次实际源、范围和参数值；接受分离覆盖其全部 writes |
| 地址／condition 编码 | [坐标替换](../adapters/compcert-memory/GuardMemoryAffineAddressSpecialization.v) 证明原入口求值；[多写探针](../adapters/compcert-memory/GuardMemoryAffineWriteSeparation.v) 复用已有 access encoding／range checker；[当前行 guard](../adapters/compcert-memory/GuardMemoryAffineRowSeparation.v) 证明真实扫描安全、可用、接受保持 bound 观察 | `memory_affine_row_domain` 的 arithmetic／word／receipt 字段要从 checked source package 与实际 row 生产 |

Word separation 使用实际 `Mem.valid_access Mint32 ... Writable` 和 bound
load 所给的对齐与权限，两个不同有效 word addresses 才推出 byte separation。
它支持不同 memory blocks 的等号比较，也支持同 block 内不同有效偏移。
没有 pointer order、pointer-to-integer conversion 或运行时 `Mem.valid_access`
查询。算术求值使用 CompCert modular representation；数学 index 的 signed
范围由已有 checked access／box 证明另行提供。

`memory_affine_at` 把当前 `(i,j)` 替换成 constants，其他参数仍在 runtime
读取，证明生成地址等于该实际点的物理地址。不需修改或读取当前公开
`i/j` 的值。`memory_affine_checked_write_ready` 消费原来的 source affine
encoding 和 range certificate，没有新建一个独立可信编码器。

`memory_affine_row_probe` 输出真实 decision tree，按照 `j < U(i,parameters)`
选择活动点，仅运行这些点的各 write 比较。它已经有 readonly condition
证书和实际物理 point-step 的 load 保持定理。其 domain 只要求当前行
receipts；没有假定未来行的执行、未来访问权限或 bound 稳定性。

`loaded_row_prefix` 保存剩余真实 source execution、stable temp agreement、
当前 bound load 以及从当前源 memory 回到原 guard entry 的权限运输。
Memory values 并不相等。`loaded_row_prefix_receipt` 不需要保持假设；
`loaded_row_prefix_advance` 需要本行 positive preservation evidence。
`loaded_rows_scan_sound` 只覆盖给定 fuel 范围，fuel 耗尽不是完整稳定性的证据。

## 尚缺的实际实例连接

这些接口参数没有被“无新增公理”的审计自动消去：

1. checked source package 的原入口 ranges／typed parameter values、实际 row
   decode 和 frame，必须产生每次到达的 `memory_affine_row_domain`，并证明
   初始 loaded-prefix invariant 以及全部活动 rows 的 fuel 覆盖。
2. 将已证明的当前行 probe 作为 `loaded_rows_prefix_spec` 的 `ROW_CHECK`，
   将真实 physical sequence preservation 作为其 `PRESERVE`；当前通用
   scan 定理量化这些有类型的证书，不等于已实例化完整源。
3. 正结果接到 external loaded→cached 运输、原 mapped／tiling candidate
   checker、restore 和 guarded fallback；matcher 核对独立 bound pointer
   的 producer／保护集，并复用旧 progress／placement／Csem→Asm。
4. 提取并运行完整 C：独立 allocations、同 block 切片、写中 bound 导致
   源提前停、alias 后后续危险地址不被检查，以及公开出口／外围上下文。

源完成证据仍是 finite normal completion。没有新增任意无限源的安全域，
没有插入 private snapshot，没有解决多个依赖 preload。已生成的 unrolled
scan 还需评估实际 AST／共享 fallback／runtime 成本；本轮未测量性能。

## 验证与证据边界

独立命令：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  make affine-loaded-stability-proof
```

[审计脚本](../scripts/audit_affine_loaded_stability.py)编译所选依赖 closure，
检查各新增 endpoint 相对 CompCert／mapped／tiling baseline 无新增全局
公理。此次使用 Rocq 9.2、OCaml 4.14.1，**增量编译**；没有 clean 全量重编。
共 40 个新端点，其中 17 个 language 端点；567 个实际依赖、911 份源码
摘要。两个旧 full-compiler regression 都继续继承 42 项 baseline 假设。
报告明确将 new source-package instance／candidate connection／whole-program
endpoint／frontend／extraction／native 置为未安装。

[真实 Clight fixtures](../prototype/interface/ClightAffineWriteSeparationExamples.v)
证明 `p[32+64*1+1]` 地址在无 `i/j` 绑定时仍可求值；与 bound 地址一致时
拒绝、不同有效 blocks 时接受；拒绝后不运行任意 tail。这是有实际 memory
权限前提的符号证明，不能算作原生调用。

本轮重新核对此前 loaded 和 cached 两份 native 报告与源码／对象／编译器
stamp 的绑定，两个 validator 均通过。**没有重执行旧原生矩阵**：

| 历史矩阵 | 原报告调用／机器探针 | 本轮范围 |
| --- | --- | --- |
| loaded compiler | 1,650／7 | 报告／源／对象／stamp 绑定核对 |
| cached affine-inner compiler | 891／7 | 同上 |

证明报告与摘要在 `build/affine-loaded-stability/proof/report.json`；摘要在
下方验收补记，不作为仓库中的生成物提交。

验收摘要：

- 新 proof report：`2f12356f3805a172902089008db1cbf9ef2e4fa9b59071963c6b967bd8d4b89d`。
- 审计脚本：`680b9f30429970e9cc9be164f71f3716da4acf41fd6782eafb05e14aa15fca76`。
- 旧 loaded native report：`cb3ab04c6681e1798f44433a6c41a4cc33203ef094dea11dc7b588bcd57d0f82`。
- 旧 cached native report：`d7d8d31cbdeed3ddf71a9f647adb412c88928263ae451d76b3acb13523b5a515`。

最后逐项复核新报告的全部源码与对象摘要、审计脚本摘要，以及 checkpoint
链接；均通过。没有从端点数推导性能、新颖性或总作者证明负担收益。
