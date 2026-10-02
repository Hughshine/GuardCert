# 真实 CInstr 调度证书的完整程序接口

`PolCertScheduleRegion.v` 连接真实 `CInstr Names` 实例、条件合成器和完整程序区域宿主。`compile_schedule_regions_correct` 的端点是 Csem→Asm backward simulation，输入是提供已证明片段包的 `propose` 函数。`PolCertStorePackage.v` 已提供动态数组双写的具体包族；真实 `PolOpt` 循环优化器尚未进入原生入口。

`schedule_bridge source candidate` 要求语言插件提供以下接口：

- `bridge_entry_domain`：源 Clight 正常执行建立安全检查所需的域。
- `bridge_assumption`：语言适配所需的前提，可以包括索引范围、无溢出等。它与检查域分开，源的定义执行未必建立候选前提。
- `bridge_decode`：源正常执行及适配前提允许解码为真实 CInstr 指令列执行，保持 temps；逻辑最终状态通过 `concrete_memory_view` 对应源出口内存。
- `bridge_encode`：在检查域和适配前提下，将任意候选逻辑执行恢复为正常 Clight 执行，保持 temps 并连接实际内存。该字段提供候选进展，不能以一个没有执行的关系代替。

逻辑指令列和参数可以依赖入口状态。模型环境可以投影片段访问的变量；插件仍须证明两端执行与实际 Clight 内存的对应。出口覆盖整个内存关系，投影不能隐藏写入。

`schedule_region_package` 加入性质维度、检查原语和公式。`package_presumption` 证明公式成立时，适配前提成立、逻辑入口满足真实 `I.NonAlias`，且源／候选指令列具有 `schedule_certificate`。该证书由满足 Bernstein 写写、写读和读写独立性条件的有限相邻交换组成；它不是一般多面体调度验证器。NonAlias 本身也不是交换的充分条件。

`package_rule` 在接受证据下调用真实 CInstr 调度定理，取得 `CState.eq` 出口；两端内存视图将其转为双向 `Mem.extends`。共享合成器产生 guard 和原片段 fallback，区域宿主将局部证书提升为完整 Clight 模拟与 C→Asm 正确性。桥接字段是必须证明的义务，没有添加为全局公理；命名接口提供数据操作，不解释指令执行。

`PolCertStorePackage.v` 将 [动态下标规则](polcert-dynamic-stores.md) 实例化为该包。源执行取得实际数组地址及已定义下标；接受范围和不同下标条件后，才构造真实源指令列。检查接受也建立单数组逻辑投影的 NonAlias 和交换证书。候选编码通过两次真实 store 恢复 Clight 执行，没有指令执行 oracle。物理内存关系仍覆盖全部内存。

该包使用 `DomainRestriction.v` 为已有下标性质库补充数组地址域，不改变生成的检查代码。`propose_dynamic_package` 用已证明的展平和完整语法等式把包绑定到源片段。`compile_packaged_stores_correct` 给出这一具体包族的完整 C→Asm 定理；[静态双写实例](polcert-store-swap.md) 继续直接提供区域证书。

复现证明为 `make polcert-memory-proof POLCERT_SOURCE=.../verified-compilation-v10-driver`，原生驱动为 `make polcert-store-native`。`build/polcert-memory-region-adapter-report.json` 审计通用接口，`build/polcert-memory-store-package-report.json` 单独审计具体包，实际原生重建及运行由执行报告另行确认。有限源区域、全部 temps 精确对应和 `fn_temps` 不扩展仍适用；内部循环、private temporary 及实际 PolOpt 仍未接入。
