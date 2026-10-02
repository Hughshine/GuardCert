# 真实 CInstr 调度证书的完整程序接口

`PolCertScheduleRegion.v` 将真实 `CInstr Names` 实例、条件合成器和完整程序区域宿主连接起来。`compile_schedule_regions_correct` 的端点是 Csem→Asm backward simulation。这个定理针对一个提供已证明片段包的 `propose` 函数；目前尚没有具体调度片段包，也没有将真实 `PolOpt` 循环优化器放入原生编译入口。

`schedule_bridge source candidate` 要求插件提供两个方向的语言桥接：

- `bridge_decode`：源 Clight 片段的正常定义执行建立检查域、不改变 temps，并解码为真实 CInstr 指令列执行。其最终状态通过 `concrete_memory_view` 对应源的实际出口内存。
- `bridge_encode`：在检查域中，候选 CInstr 指令列的执行生成正常 Clight 执行，不改变 temps，并对应候选出口内存。该字段提供实际候选进展，不能以一个没有执行的关系代替。

逻辑指令列和参数可以依赖入口状态，因此不要求所有迭代访问都静态固定。模型环境也可以投影片段访问的变量；插件仍须证明两端执行与实际 Clight 内存的对应。内存出口检查覆盖整个内存关系，不能通过投影隐藏写入。

`schedule_region_package` 加入性质维度、检查原语和公式。`package_presumption` 证明公式成立时，逻辑入口满足真实 `I.NonAlias`，并且源、候选指令列具有 `schedule_certificate`。这里的证书由满足 Bernstein 写写、写读和读写独立性条件的有限相邻交换组成；它不是一般多面体调度验证器。

`package_rule` 调用实际 CInstr 重排定理，取得 `CState.eq` 出口；再用两端内存视图将其转为双向 `Mem.extends`。共享条件合成器产生 guard 和原片段 fallback；`select_schedule_region_sound` 把每个包变为区域宿主的局部证书。随后 `schedule_program_correct` 和 `compile_schedule_regions_correct` 分别给出完整 Clight 和 C→Asm 正确性。

这些桥接字段是插件必须证明的义务，没有作为全局公理添加。命名接口只提供数据操作，不解释指令执行。实际 CInstr 的执行、内存关系和 Bernstein 定理继续来自锁定的 v10 源码。

`PolCertStoreRegion.v` 已开始补具体解码实例：对经过边界检查的普通 signed32 数组、常量下标与常量写入，`constant_store_inv` 从实际源 Clight 执行恢复数组地址和真实 `Mem.store`，`constant_store_run` 给出反向生成。它支持局部数组和经符号表取得的全局地址；具体指令列的包、重排条件及原生选择器仍需构造。

独立的 [双写重排实例](polcert-store-swap.md) 已进一步构造源执行、调用真实 Bernstein 定理并恢复候选 store，直接形成完整程序区域证书；独立原生入口已提取运行。这一实例尚未包装为上述 `schedule_region_package`。调度包的实例数量与具体区域实例分别记录。

复现命令为 `make polcert-memory-proof POLCERT_SOURCE=.../verified-compilation-v10-driver`。`build/polcert-memory-region-adapter-report.json` 单独记录完整程序接口的假设审计和未完成义务，避免把接口定理当作具体多面体优化已经运行。有限区域限制、全部 temps 精确对应和 `fn_temps` 不扩展仍适用。
