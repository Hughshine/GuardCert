# 2026-10-06：真实私有扫描的原入口前提与分派证明

本阶段关闭参数化 pointer scan 的原入口前提运输、实际 result 初始化，以及检查 wrapper 的双向 statement 分派。新增语言服务与 domain 桥均通过 Rocq 编译和假设审计；没有改变语言无关 kernel 或旧优化语义库。公共 pointer host／compiler 尚未安装，完整目标保持进行。

上一阶段的 [参数化 affine 编译器](research-checkpoint-2026-10-06-parametric.md)已推送于 `b4e82f36d8bf71057b5c771a54a6fd1bd2588c75`。此次沿 [topdown narrative](topdown/paper-narrative.md) 将困难义务落实为真实语言和 domain 定理，见[责任矩阵](framework-responsibilities.md)，没有将新接口数量算作研究增量。

## 关闭的语义义务

旧 scan 写私有左右游标和 flag，旧 witness 只建立 `P(checked)`。公共证书要求 `P(original)`，而 P 观察源 header、寄存器 bounds、参数／scalar context、实际 footprint 和 pointer bindings。仅保持调用者声明的 live set 无法自动满足这一要求。

[ClightParamPointerEntryFacts](../prototype/interface/ClightParamPointerEntryFacts.v) 复用已有 header 和 footprint frame，从源 header 成功取得实际 bounds 的 word／数学对应，再由 footprint membership 证明每个允许访问的 pointer ID 都属于 protected 集。它得到受限 location view 的逐点相等和原入口／检查后 P 的双向稳定；没有新增函数外延公理。请求旧 encoder 的更强 protected frame，再复用完成确定性，即得到所有完成 raw scan 的 `accepted⇒P(original)`。

[ClightPrivateScan](../prototype/interface/ClightPrivateScan.v) 提供真实包装：

```text
result = 0;
loop {
    raw_check;       // normal 接受；break 拒绝
    result = 1;
    break;
}
if (result) candidate; else source;
```

语言证明检查代码的受限语法只读 memory、可写 temps、无事件，完成出口为 normal／break。raw 可包含结构化循环和实际读取，但不含内存写、call、return、goto 或 continue；这项语法本身不保证终止。

`private_scan_select_exact` 对所有入口和任意候选／回退的完成执行证明双向对应。分支处在 wrapper loop 外，因此保留实际 trace 和 break／continue／return；没有以 D 为前提，也不要求分支 quiet 或正常完成。`private_scan_prefix_dispatch` 在实际 CompCert program globalenv 上给出到所选分支入口的小步 star，不要求该分支完成。

[ClightParamPointerScanBridge](../prototype/interface/ClightParamPointerScanBridge.v) 证明实际参数化 scan 属于这项语法，并将真实 result 初始化纳入运输。result 对 raw 读写 temps 与 protected 集 fresh 时，原 scan 的实际执行可在 result 初始化后复现；prefix 保持 protected 观察并物化正确接受值。所有完成 prefix 执行均保持 memory、无事件、正常退出；实际 result 测试成功建立原入口 P。检查后的真实 cursor 没有被替换为一个仅依赖 bool 的函数。

## 三方责任和范围

| 层 | 本阶段实际交付 | 下一项仍需交付 |
| --- | --- | --- |
| 语言无关框架 | 复用既有 `guard_host`、certificate 与组合边界，kernel 未改变 | 消费实际新 host／证书；不承担 pointer 或 loop 语义 |
| Clight 语言库 | 新 scan 语法、无事件／memory frame、实际初始化包装、statement exact dispatch、分支前小步 prefix；复用确定性和 temp transport | 实例化公共检查关系、安全／观察范围与 host；分支运输、private scope 和完整安装 |
| 优化／domain 库 | 实际源 footprint 的 pointer 覆盖、P 的 protected 依赖、原入口接受结论、真实 scan 语法与初始化 witness | 绑定旧 candidate checker 和实际 source／target；提交扫描资源与 source progress，提取和运行一个公共 pointer pass |

这里的 pointer package 是稳定寄存器矩形 bounds 下的参数化仿射访问；它与 readonly `j<U(i,parameters)` 的非矩形源 package 分开记录。D 沿用 source-derived runtime domain，没有增添 no-alias 或 P。当前已有 witness 的域不自动扩大为任意 source 或 allocation。

statement exact 和 prefix steps 已证明，但公共 `guard_host`／`guard_certificate` 尚未实例化。检查安全仍须在该实例的具体解释中落实；完成 witness 和完成确定性不能被改称任意小步路径／无限行为的完整宿主定理。完整 normal macro host 仍要求 source progress，任意无限 pointer fallback 继续是独立义务。

## 验证与产物身份

`make interface-private-check-proof` 编译所需 closure 并审计 15 个端点：六个语言端点、九个实际 domain 端点，392 项依赖、805 份源码摘要。全部新增模块实际编译通过，继承假设不超出 CompCert 35 项；旧 scan 的六项假设已包含在该基线中，无新增全局公理。计数与其他审计有重合，不相加。

| 产物 | SHA-256 |
| --- | --- |
| `build/interface-private-check/report.json` | `64ab74f879b05033515eddd183e303fd8ca5e0217c0336468d657b96ce858d78` |
| `ClightPrivateScan.v` | `8634bb3c115d7d5644ae05974e2a5e06424c5ef6f43dd332ef168a9ea7a770de` |
| `ClightParamPointerEntryFacts.v` | `a5bd5d58285004faa98e134601c85fb8b0d3b783e1c6fe58a4354630da83b842` |
| `ClightParamPointerScanBridge.v` | `c6e51c5e08e4b5f46f6aeb7f504b9503111eba7cd0582bf38e73c9b4a2f14aeb` |

当前参数化编译器的 134 配置／四个顺序探针、named 编译器的 40＋8 配置以及主接口的 25 配置／40 报告，全部源码与产物绑定重新核对通过；本阶段没有重新运行这些 native 配置。旧编译器和 native 输入未改变，新 wrapper 尚未进入提取入口。因此本阶段交付的是实际语义证明，不声称已运行新的 pointer pass 或取得性能收益。

本阶段重新 fetch 并核对三个评审分支，锚点仍为 `f793629`（topdown）、`9673381`（evidence-to-claim）、`3e9f008`（performance），没有新提交。责任划分、困难义务和 completed／infinite 边界继续按这些意见维护。

下一项按[迁移规格](clight-private-check-migration.md)完成公共证书、分支状态运输和真实安装，然后提取运行 pointer fixtures。一般深度 affine 域、一个实际受限符号条件／footprint 推导算法、同例作者负担与性能仍独立验收；完整 OLO 目标没有缩小为本阶段的 proof facts。
