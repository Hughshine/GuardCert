# 循环式私有检查：公共接口与实际 pointer compiler

2026-10-06 更新。实际参数化指针扫描已接入公开 `guard_host`、`guard_certificate` 和 kernel 的 `guardify_preservation`，完成 Csem→Asm 证明与编译器提取。上一阶段仅有扫描／分派 facts 的记录保留在 [历史阶段记录](research-checkpoint-2026-10-06-private-scan.md)；本阶段证据与验收见 [公共 compiler 记录](research-checkpoint-2026-10-06-private-scan-compiler.md)。

## 实际输入、条件与目标

source package 定义稳定寄存器 bounds 的矩形嵌套循环；body 对多个真实 pointer 进行带入口参数的仿射访问，并支持独立 RHS scalars、多读取和多语句。它与 readonly 的 `j<U(i,parameters)` 非矩形源是不同 package，不能将两者组合描述成已实现的一般 affine pointer polyhedron。

不受信任的使用者提供 mapped Loop／index-map、tiling 或 affine schedule。实际 schedule generation 的输出还须重新经过候选检查。domain library 从实际 source 访问构造受限 footprint；入口检查先核对活动 header 和机器／参数范围，再扫描访问对和坐标，比较实际地址。候选证书证明抽象单元下的对应与依赖保持；runtime separation 为它提供真实单元解释。拒绝时执行原 source。地址分离不能独自许可任意重排。

```text
result = 0;
一次性 loop {
  raw check;                 // normal 接受；break 拒绝
  result = 1;
  break;
}
if (result) candidate; else source;
```

一次性 loop 只包围检查，candidate 和 fallback 位于它外部。实际 prefix 保留 raw scan 的真实 cursor／flag 环境，不使用 `bool→original temps` 的固定状态函数。result 的初始化和物化都是真实 Clight 写入。

## 三方如何使用

| 责任 | 本阶段交付 | 每个新实例仍需提交 |
| --- | --- | --- |
| 语言无关框架 | 复用既有 `guard_certificate`／`preservation_certificate`／`guardify_preservation`，本阶段没有修改 kernel | 不承担任意前提抽取、footprint 建模或候选正确性 |
| Clight 语言实例 | [Safety](../prototype/interface/ClightPrivateScanSafety.v)：已到达求值与有限续行；[Host](../prototype/interface/ClightPrivateScanHost.v)：实际 checked state、双向 dispatch 和安全到可用；[Preservation](../prototype/interface/ClightPrivateScanPreservation.v)：公开观察、分支运输、kernel 消费与小步 region contract | check 必须属于受支持语法、result 不在 raw 的读写 temps 中；使用者声明保护 ports、source effect bound／scope，宿主检查实际 target scope 和合法 source progress |
| 优化／domain library | [Certificate](../prototype/interface/ClightParamPointerCertificate.v)：指针 guard 的 D、安全和原入口 P；[Preservation](../prototype/interface/ClightParamPointerPreservation.v)：消费实际 candidate 证书；[Candidates](../prototype/interface/ClightParamPointerCandidates.v)：核对 mapped／tiling／schedule 候选；[Compiler](../prototype/interface/ClightParamPointerCompiler.v)：实际表与 Csem→Asm | 实际 source／模型／candidate 对应、入口 footprint coverage、机器地址定义性、P 的 protected-frame 稳定、私有名字与新编码的安全证明 |

`private_scan_preserving_rule` 是语言适配器的接入接口。它要求实际 source/candidate/check、D/P、protected ports 和 source write bound；一份 guard certificate；P 在 checked frame 下的稳定；条件下 source→candidate 的正常执行与公开出口保持；以及从 source 正常执行导出 D。优化方不用重新证明实际 if／一次性 loop、source 的私有 temp 运输和 region 的小步安装。

`C_opt` 来自实际 body／candidate checker；`C_derive` 来自 source footprint／机器域与抽象单元的对应；`C_guard` 来自真实扫描的执行、范围和接受定理；`C_host` 来自通用语言适配器与既有 private-region 宿主。旧条件／候选数学证明继续复用，新 compiler 没有调用旧统一 compiler 的整程序入口。

## 安全与检查关系

`private_scan_safe` 是独立的归纳判断，不把 `check_safe` 定义为“存在完成执行”。set 规则要求实际 `eval_expr`；if 要求可定义的实际 Boolean 测试和每个可选分支安全；sequence／loop 对实际子执行后的状态继续提出安全义务；loop 还需有限的递归续行证明。`private_scan_safe_execution` 在受支持语法下证明真实完成执行可取得。当前 bounded domain 的既有执行见证，经无事件执行的确定性，构造上述安全判断。这不是一般无限检查的安全定理。

raw 语法支持 skip、set、break、sequence、if 和 loop。表达式可以读取内存；排除内存写、call、return、goto 和 continue。语法只保证完成检查没有 events／memory 写，不能独自保证终止。result freshness 使拒绝后 result 保持 0、接受后物化 1；`select_exact` 对任意入口与任意实际 branch 的完成 trace／outcome 成立，不以 domain D 为前提。

公开 `checks` 绑定 raw 从真实初始化环境执行到真实 after，并把 result 的物化计入 checked entry。`private_scan_checks_prefix` 证明它对应真实 prefix 和实际 Boolean 测试；`private_scan_prefix_checks` 反向分解真实 prefix。该 host 的观察量由语言使用者参数化，分派定律不强制分支 quiet 或正常完成，也不会吞掉分支的 break／continue／return。

指针证书中的 D 是 [memory_param_pointer_runtime_domain](../adapters/compcert-memory/GuardMemoryParamPointerProjectedCandidate.v)：源所需的机器值和实际访问 capability；没有预先要求 header 接受或 nonalias。此有限 region 宿主从 source 的正常执行导出 D。所有完成检查执行都保持 globalenv、locals、memory 和 protected temps；接受时建立 P(original)，拒绝不意味着 P 的否定。

P 包括当前 header 接受和受限真实 footprint 的 nonalias。其依赖包含 bounds、入口参数和真实 pointer binding，不能只保护调用者关注的 live-out。已有 [EntryFacts](../prototype/interface/ClightParamPointerEntryFacts.v) 与 [ScanBridge](../prototype/interface/ClightParamPointerScanBridge.v) 提供依赖 coverage、原入口稳定和 result 初始化的实际运输。

## 局部保持与完整程序

语言 adapter 使用正常、无事件 region 的公开 temp agreement 和 memory equivalence 作为 observation。先把原 source 执行运输到检查后的保护环境，再使用候选局部证明；fallback 也经相同运输。`guardify_preservation` 提供实际选中程序的 source→target 保持，随后 `private_scan_preserving_region_contract` 接入真实 Clight 小步 continuation。

compiler 在 private pool 中先为 result 保留一个 slot，其余 pairs 用于 scan 和 candidate lowering。检查 result 对 raw 读写与 protected 集 fresh；source／candidate 的实际 scope 由安装宿主核对。candidate 在 Boolean 读取后执行，其私有写入由局部证书和公开观察处理，不另外要求保存整个检查后 temp 环境。既有 private-region traversal、source progress、frontend 和 CompCert 后端给出 `compile_preserving_pointer_scan_correct` 的 Csem→Asm backward simulation。

局部 host 的完成执行定律仍不包含无限行为。上述 compiler 通过既有有限 region 宿主连接全程序 simulation；没有在此新增任意无限指针 source 的 open-region 协议，也没有把 source→candidate 保持改称双向全程序等价。

## 复现与后续

在固定 Rocq 工具链环境运行：

```sh
make interface-private-check-proof
make interface-private-scan-native
make interface-private-scan-runtime-order
```

最后一项使用 x86-64/GDB 硬件观察点。形式证明、完整汇编输出对照、实际路径探针分别报告；路径探针不计性能证据。审计覆盖 38 个端点、465 个实际依赖、812 份摘要；语言端点只继承 CompCert 假设，候选检查继承 7 项 PolCert/VPL 假设，没有新增公理。

后继 [源观察 alias 包络](source-observed-affine-separation.md) 已证明受限符号推导、全部实际 footprint coverage、source receipt 和 checked fragment lowering。当前 compiler 仍执行此处原 scan；下一项完成新片段的 normalized AST／proposal／完整入口接入及实际跳过 scan 的验收。一般 affine 域与 pointer 组合、机制成本和作者证明负担对照继续按 [责任矩阵](framework-responsibilities.md) 和 [当前计划](current-work-plan.md) 验收，公共 pointer pass 完成不等于完整研究目标完成。
