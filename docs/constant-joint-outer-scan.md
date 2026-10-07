# 原源许可的 outer 扫描与接受后的双缓存源

2026-10-07。[Inner 消费者](constant-joint-inner-scan.md)现已接到实际 outer
Clight loop。整段接受生产全部 rows／columns 的观察保持，并填入已有语言
运输定理，取得完整双缓存源执行。这里关闭的是检查与缓存源之间的证明连接；
canonical 模型、原 AST factory、候选／host 安装和新提取编译器仍未完成。

## 实际检查代码

[ClightConstantJointOuterScan.v](../prototype/interface/ClightConstantJointOuterScan.v)
定义实际代码：

```c
scan_row_limit = root_cache;
flag = 1;
scan_row = 0;
for (; scan_row < scan_row_limit; ++scan_row) {
    scan_column_limit = child_cache;
    scan_column = 0;
    for (; scan_column < scan_column_limit; ++scan_column) {
        /* 原 constant BODY 许可的完整写地址 × observations 比较 */
        if (!flag) break;
    }
    if (!flag) break;
}
```

这里每个 column 内调用此前的 constant-nest scan，不执行原 stores；这个
BODY 的全部点已经由一次真实原 BODY 执行许可。跨 column／row 则只在接受后
继续，不在新 row 重置 `flag`。实际 component scan 和 leaf 比较复用旧实现。

`constant_outer_row_execution` 从当前原 outer prefix 打开 inner prefix，调用
`constant_joint_current_row_execution`。它生产整 row 的实际检查执行、全部
column 的观察保持和下一 outer prefix；接口没有 `BODY`／`PRESERVE` 语义回调。
`constant_joint_outer_scan_execution` 将这个 producer 实例化到旧短路循环库，
输出原 guard-entry memory、protected-temp frame、实际 Boolean 结果及全部
已接受 rows 的 prefix／比较结果／preservation。

`constant_joint_outer_first_row_refusal` 针对已经初始化的外层 loop，证明第一个
row 拒绝后私有 row cursor 仍为零，没有 increment 或后继 row receipt。
它不是额外的 whole-statement 初始化证明；完整 statement 的初始化与运行由
`constant_joint_outer_scan_execution` 覆盖。一般短路循环的拒绝分支同样不递归
调用下一 BODY，因而不需要其实际内存许可。

## 两份状态及 word 对应

原 source prefix 在 stores 已执行的 memory 中；guard 比较在原入口 memory
中。包围的 logical row 与 guard 的 private row cursor 分开，不通过改写公开
source row 满足求值。

`constant_outer_row_words` 从 logical source word view、当前 private cursor 和
protected-temp frame 构造 inner guard 所需的 mapped words。Row 映射到外层
cursor，column 映射到内层 cursor，其余 prefix／parameters 保持原名称。
内层保护 `row_cursor :: row_limit :: live`；component controls 与这两层 cursor、
flag 和受保护状态均须分离。

每个 row 的数学结果使用 logical inner entry 的 location dictionary；它只用于
证明实际代码的 Boolean 结果，不在 runtime 创建 source 状态。Checked leaf
与 pointer scope 负责实际写数组的绑定，不要求任意无关 identifier 的 location
dictionary 相等。`memory_accesses_back` 继续只运输权限，不运输写后的数据值。

这里 `public` 是这层服务的共享保护接口，含 captured caches；它不是最终用户
程序的最小 live-out 集。语言 preparation／host 仍须把新增 private caches 与
helpers 投影回真正原 source 的公开作用域。

## 全部观察保持与完整 cached-source 执行

`constant_joint_outer_acceptance_preserves_all` 的结论针对任意活动 `(i,j)` 和
任意满足同 row／column／stable view 的真实原 BODY 执行：若执行前全部 raw
observations 一致，执行后仍一致。它不只保持证明过程中选择的某一个 witness。

`constant_joint_outer_cached_source` 消费这个结论，实际填入
`nested_expression_initial_cached` 的 `PRESERVE`，取得：

```text
原：row < root_expression；column < child_expression；component < literal
                                  ↓ joint scan accepts
缓存：row < root_cache；column < child_cache；component < literal
```

两段执行有相同 exit temps 和 final memory，全部 raw observations 保持。
第三层仍是原 literal-bound BODY，尚未把整段缓存源换成 canonical affine nest。
完整缓存执行是接受后的结论；检查许可的输入只有原源 prefix，不含它。

## 空域与有条件读取

`constant_joint_outer_empty_execution` 独立证明 root cache 为零时，只运行三个
private assignments 和第一次 false outer test。它不要求 source prefix、child
cache／header、observer、参数 word、output pointer 或 math-domain receipt。
因此不能为取得这个路径而提前读第二 header。

新语言服务
[ClightEmptyExpressionTransport.v](../prototype/interface/ClightEmptyExpressionTransport.v)
提供 `strict_false_execution` 与 `expression_zero_cached_transport`。后者只使用
原 root header 求值、root cache 和 row 为零及 quiet 原 body，从真实原执行取得
任意 cached body 下的零次 loop 执行；两段均不进入 BODY，child cache 可以未定义。

通用完整 source-prefix 定理本身携带整个 observation list 的 initial match。
未捕获 child 的空 outer 应消费上述独立 empty 服务，不能为了实例化一个双观察
prefix，反过来要求第二 word 可读。完整 factory 仍须实际组装这条分支。
空扫描返回 true 只证明扫描结果，不能单独证明一个先读取 child 的重排候选可用。

Active root 下 child cache 定义性、非负性及 observer receipts 是显式输入；
word／math-domain 输入只量化活动 columns，empty child 不要求 BODY 参数定义。
当前 prefix 主线要求非负的 computed signed counts，负 count 的原 source 行为
仍必须由实际 runtime gate／fallback 处理，本文没有将它计作已接入的接受路径。

## 验证责任与验收

| 责任 | 本阶段交付 | 仍需实际生产／连接 |
| --- | --- | --- |
| Kernel／上层条件库 | Kernel 不变；复用 prefix 和 short-circuit 组合 | 最终 guard certificate 与 conditional candidate rule 尚未组装 |
| Clight 语言服务 | Empty header 执行运输、已有 private frames／权限／双缓存运输 | 原 header receipts 到 fixed-entry laws、typed allocation、public projection、独立 progress／placement 和 whole-program host |
| Domain 实现 | Logical/private words、逐 row producer、真实完整 outer scan、所有 rows preservation、接受后的完整 cached source | Checked leaf／lowering、numeric domain／source words、scope／freshness／writes 当前仍是 typed inputs；factory 须从实际 source／package 生产，随后接完整 canonical model 与候选 |

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make constant-joint-outer-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make constant-joint-outer-validate
```

Audit 继承固定的 inner report，并核对其 sources／objects 保持。14 endpoints
（2 language、12 domain）、565 required dependencies、含 inherited material 的
1,069 源摘要通过；新端点最多使用 6 项已有 CompCert globals，无新增公理。
Kernel 保持闭合，既有完整 compiler 保持 42 项 assumptions。报告 SHA-256：
`24c969d3cda845e6dcc12a41403120cf9fa53fdea253793a563b1f5e6a5d9c8c`。

当前 outer／inner、前一 BODY／constant-model／nested-header 和 loaded-offset
validators 均通过。旧六配置 708 调用、236 Clight 路径、21 machine probes 及 guard
工作量报告只核对既有产物绑定，没有重跑矩阵。Narrative／context-lifting 重新
fetch 后仍为 `271f6fc`，正文与 main 一致。

这是 inherited build 上的增量编译／审计，未另验空 build bootstrap；没有新数组
fixture、extraction、native 或 timing。原 Figure 2 适配源的 16 调用 coverage
结果保持 `not-supported`。后续须连接完整 canonical model、实际 numeric／guard
证书、原 AST／typed pool／candidate／host 和真实 C 验收，随后改进 compact 条件，
测量 guard 工作、接受域、计时和同例作者责任。完整目标 active。
