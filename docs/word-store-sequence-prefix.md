# 实际 store 序列与 loaded 原源 prefix

本阶段处理 optimistic loop transformation 的一个前置困难：原 body 有多条
实际数组赋值，后面的 RHS 可能读取前面刚初始化的 cell，同时任意一条 store
都可能改写后续循环测试读取的 header。必须从真实原源执行许可检查，再由接受
建立保持并推进原源；不能预先假定 cached rectangle 的执行来许可缓存生产。

这是语言／domain 库的局部服务，尚未接成新的完整多维 loaded compiler。
前一 [temp-bound 多数组 C 流水线](multi-array-affine-native-pipeline.md)保留其
已安装范围；本阶段不增加 native、Csem→Asm、紧凑条件或成本结果。

## 数据与证明接口

`ClightWordStoreSequence.v` 的 `word_store_site` 描述实际 typed pointer、
word index 和原 RHS。列表长度和 identifiers 不固定。Index 是 CompCert
int32 常量、temp、加减乘的子集，保留 modular word semantics；证明检查安全
不先要求 affine/no-wrap 模型。RHS 保留实际 Clight 表达式，逐条在原执行的
中间内存求值，不能通过权限回运将值复制到检查入口。

`word_store_sequence_tree` 按各 store 的实际地址与捕获 header 地址生成静态
decision tree；一个比较拒绝即跳过后面的比较。它不扫描 RHS 值，也不执行源
stores。比较服务只针对完整、对齐的 `Mint32` word；地址不同据此推出 word
不重叠，不能将结果外推到任意 chunk／byte overlap／volatile access。

`word_store_sequence_domain` 消费捕获的 observer receipt、source/check temp
frame、原源到检查入口的 permission 关系，以及整段实际 assignment-list
执行。`word_store_sequence_point_domains` 从每一条真实 store 取得地址许可：
后一 store 的 receipt 来自前一 store 后的内存；只将访问权限回运到入口。
它不要求各 RHS 在入口已定义。

`word_store_sequence_sound` 证明接受后，任意满足相应 frame 的该序列实际
执行均保持捕获的 header words。`word_store_sequence_condition` 把安全、
正常 check completion、readonly entry 及接受充分性接到既有框架接口。
`word_store_sequence_check_execution` 提供实际 Clight flag 代码执行，memory
保持，其余 temps 只可能在所选 flag 上改变；在完整安装中仍须由 allocator
证明 flag 私有。生成语法只使用地址 templates；observer block/value metadata
属于语义证据，不成为按运行时内容构造 AST 的算法。

`ClightWordStoreSequenceFactory.v` 的 `check_word_store_body` 从实际 AST 返回
`checked_word_store_body`：sites、flatten 对应、index word grammar、normal、
quiet 和空 temp 写集均由 checker 生产。Sequence 结合次序和行政 `Sskip`
允许变化；非 word／含 load 的 index、非完整 int32 lvalue、temp assignment
保守拒绝。该 checker 不推导任意 RHS 的值或候选正确性。

`ClightWordStoreSequenceLoaded.v` 接实际 `i < *h + delta` 原源 loop：

1. Capture receipt 建立入口读取与 private cache 的关系。
2. `word_store_loaded_prefix_initial` 消费原 loaded loop 的实际正常执行，
   建立 prefix 0，不消费 cached-source 执行假设。
3. `word_store_loaded_prefix_receipt` 在尚活动的当前 prefix 取得原 body
   的真实执行、header snapshots、稳定 temps 与回运权限。
4. `word_store_loaded_point_domain` 据此许可该序列的全部实际 store 地址。
   `word_store_loaded_point_execution` 证明静态 probe 的 decision execution。
5. `word_store_loaded_prefix_advance` 只有在当前序列检查接受后，才建立
   header 保持、原源 counter increment 和下一 prefix。

`word_store_loaded_probe_static` 明确静态地址语法与实际 captured observer
的树相同。当前连接是一条源 axis 和一个 loaded header；完整 rank-n nest、
多 header 的条件读取次序及实际 scan exit 仍须组合。该服务的 scope、rename、
稳定 pointer 等静态参数由语言／domain 实现提供，尚未全部变成同族 data
factory 的自动输出。它不构成已完成的新源码用户接口。

## 责任与最难的后继

| 责任方 | 本阶段交付／消费 | 后继责任 |
| --- | --- | --- |
| Generic framework | 既有 readonly condition 与局部 preservation 证书组合 | kernel 不新增指针、array 或 loop 知识 |
| Clight 语言库 | 实际 store receipts、word 地址运输、安全 comparison、私有 flag 执行、header 保持 | typed resources、完整 scan 的 memory/public frame、实际出口运输与安装 |
| Loop/domain 实现 | 用原 loaded prefix 生产点 domain；checker 生产实际 body 的静态事实 | rank-n prefix/coverage、全接受到 cached/model 对应、候选与恢复 |
| 支持族的源码用户 | 最终仍应只提供 marked C 和策略数据 | 当前服务不是要求用户手填 SOURCE／simulation 的替代接口 |

最难的下一连接是：对于完整原 loaded nest，在每个将读取新 header 的边界，
以此前已接受的 store 检查建立读取许可；整个 guard 接受后，才能生产同一
源的 cached/model 执行，并运输到实际检查出口。随后消费已安装多数组的
candidate checker、真实 scheduler/codegen 与 selected host。局部 prefix 不
自动给出 context lifting；region guarantee 与 site/placement evidence 仍分别
由 domain producer 和语言 host 建立。

本 slice 需要的证明闭合后，紧凑充分条件、code size、runtime work、接受域及
完整调用成本继续单独验收，不等待所有 source grammar 扩展。依照 OLO 功能／
可用性参照，scan 的正确性不等于已完成参数化条件简化或可用性能。

## 验证证据

四模块已用固定 Rocq 9.2 工具链编译，独立 audit 查询 **44 端点、16 闭合、
最多 6 项既有 globals**，全部在前一 42-global compiler allowed set 内；
零新增全局公理，绑定实际可达 closure 及审计文件共 **1,100 项**。只读核对
前一 report 的 183 个 bindings，未重跑其全部历史 parent audits。报告为
[`proof-v1/report.json`](../build/multi-word-sequence/proof-v1/report.json)，SHA256：

```text
5a744f66a88b8870eea213a191b99761ae63250813ba5b0b390a50b7bb7e1dad
```

`ClightWordStoreSequenceExample.v` 用实际 `Mem.alloc`／`Mem.store`／`Mem.load`
定律构造同一 block 的 header、A、B，而非抽象独立数组假设。原 body 为
`A[0] = B[0] + delta; B[0] = A[0] + delta`：

- 接受例：header=1、B=5、delta=3；入口 A=`Vundef`，实际赋值序列最终
  A=8、B=11，header 保持 1。实际 readonly Clight check 写 flag=1，memory
  保持；一般保持定理已实例化到此例。
- 拒绝例：B 指向 header，入口 header=2、delta=−2；A 仍先初始化，再被
  第二 RHS 读取。真实第二条 store 将 header 改为 −2；实际 Clight check
  写 flag=0 并保持原入口 memory，不能据此许可 cached bound。
- 静态例：同一序列的重结合／`Sskip` 接受；load index 和 temp assignment
  拒绝。上述执行是 `exec_stmt` 构造性证明；本阶段没有跑新的 Clight
  interpreter、native C 或 assembly 矩阵。

原始失败／中止日志均保留，成功对象及成功 audit 不覆盖。例子的内存证明
通过分配／访问／store 保持定律建立，避免将不可直接反射执行的 memory
permission decision 当成运行器。数字条件计算与实际 source/check 执行证明
分开记录。

## 复现

需要已准备的 CompCert 3.18／Rocq 9.2 proof objects 和现有 compiler baseline。
新 builder 只编译缺失模块；成功的 source/object 不重编，失败日志另存。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/compile_word_store_sequence_sources.py
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_word_store_sequence.py
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_word_store_sequence.py --validate
```

Audit 重新查询本阶段全部端点，绑定它们实际可达的 source/object closure；
只读核对前一 compiler report 的 183 个 bindings 与 42-global allowed set。
它不重新运行全部历史 parent audit，不编译旧 dependencies，也不读取其他
工作者未完成的 word-column/component 文件。
