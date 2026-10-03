# 语义等价的域表示与统一候选入口

循环交换后的域可能有不同的约束写法。例如源循环 `i = 0..N-1; j = 0..i`
和候选 `j = 0..N-1; i = j..N-1` 枚举相同的整数点，但两个提取器产生的约束行并不相同。
只排序行不能建立这个对应。现在的外部候选入口在坐标对应之后，逐条检查两个域是否相互包含。

`GuardMemoryDomainAlignment.memory_check_domain_inclusion` 对目标的每条约束，检查
“源域且该约束不成立”是否为空。它复用已有的 `isBottom` 和 LCF 证书检查；证书失效或
资源不足不会产生成功的域对应。双向包含检查成功后，`memory_check_domain_equivalence_correct`
证明每个整数点在两个域中的成员资格相同。约束行完全相同时使用一个已证明的语法快路。

`memory_align_domains` 用已核对的源域表示替换候选域，保留候选指令、实参、时间戳和
其他元数据。`memory_aligned_domains_execution` 通过点双射接口证明整个 PolyLang 执行
不变。`GuardMemoryEquivalentDomainsExtractor` 将实际源／候选提取、iterator 坐标对应、
域等价和实际双向依赖验证接起来。最终的 `validated_memory_equivalent_domain_loops_at`
连接原始的两个 Loop，保留入口参数与实际 CompCert Mem。

这不是把域等价当作一个布尔 oracle。空域的原生搜索仍不受信任，接受结论来自已证明的
证书检查器。完整编译定理的全局假设仍是原有 CompCert 和 validator 的 42 项并集。

## 同一个编译器消费两类提案

`GuardMemoryUnifiedCompiler` 暴露：

```text
guarded_memory_candidate :=
  GuardedAffineCandidate Loop.stmt (list nat)
  | GuardedTilingCandidate Z Z

guarded_memory_proposer :=
  list memory_instruction -> option guarded_memory_candidate

compile_memory_unified_regions proposer private_count Csyntax.program
```

仿射提案可以重排、融合、分裂循环或带上仿射条件；其中的指令引用必须来自已核对的源
片段。分块提案提供两个块宽，走已经证明的二维 tile witness 路径。两类提案共用同一个
源识别、私有临时变量池、实际运行时 guard、原片段回退和完整程序宿主。
`compile_memory_unified_regions_correct` 对任意 proposer 给出成功编译时的完整
`Csem` 到 `Asm` backward simulation，不要求提案生成器正确。

原生入口读取 `GUARDCERT_LOOP_CANDIDATE` 指定的候选文件。已有的 loop／reindex 文件
继续使用仿射入口；分块可以写成：

```text
(tile 4 4)
```

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make native-memory-unified
GUARDCERT_LOOP_CANDIDATE=/tmp/candidate.sexp \
  build/compcert-memory-unified/ccomp \
  -conf build/compcert-memory-unified/compcert.ini \
  -stdlib build/compcert-memory-unified/runtime -S examples/native_memory_operations.c
```

一般 IR 的测试已通过 24 个提案和 1632 次独立执行比较，包含三角形域的交换、冗余约束
以及删除对角线点的拒绝见证。完整 C 的外部仿射入口已通过十二组配置，每组 1564 行
完整输出与 GCC 和独立模型一致；冗余条件实际命中全部十个适配函数。完整 C 源识别仍是
当前单数组矩形混合读写列表，因此三角形域交换的这份新证据目前位于 Loop IR 层。
统一入口也已通过十二组仿射配置、五组二维块宽和五条分块拒绝路线，每组均检查这
1564 行输出。两类提案实际使用同一份编译器可执行文件；报告位于
`build/native-memory-unified/report.json`。
[多个实际数组对象](memory-multiple-array-objects.md)已接入统一入口。一般源 AST 提取、跨数组读取、指针切片以及整数剪切与平移的坐标对应仍在继续实现。
