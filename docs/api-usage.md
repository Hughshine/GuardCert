框架有三个使用层次。使用现有 CompCert 实例的人提供 C 程序和不受信任的候选数据；增加规则的人提供局部条件性正确性证明；增加语言实例的人提供语义性质与检查实现。通用核不分析整数、指针或硬件标志的含义。

接入其他语言及讨论稳定契约时，先读[语言无关接口与分类](language-independent-interface.md)。它规定语言、检查、条件变换和上下文四份契约，并有独立机械化原型。以下记录当前 CompCert 路线的实际使用接口；该路线尚未迁移到新的契约原型。

现有编译器的使用流程是导出源请求，再提交候选：

```sh
mkdir -p requests
GUARDCERT_AFFINE_MODE=disabled GUARDCERT_AFFINE_PROFILE=inferred \
  GUARDCERT_AFFINE_REQUEST_DIR=requests \
  build/compcert-guardcert/ccomp -conf build/compcert-guardcert/compcert.ini \
  -stdlib build/compcert-guardcert/runtime -S -o source.s source.c

python3 scripts/affine_composed_candidate.py requests candidates.sexp --mode shift-tile

GUARDCERT_AFFINE_MODE=external GUARDCERT_AFFINE_PROFILE=inferred \
  GUARDCERT_AFFINE_CANDIDATE=candidates.sexp \
  build/compcert-guardcert/ccomp -conf build/compcert-guardcert/compcert.ini \
  -stdlib build/compcert-guardcert/runtime -S -o guarded.s source.c
```

`source.c` 必须含受支持的规范循环；例如子上界先赋给辅助变量，再将子游标置零。请求包含实际 Loop、参数环境、指令和所提议的有限范围，不是空的接口占位。导出结果不构成证明。

候选可来自人工、脚本或搜索工具。`shift-tile` 实际生成索引平移的中间 Loop 和分块的最终 Loop；每段都接受检查。也可提交 `(partition-target cuts (tile-box 2 3))`，让框架核对分块候选与完整分区展开。导入器和摘要匹配均不受信任。静态检查不接受时不安装候选；接受后才生成运行时检查、候选和原片段回退。

已有实例从源提议控制／地址范围和实际访问分离检查，并证明检查安全及其接受结果足够支持候选。它不会凭候选自动推导任意最弱条件。`compcert-guardcert-conditioned/ccomp` 在有限范围族中寻找第一个静态接受的方案；`compcert-guardcert-versions/ccomp` 可安装多个运行时版本。它们分别有完整程序定理。

规则作者使用以下接口：

| 接口 | 提供的内容与义务 |
| --- | --- |
| `property_dimension S A I` | 原子命题、可计算检查和解释正确性；`Some false` 要证明否定，单纯拒绝应返回 `None` |
| `formula A` | 原子、常量、合取、析取和否定；生成代码保持短路和 unknown 路径 |
| `check_primitives` | 实际 validity/value 测试及其安全求值、状态保持证明 |
| `conditional_preservation` | 在入口域和前提成立时，每次源执行都有对应候选执行，保留指定观察关系 |
| `encoded_decision_rule` | Clight 条件表达式规则，包含类型、定义性、检查原语和局部值保持 |
| `projected_region_contract` | 实际语句片段、私有状态、公开出口和内存的对应，供完整程序宿主消费 |
| `affine_candidate_evidence` | CompCert 多面体实例中的索引、站点、分块、完整分区与逐段组合证据数据 |

语言实例提供 `language S` 的 command、test、observation、执行关系和条件选择构造器，并证明条件构造的语义。检查若需要私有循环或标志，使用 `StatefulGuard` 的状态关系接口；实例必须证明检查不改变公开状态，并能运输源观察和前提。别名分离足以支持某些交换，是具体内存实例证明的事实。

`compile_condition_correct` 证明生成条件精确选择真、假或 unknown 的 continuation；性质维度定理将 Bool 结果连接到逻辑前提。实际 Clight 宿主将局部契约放回函数与外围控制流，`compile_guardcert_correct` 再给出完整 Csem→Asm backward simulation。它覆盖候选与回退的行为，不承诺候选可达、条件最弱或性能提高；这些另以实例证明或运行结果报告。

完整程序定理从 CompCert Csyntax/Csem 起步。C 文本解析、系统汇编器、链接器及运行库不在该定理中。已有 native 检查在这个边界之外另比较实际编译生成的汇编、数组与公开出口。
