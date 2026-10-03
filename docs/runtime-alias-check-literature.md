# 运行时 alias 检查：既有能力与当前语言义务

核对日期为 2026-10-03。这里比较具体检查算法及其语义要求，不把使用 guard、版本化或动态 nonalias 本身作为新颖性主张。

## 动态前提和区域版本化已有直接先例

Alves 等的 OOPSLA 2015 论文 **Runtime Pointer Disambiguation**，DOI `10.1145/2814270.2814285`，同时讨论分配器元数据检查和静态生成的符号／多面体访问范围检查。它在区域入口选择带 nonalias 信息的优化版本或原版本，§4.3 还处理检查所需表达式的可用性和新鲜辅助变量。这补充了用户指定 CGO 2017 工作之前的直接需求先例。[作者全文 §§2–4.3](https://homepages.dcc.ufmg.br/~fernando/publications/papers/OOPSLA15.pdf)

因此，自动构造动态检查、使用私有临时变量或把区域嵌回程序，都不是孤立的新贡献。当前要交付的是实际语言中的检查正确性、安全求值、公共状态运输和完整程序证明。本文核对的是论文给出的算法与论证，没有把它们当作已经取得的 Rocq／CompCert 定理。

## 检查成本及读写角色同样已有先例

该论文 §5.2.1 按至少一侧可写选择指针对，也分析检查数量和运行时成本。[作者全文 §5.2.1](https://homepages.dcc.ufmg.br/~fernando/publications/papers/OOPSLA15.pdf) 当前 LLVM 的 `RuntimePointerChecking::needsChecking` 明确跳过两个只读指针，另外根据 dependency set 和 alias set 决定是否需要检查。[LLVM LoopAccessAnalysis.cpp](https://github.com/llvm/llvm-project/blob/main/llvm/lib/Analysis/LoopAccessAnalysis.cpp)

GuardCert 当前的受限视图要求所有不同逻辑指针的活动单元分离，包括只读单元，因此仍比这种策略保守。删除只读比较必须同时改变具体内存实例的性质：逻辑对象到物理单元的映射可以在只读部分不单射，实际交换性质及候选执行运输仍须成立。这是实现缺口，不应重命名为新算法贡献。

## 检查表达式必须匹配语言语义

Polly 的 `IslExprBuilder::createOpICmp` 把指针操作数转换为指针宽度的整数；对两个 address-of 操作数使用无符号比较。[Polly 源码](https://github.com/llvm/llvm-project/blob/main/polly/lib/CodeGen/IslExprBuilder.cpp) LLVM 的 `ptrtoint` 有自己的表示语义，而且非整数指针可能携带额外状态。[LLVM Language Reference](https://www.llvm.org/docs/LangRef.html#ptrtoint-to-instruction)

在本仓库锁定的 CompCert 中，`Val.cmp_different_blocks` 只为 `Ceq`／`Cne` 给出结果；`cmpu_bool`／`cmplu_bool` 的不同 block 分支还检查实际指针有效性。不同 block 的大小比较不能直接用作保证安全求值的 Clight guard。证据是锁定源码 [Values.v](../vendor/CompCert/common/Values.v)，不是关于 LLVM 错误的结论。

这是对来源和实际语义的推论：同一个数学分离条件，可以需要不同语言实例的编码方式。核心应消费“检查执行安全、接受推出前提”的证书，而不预设区间指针比较或机器地址表示。

## 当前实现的选择

[一般仿射扫描](memory-affine-alias-scans.md)只对源实际访问过的有效、对齐单元查询地址，用相等／不等比较建立 NonAlias，并使用语言提供的状态关系接入完整程序宿主。[单层端点策略](memory-affine-endpoint-scans.md)针对相同步长或任一侧为常量的访问，其他访问保持已有双层扫描。297 个适配模块、七个 lowering 模块及两个核心模块的全量审计通过；新例子通过 1687 次完整 CompCert 汇编调用与 964 次独立分支／比较计数诊断。完整编译器没有增加全局公理，数学充分性和算法选择没有全局公理。

单层策略不会把区间重叠直接当作 alias。例如 `p[2*i]` 与同一 block 内的 `q[2*i+1]` 可能覆盖交错而分离的单元。是否值得保留这种精度、如何减少读写对数量及如何扩展到多轴，仍需实际成本与覆盖率记录。通用接口的价值在于这些编码策略可以更换，局部候选所消费的性质及完整程序宿主不必随之重写。
