# 动态 indexed footprint 下的参数 load 提升

本例把 alias 条件从两个固定单元扩展到一个实际循环的活动写足迹。它使用新只读接口，属于 [Optimistic Loop Optimization 验收账本](optimistic-loop-acceptance.md) 中稳定参数与活动访问分离的一个有界实例。

## 实际变换与条件

```c
/* source */
for (; i < n; ++i)
  out[i] = *parameter + (unsigned int)i + 1U;

/* candidate */
private_snapshot = *parameter;
for (; i < n; ++i)
  out[i] = private_snapshot + (unsigned int)i + 1U;
```

guard 要求 `i==0`、`0<n<=cap`，并逐个检查每个活动的实际 `out+k` 都不等于 `parameter`。`cap` 是使用者 pass 的静态代码生成上限，当前默认 16；一般规则及其正确性定理对任意不超过 signed32 最大值的 cap 成立。`n>cap`、空路径和重叠路径回退到源。

这个检查允许同一数组中位于活动写前缀外的参数单元，也允许不同对象。例如 `n=4, out=buffer, parameter=buffer+7` 可接受；`parameter=buffer+1` 必须拒绝。后者被第二次 store 修改，之后的源 load 就会读到新值，无 guard 快照会产生不同结果。

检查语法是一棵只读决策树：先判断计数，再按 `k<n` 激活对应的地址相等测试。它不读取数组内容，不执行原片段，也不写 guard 私有变量。参数快照发生在条件成立后的候选前缀。生成器直接使用 Clight 的实际指针相等操作，没有引入指针排序或整数地址转换。

## 使用者需要证明什么

完整 AST 检查把源绑定到普通 unsigned32 load／store、实际 `out+i`、严格循环头及 `i++`。不同下标、修改参数指针的 body 和 volatile load 不符合证书；提议器不能绕过这个核对。使用者还提交 counter／bound／pointer 不相交约束及新私有 slot 的 freshness。

`indexed_load_domain_from_source` 从实际源循环取得检查的读取域。计数器和 bound 来自源循环头；当 `i=0,n>0` 时，第一轮实际地址求值给出 out 指针，实际 load 给出参数指针及入口读取值。`indexed_iterations_writable` 则逐轮消费实际 source store，将每个活动 `out[k]` 的写权限运输回入口；store 保持权限，故不需要预先假定内存参数稳定。

因此，每个被执行的 pointer comparison 两端均是有效地址。空路径在读取指针前停止。参数仅需可读；它的权限不用加强为可写。地址按实际 `Ptrofs.add`、`Ptrofs.mul` 和 signed index 转换解释。此变换保留所有 store 的地址与次序，无需把地址算术先改成整数模型再缓存 load。

`indexed_alias_scan_run` 给出检查树的实际 Clight 执行；`indexed_alias_scan_sound` 证明扫描接受后覆盖全部活动点；`indexed_guard_condition` 通过 Boolean 条件合成器提供通用 `readonly_condition`。超出 cap 时不会用一个不完整扫描证书接受。这是有界活动单元分离条件，没有声称已实现一般区间 min／max 检查或最弱条件。

## 局部稳定性、出口与完整程序

`indexed_load_body_preserves_parameter` 消费实际 body 的 store 和已接受的地址分离，复用 Mint32 的对齐／字节不重叠证明，保持参数的实际 `Mem.loadv` 值。

`indexed_iterations_cached` 沿实际迭代序列建立前缀不变式，再用表达式／temps 运输证明每轮缓存 RHS 与源 RHS 相同。数据 unsigned 回绕保持；条件不要求数据加法无溢出。候选和源逐轮得到相同 memory，只在新鲜私有 snapshot temp 上允许不同。

`indexed_load_forward` 连接完整计数循环，保留所有原 temps、完整 memory、trace 和 outcome。只读投影规则库补足源完成性、候选确定性及观察运输，得到局部条件等价。全局宿主保护所有原程序 temps，并负责私有声明、源入口和 continuation 运输。

完整端点是 `compile_indexed_loads_correct`：

```text
compile_indexed_loads p = OK target
  -> backward_simulation (Csem.semantics p) (Asm.semantics target)
```

统一使用者 pass 也接入这条规则，与固定单元 load 提升、参数 stride、内存循环上界及其他 exact rewrite 共用完整编译端点。

## 检查成本和验证状态

最多执行 cap 次指针相等测试和相应的活动性测试。决策树的提前成功叶子各自编码候选，因此当前生成方式会复制候选代码；默认 cap=16 时有 17 个候选叶子。这是保持 guard 只读的原型选择，尚未实现共享候选的控制流 lowering，也没有性能测量。

证明模块和 119 个编译接口端点的假设审计已通过，没有新增公理。复现入口为 `make interface-indexed-load-native`；统一 pass 的同程序验证入口为 `python3 scripts/native_interface_indexed_load.py --common`。两个实际提取的入口都通过 1095 次调用／2188 行输出，全部单元和公开 iterator 出口与 GCC 和逐次 load 的独立模型一致。

1050 次同对象网格调用中，有 528 个输入满足 guard、272 个 cap 内活动重叠输入回退、200 个超 cap 输入回退，其余为空路径；另有不同对象和 const 参数各 20 次、null 空路径两次、数据回绕一次以及 goto／外围循环。四个函数中的实际 guard、16 个有活动性测试的地址相等比较及 17 个候选出口均已确认；错误下标、修改参数指针和 volatile 模板未改写。无限外围循环只编译，不执行。报告在 `build/interface-indexed-load-native/report.json` 和 `build/interface-common-indexed-native/report.json`，绑定当前证明报告、源码、Clight、汇编及实际编译器。

本例仅提升单个标量读取，写 footprint 是从零开始的连续 indexed word 序列。一般仿射写集、多参数稳定性、廉价无界区间检查，以及该足迹证明与二维调度的组合仍待接入。
