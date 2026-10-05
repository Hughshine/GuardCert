# 源前缀安全的内存循环上界提升

本例组合动态 indexed 写足迹与内存中的循环上界。它处理 [Optimistic Loop Optimization](optimistic-loop-acceptance.md) 所需的参数稳定性检查中的一个关键边界：检查安全不能先假定待检查的参数稳定。

## 实际源、候选与检查

```c
/* source; i starts at zero */
for (; i < (int)*bound; ++i)
  out[i] = (unsigned int)i + 1U;

/* candidate */
private_upper = (int)*bound;
for (; i < private_upper; ++i)
  out[i] = (unsigned int)i + 1U;
```

两者逐轮使用相同的 store 地址和值，候选只缓存上界。源每次循环头都重新读取上界，因此 alias 可以使源提前退出。guard 首先检查 `i==0` 与 `0<(int)*bound<=cap`，再按源顺序逐点检查活动的 `out+k` 不等于 `bound`。默认 cap 是 16；任意不超过 signed32 最大值的静态 cap 均可实例化已证明的规则。超出 cap、空域或重叠均回退。

这个只读 tree 不执行源 store，不写临时变量，也不查询证明中的源执行。快照赋值仅存在于条件成立后的候选。上界指针只需可读；空域允许 out 为 null。由于源循环头本身读取上界，空域不允许用 null bound 作为定义良好的源输入。

## 为什么不能预先取得整个 footprint

```c
unsigned int small[3] = {7, 7, 8};
out = small;
bound = small + 2;
```

入口上界是 8，但源只执行 3 次。第三次 store 将 `small[2]` 改为 3，下一次头部测试退出；完整源执行定义良好。入口并不具有写入 `small[3]` 到 `small[7]` 的能力。

guard 依次比较 `small+0`、`small+1`、`small+2`，第三次发现 alias 后立即回退。后面的比较处于未到达的树分支，安全性证明不要求它们有定义。若先假定上界稳定来证明所有 8 个地址有效，便会形成循环论证。省略 guard 的缓存版本会尝试越界；回归只用独立模型验证这一反例，不执行那个未定义的 C 程序。

## 使用者交付的局部证据

完整源 AST 证书固定普通 unsigned32 word 指针、上界的 signed32 cast、实际 `out+i` store、严格 `<` 头部和 `i++`。使用者还提供标识不相交及候选私有 slot 的 freshness。修改 bound 指针、volatile 上界及不同下标不会通过核对。

`indexed_bound_domain_from_source` 从实际源头部取得 iterator、上界指针和读取值，并提供一个仅用于证明的源完成 witness。这个 witness 不要求上界稳定，不会被提取到运行时。源进展使用 signed32 最大值减去当前 iterator 的排名函数；所有实际为真的头部都保证自增不会越过最大值，排名与上界是否变化无关。

`indexed_bound_source_step` 从一个实际为真的源头部与剩余源执行解出下一次真实 store、自增及源 tail。`indexed_bound_alias_scan_run` 随检查前缀推进该 ghost 执行：

1. 当前源 load 给出相同的上界，故可判断当前点是否活动。
2. 真实源 store 给出当前地址的写权限；此前 store 保持权限，将其运输回只读检查使用的入口 memory。
3. 此地址和 bound 均有效，因此实际 Clight 指针相等比较有定义。
4. 若 alias，检查立即拒绝。若 non-alias，Mint32 对齐／字节分离引理保持 bound 的 load 值，然后才能使用剩余源执行证明下一点安全。

接受后的覆盖证明另由 `indexed_bound_alias_scan_sound` 给出。检查安全和接受含义是两份证据，前者没有使用完整已接受 footprint 的稳定性结论。`positive_readonly_tree_primitives` 将具有完成路径证书的含 load 检查树接入前提公式合成；拒绝仍为 unknown，不自动证明前提的否定。

## 从活动迭代到局部等价

`strict_active_condition_transport` 是可复用的语言侧设施。规则作者提交两个不变式：循环头的 `0<=i<=N` 与自增前的 `0<=i<N`。body 证明显式接收实际源头部为真这个事实；只有在它为真时，才消费当前迭代的 non-alias 前提。

`indexed_bound_loop_cached` 用接受后的活动地址分离证明每次实际 store 保持上界，然后替换实际循环条件。自增把较强的活动不变式送回头部不变式。源和候选保持同一 memory、公开 iterator、所有原 temps、trace 和 outcome；仅新鲜的私有上界 temp 可以不同。

`indexed_bound_forward` 提供实际 Clight 局部执行运输。只读 projected 规则库以源完成性和候选确定性补足观察下的局部等价；既有 freshness／continuation 宿主将其嵌回完整程序。完整端点是：

```text
compile_indexed_bounds p = OK target
  -> backward_simulation (Csem.semantics p) (Asm.semantics target)
```

统一使用者 pass 也接入该规则。遍历与规则选择属于这个使用者；框架提供 guard／候选／原源回退和实际局部到全局证明连接。

## 验证与边界

复现入口为 `make interface-indexed-bound-native`；统一 pass 的相同源程序使用 `python3 scripts/native_interface_indexed_bound.py --common`。验证包含逐单元／公开出口与 GCC 及独立逐头部 load 模型的比较，生成 Clight 中的 16 个活动地址比较、17 个提前成功候选，以及三种不支持的源模板拒绝。

139 个编译接口端点的假设审计通过，没有新增公理；十二种编译器配置重建并回归通过。新独立入口和统一 pass 对本程序各通过 1079 次调用／2154 行输出：1050 个同对象网格输入、20 个不同对象输入、一个 const bound、四个 null out 空域、两个三元素数组上界变化输入，以及 goto／有限外围循环。528 个网格输入满足 guard，其余包括 alias、超 cap 与空路径回退。无限外围函数也确认生成 guard，未执行。

上界 8 的三元素数组实际结果是 `exit 3` 与 `small 1 2 3`；上界 INT_MAX 的相同数组也保持该合法源结果，并在 cap 测试处回退。生成的四个函数均有顺序排列的 16 个活动地址比较、17 个仅在成功叶子内执行的私有快照和缓存循环头；不支持的三个源模板未改写。报告位于 `build/interface-indexed-bound-native/report.json` 与 `build/interface-common-indexed-bound-native/report.json`，绑定源码、Clight、汇编、实际提取编译器和当前证明报告。

本例缓存单个上界，body 写入连续 indexed word。检查成本仍为 O(cap)，直接 tree lowering 仍复制 17 个候选；没有性能测量。一般无界／仿射区间检查、多个相互依赖的 memory 参数、内存上界与二维调度的组合、潜在发散的 `!=` 源循环及旧 affine／tiling 路径迁移仍是后续工作。
